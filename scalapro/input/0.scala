package scala.tools.nsc
package typechecker

import java.lang.Math.min
import symtab.Flags._
import scala.tools.nsc.util._
import scala.reflect.runtime.ReflectionUtils
import scala.collection.mutable.ListBuffer
import scala.reflect.ClassTag
import scala.reflect.internal.util.Statistics
import scala.reflect.macros.util._
import scala.util.control.ControlThrowable
import scala.reflect.macros.runtime.{AbortMacroException, MacroRuntimes}
import scala.reflect.runtime.{universe => ru}
import scala.reflect.macros.compiler.DefaultMacroCompiler
import scala.tools.reflect.FastTrack
import scala.runtime.ScalaRunTime
import Fingerprint._

trait Macros extends MacroRuntimes with Traces with Helpers {
  self: Analyzer =>

  import global._
  import definitions._
  import treeInfo.{isRepeatedParamType => _, _}
  import MacrosStats._

  lazy val fastTrack = new FastTrack[self.type](self)

  def globalSettings = global.settings

  protected def findMacroClassLoader(): ClassLoader = {
    val classpath = global.classPath.asURLs
    macroLogVerbose("macro classloader: initializing from -cp: %s".format(classpath))
    ScalaClassLoader.fromURLs(classpath, self.getClass.getClassLoader)
  }

  case class MacroImplBinding(
      val isBundle: Boolean,
      val isBlackbox: Boolean,
      className: String,
      methName: String,
      signature: List[List[Fingerprint]],
      targs: List[Tree]) {
    def is_??? = {
      val Predef_??? = currentRun.runDefinitions.Predef_???
      className == Predef_???.owner.javaClassName && methName == Predef_???.name.encoded
    }
    def isWhitebox = !isBlackbox
  }

  def macroEngine = "v7.0 (implemented in Scala 2.11.0-M8)"
  object MacroImplBinding {
    def pickleAtom(obj: Any): Tree =
      obj match {
        case list: List[_] => Apply(Ident(ListModule), list map pickleAtom)
        case s: String => Literal(Constant(s))
        case d: Double => Literal(Constant(d))
        case b: Boolean => Literal(Constant(b))
        case f: Fingerprint => Literal(Constant(f.value))
      }

    def unpickleAtom(tree: Tree): Any =
      tree match {
        case Apply(list @ Ident(_), args) if list.symbol == ListModule => args map unpickleAtom
        case Literal(Constant(s: String)) => s
        case Literal(Constant(d: Double)) => d
        case Literal(Constant(b: Boolean)) => b
        case Literal(Constant(i: Int)) => Fingerprint(i)
      }

    def pickle(macroImplRef: Tree): Tree = {
      val runDefinitions = currentRun.runDefinitions
      import runDefinitions._
      val MacroImplReference(isBundle, isBlackbox, owner, macroImpl, targs) = macroImplRef

      // todo. refactor when fixing SI-5498
      def className: String = {
        def loop(sym: Symbol): String = sym match {
          case sym if sym.isTopLevel =>
            val suffix = if (sym.isModuleClass) "$" else ""
            sym.fullName + suffix
          case sym =>
            val separator = if (sym.owner.isModuleClass) "" else "$"
            loop(sym.owner) + separator + sym.javaSimpleName.toString
        }

        loop(owner)
      }

      def signature: List[List[Fingerprint]] = {
        def fingerprint(tpe: Type): Fingerprint = tpe.dealiasWiden match {
          case TypeRef(_, RepeatedParamClass, underlying :: Nil) => fingerprint(underlying)
          case ExprClassOf(_) => LiftedTyped
          case TreeType() => LiftedUntyped
          case _ => Other
        }

        val transformed = transformTypeTagEvidenceParams(macroImplRef, (param, tparam) => tparam)
        mmap(transformed)(p => if (p.isTerm) fingerprint(p.info) else Tagged(p.paramPos))
      }

      val payload = List[(String, Any)](
        "macroEngine" -> macroEngine,
        "isBundle"    -> isBundle,
        "isBlackbox"  -> isBlackbox,
        "className"   -> className,
        "methodName"  -> macroImpl.name.toString,
        "signature"   -> signature
      )

      val nucleus = Ident(newTermName("macro"))
      val wrapped = Apply(nucleus, payload map { case (k, v) => Assign(pickleAtom(k), pickleAtom(v)) })
      val pickle = gen.mkTypeApply(wrapped, targs map (_.duplicate))

      new Transformer {
        override def transform(tree: Tree) = {
          tree match {
            case Literal(const @ Constant(x)) if tree.tpe == null => tree setType ConstantType(const)
            case _ if tree.tpe == null => tree setType NoType
            case _ => ;
          }
          super.transform(tree)
        }
      }.transform(pickle)
    }

    def unpickle(pickle: Tree): MacroImplBinding = {
      val (wrapped, targs) =
        pickle match {
          case TypeApply(wrapped, targs) => (wrapped, targs)
          case wrapped => (wrapped, Nil)
        }
      val Apply(_, pickledPayload) = wrapped
      val payload = pickledPayload.map{ case Assign(k, v) => (unpickleAtom(k), unpickleAtom(v)) }.toMap

      import typer.TyperErrorGen._
      def fail(msg: String) = MacroCantExpandIncompatibleMacrosError(msg)
      def unpickle[T](field: String, clazz: Class[T]): T = {
        def failField(msg: String) = fail(s"$field $msg")
        if (!payload.contains(field)) failField("is supposed to be there")
        val raw: Any = payload(field)
        if (raw == null) failField(s"is not supposed to be null")
        val expected = ScalaRunTime.box(clazz)
        val actual = raw.getClass
        if (!expected.isAssignableFrom(actual)) failField(s"has wrong type: expected $expected, actual $actual")
        raw.asInstanceOf[T]
      }

      if (!payload.contains("macroEngine")) MacroCantExpand210xMacrosError("macroEngine field not found")
      val macroEngine = unpickle("macroEngine", classOf[String])
      if (self.macroEngine != macroEngine) MacroCantExpandIncompatibleMacrosError(s"expected = ${self.macroEngine}, actual = $macroEngine")

      val isBundle = unpickle("isBundle", classOf[Boolean])
      val isBlackbox = unpickle("isBlackbox", classOf[Boolean])
      val className = unpickle("className", classOf[String])
      val methodName = unpickle("methodName", classOf[String])
      val signature = unpickle("signature", classOf[List[List[Fingerprint]]])
      MacroImplBinding(isBundle, isBlackbox, className, methodName, signature, targs)
    }
  }

  def bindMacroImpl(macroDef: Symbol, macroImplRef: Tree): Unit = {
    val pickle = MacroImplBinding.pickle(macroImplRef)
    macroDef withAnnotation AnnotationInfo(MacroImplAnnotation.tpe, List(pickle), Nil)
  }

  def loadMacroImplBinding(macroDef: Symbol): Option[MacroImplBinding] =
    macroDef.getAnnotation(MacroImplAnnotation) collect {
      case AnnotationInfo(_, List(pickle), _) => MacroImplBinding.unpickle(pickle)
    }

  def isBlackbox(expandee: Tree): Boolean = isBlackbox(dissectApplied(expandee).core.symbol)
  def isBlackbox(macroDef: Symbol): Boolean = {
    val fastTrackBoxity = fastTrack.get(macroDef).map(_.isBlackbox)
    val bindingBoxity = loadMacroImplBinding(macroDef).map(_.isBlackbox)
    fastTrackBoxity orElse bindingBoxity getOrElse false
  }

  def computeMacroDefTypeFromMacroImplRef(macroDdef: DefDef, macroImplRef: Tree): Type = {
    macroImplRef match {
      case MacroImplReference(_, _, _, macroImpl, targs) =>
        var runtimeType = decreaseMetalevel(macroImpl.info.finalResultType)

        runtimeType = runtimeType.substituteTypes(macroImpl.typeParams, targs map (_.tpe))

        def unsigma(tpe: Type): Type =
          transformTypeTagEvidenceParams(macroImplRef, (param, tparam) => NoSymbol) match {
            case (implCtxParam :: Nil) :: implParamss =>
              val implToDef = flatMap2(implParamss, macroDdef.vparamss)(map2(_, _)((_, _))).toMap
              object UnsigmaTypeMap extends TypeMap {
                def apply(tp: Type): Type = tp match {
                  case TypeRef(pre, sym, args) =>
                    val pre1 = pre match {
                      case SingleType(SingleType(SingleType(NoPrefix, c), prefix), value) if c == implCtxParam && prefix == MacroContextPrefix && value == ExprValue =>
                        ThisType(macroDdef.symbol.owner)
                      case SingleType(SingleType(NoPrefix, implParam), value) if value == ExprValue =>
                        implToDef get implParam map (defParam => SingleType(NoPrefix, defParam.symbol)) getOrElse pre
                      case _ =>
                        pre
                    }
                    val args1 = args map mapOver
                    TypeRef(pre1, sym, args1)
                  case _ =>
                    mapOver(tp)
                }
              }

              UnsigmaTypeMap(tpe)
            case _ =>
              tpe
          }

        unsigma(runtimeType)
      case _ =>
        ErrorType
    }
  }

  def typedMacroBody(typer: Typer, macroDdef: DefDef): Tree = pluginsTypedMacroBody(typer, macroDdef)

  def standardTypedMacroBody(typer: Typer, macroDdef: DefDef): Tree = {
    val macroDef = macroDdef.symbol
    assert(macroDef.isMacro, macroDdef)

    macroLogVerbose("typechecking macro def %s at %s".format(macroDef, macroDdef.pos))
    if (fastTrack contains macroDef) {
      macroLogVerbose("typecheck terminated unexpectedly: macro is fast track")
      assert(!macroDdef.tpt.isEmpty, "fast track macros must provide result type")
      EmptyTree
    } else {
      def fail() = { if (macroDef != null) macroDef setFlag IS_ERROR; macroDdef setType ErrorType; EmptyTree }
      def success(macroImplRef: Tree) = { bindMacroImpl(macroDef, macroImplRef); macroImplRef }

      if (!typer.checkFeature(macroDdef.pos, currentRun.runDefinitions.MacrosFeature, immediate = true)) {
        macroLogVerbose("typecheck terminated unexpectedly: language.experimental.macros feature is not enabled")
        fail()
      } else {
        val macroDdef1: macroDdef.type = macroDdef
        val typer1: typer.type = typer
        val macroCompiler = new {
          val global: self.global.type = self.global
          val typer: self.global.analyzer.Typer = typer1.asInstanceOf[self.global.analyzer.Typer]
          val macroDdef: self.global.DefDef = macroDdef1
        } with DefaultMacroCompiler
        val macroImplRef = macroCompiler.resolveMacroImpl
        if (macroImplRef.isEmpty) fail() else success(macroImplRef)
      }
    }
  }

  def macroContext(typer: Typer, prefixTree: Tree, expandeeTree: Tree): MacroContext = {
    new {
      val universe: self.global.type = self.global
      val callsiteTyper: universe.analyzer.Typer = typer.asInstanceOf[global.analyzer.Typer]
      val expandee = universe.analyzer.macroExpanderAttachment(expandeeTree).original orElse duplicateAndKeepPositions(expandeeTree)
    } with UnaffiliatedMacroContext {
      val prefix = Expr[Nothing](prefixTree)(TypeTag.Nothing)
      override def toString = "MacroContext(%s@%s +%d)".format(expandee.symbol.name, expandee.pos, enclosingMacros.length - 1 /* exclude myself */)
    }
  }

  case class MacroArgs(c: MacroContext, others: List[Any])
  def macroArgs(typer: Typer, expandee: Tree): MacroArgs = pluginsMacroArgs(typer, expandee)

  def standardMacroArgs(typer: Typer, expandee: Tree): MacroArgs = {
    val macroDef = expandee.symbol
    val paramss = macroDef.paramss
    val treeInfo.Applied(core, targs, argss) = expandee
    val prefix = core match { case Select(qual, _) => qual; case _ => EmptyTree }
    val context = expandee.attachments.get[MacroRuntimeAttachment].flatMap(_.macroContext).getOrElse(macroContext(typer, prefix, expandee))

    macroLogVerbose(sm"""
      |context: $context
      |prefix: $prefix
      |targs: $targs
      |argss: $argss
      |paramss: $paramss
    """.trim)

    import typer.TyperErrorGen._
    val isNullaryArgsEmptyParams = argss.isEmpty && paramss == ListOfNil
    if (paramss.length < argss.length) MacroTooManyArgumentListsError(expandee)
    if (paramss.length > argss.length && !isNullaryArgsEmptyParams) MacroTooFewArgumentListsError(expandee)

    val macroImplArgs: List[Any] =
      if (fastTrack contains macroDef) {
        if (fastTrack(macroDef) validate expandee) argss.flatten
        else MacroTooFewArgumentListsError(expandee)
      }
      else {
        def calculateMacroArgs(binding: MacroImplBinding) = {
          val signature = if (binding.isBundle) binding.signature else binding.signature.tail
          macroLogVerbose(s"binding: $binding")

          val trees = map3(argss, paramss, signature)((args, defParams, implParams) => {
            val isVarargs = isVarArgsList(defParams)
            if (isVarargs) {
              if (defParams.length > args.length + 1) MacroTooFewArgumentsError(expandee)
            } else {
              if (defParams.length < args.length) MacroTooManyArgumentsError(expandee)
              if (defParams.length > args.length) MacroTooFewArgumentsError(expandee)
            }

            val wrappedArgs = mapWithIndex(args)((arg, j) => {
              val fingerprint = implParams(min(j, implParams.length - 1))
              fingerprint match {
                case LiftedTyped => context.Expr[Nothing](arg.duplicate)(TypeTag.Nothing) // TODO: SI-5752
                case LiftedUntyped => arg.duplicate
                case _ => abort(s"unexpected fingerprint $fingerprint in $binding with paramss being $paramss " +
                                s"corresponding to arg $arg in $argss")
              }
            })

            if (isVarargs) {
              val (normal, varargs) = wrappedArgs splitAt (defParams.length - 1)
              normal :+ varargs 
            } else wrappedArgs
          })
          macroLogVerbose(s"trees: $trees")

          val tags = signature.flatten collect { case f if f.isTag => f.paramPos } map (paramPos => {
            val targ = binding.targs(paramPos).tpe.typeSymbol
            val tpe = if (targ.isTypeParameterOrSkolem) {
              if (targ.owner == macroDef) {
                val argPos = macroDef.typeParams.indexWhere(_.name == targ.name)
                targs(argPos).tpe
              } else
                targ.tpe.asSeenFrom(
                  if (prefix == EmptyTree) macroDef.owner.tpe else prefix.tpe,
                  macroDef.owner)
            } else
              targ.tpe
            context.WeakTypeTag(tpe)
          })
          macroLogVerbose(s"tags: $tags")

          (trees :+ tags).flatten
        }

        val binding = loadMacroImplBinding(macroDef).get
        if (binding.is_???) Nil
        else calculateMacroArgs(binding)
      }
    macroLogVerbose(s"macroImplArgs: $macroImplArgs")
    MacroArgs(context, macroImplArgs)
  }

  var _openMacros = List[MacroContext]()
  def openMacros = _openMacros
  def pushMacroContext(c: MacroContext) = _openMacros ::= c
  def popMacroContext() = _openMacros = _openMacros.tail
  def enclosingMacroPosition = openMacros map (_.macroApplication.pos) find (_ ne NoPosition) getOrElse NoPosition

  abstract class MacroExpander(val typer: Typer, val expandee: Tree) {
    def onSuccess(expanded: Tree): Tree
    def onFallback(expanded: Tree): Tree
    def onSuppressed(expandee: Tree): Tree = expandee
    def onDelayed(expanded: Tree): Tree = expanded
    def onSkipped(expanded: Tree): Tree = expanded
    def onFailure(expanded: Tree): Tree = { typer.infer.setError(expandee); expandee }

    def apply(desugared: Tree): Tree = {
      if (isMacroExpansionSuppressed(desugared)) onSuppressed(expandee)
      else expand(desugared)
    }

    protected def expand(desugared: Tree): Tree = {
      def showDetailed(tree: Tree) = showRaw(tree, printIds = true, printTypes = true)
      def summary() = s"expander = $this, expandee = ${showDetailed(expandee)}, desugared = ${if (expandee == desugared) () else showDetailed(desugared)}"
      if (macroDebugVerbose) println(s"macroExpand: ${summary()}")
      linkExpandeeAndDesugared(expandee, desugared)

      val start = if (Statistics.canEnable) Statistics.startTimer(macroExpandNanos) else null
      if (Statistics.canEnable) Statistics.incCounter(macroExpandCount)
      try {
        withInfoLevel(nodePrinters.InfoLevel.Quiet) { 
          if (expandee.symbol.isErroneous || (expandee exists (_.isErroneous))) {
            val reason = if (expandee.symbol.isErroneous) "not found or incompatible macro implementation" else "erroneous arguments"
            macroLogVerbose(s"cancelled macro expansion because of $reason: $expandee")
            onFailure(typer.infer.setError(expandee))
          } else try {
            val expanded = {
              val runtime = macroRuntime(expandee)
              if (runtime != null) macroExpandWithRuntime(typer, expandee, runtime)
              else macroExpandWithoutRuntime(typer, expandee)
            }
            expanded match {
              case Success(expanded) =>
                val expanded1 = try onSuccess(duplicateAndKeepPositions(expanded)) finally popMacroContext()
                if (!hasMacroExpansionAttachment(expanded1)) linkExpandeeAndExpanded(expandee, expanded1)
                if (settings.Ymacroexpand.value == settings.MacroExpand.Discard) expandee.setType(expanded1.tpe)
                else expanded1
              case Fallback(fallback) => onFallback(fallback)
              case Delayed(delayed) => onDelayed(delayed)
              case Skipped(skipped) => onSkipped(skipped)
              case Failure(failure) => onFailure(failure)
            }
          } catch {
            case typer.TyperErrorGen.MacroExpansionException => onFailure(expandee)
          }
        }
      } finally {
        if (Statistics.canEnable) Statistics.stopTimer(macroExpandNanos, start)
      }
    }
  }

  class DefMacroExpander(typer: Typer, expandee: Tree, mode: Mode, outerPt: Type)
  extends MacroExpander(typer, expandee) {
    lazy val innerPt = {
      val tp = if (isNullaryInvocation(expandee)) expandee.tpe.finalResultType else expandee.tpe
      if (isBlackbox(expandee)) tp
      else {
        val undetparams = tp collect { case tp if tp.typeSymbol.isTypeParameter => tp.typeSymbol }
        deriveTypeWithWildcards(undetparams)(tp)
      }
    }
    override def onSuccess(expanded0: Tree) = {
      linkExpandeeAndExpanded(expandee, expanded0)

      def typecheck(label: String, tree: Tree, pt: Type): Tree = {
        if (tree.isErrorTyped) tree
        else {
          if (macroDebugVerbose) println(s"$label (against pt = $pt): $tree")
          val result = typer.context.withImplicitsEnabled(typer.typed(tree, mode, pt))
          if (result.isErrorTyped && macroDebugVerbose) println(s"$label has failed: ${typer.context.reportBuffer.errors}")
          result
        }
      }

      if (isBlackbox(expandee)) {
        val expanded1 = atPos(enclosingMacroPosition.makeTransparent)(Typed(expanded0, TypeTree(innerPt)))
        typecheck("blackbox typecheck", expanded1, outerPt)
      } else {
        val expanded1 = typecheck("whitebox typecheck #0", expanded0, WildcardType)
        val expanded2 = typecheck("whitebox typecheck #1", expanded1, innerPt)
        typecheck("whitebox typecheck #2", expanded2, outerPt)
      }
    }
    override def onDelayed(delayed: Tree) = {
      val shouldInstantiate = typer.context.undetparams.nonEmpty && !mode.inPolyMode
      if (shouldInstantiate) {
        if (isBlackbox(expandee)) typer.instantiatePossiblyExpectingUnit(delayed, mode, outerPt)
        else {
          forced += delayed
          typer.infer.inferExprInstance(delayed, typer.context.extractUndetparams(), outerPt, keepNothings = false)
          macroExpand(typer, delayed, mode, outerPt)
        }
      } else delayed
    }
    override def onFallback(fallback: Tree) = typer.typed(fallback, mode, outerPt)
  }

  def macroExpand(typer: Typer, expandee: Tree, mode: Mode, pt: Type): Tree = pluginsMacroExpand(typer, expandee, mode, pt)

  def standardMacroExpand(typer: Typer, expandee: Tree, mode: Mode, pt: Type): Tree = {
    val expander = new DefMacroExpander(typer, expandee, mode, pt)
    expander(expandee)
  }

  sealed abstract class MacroStatus(val result: Tree)
  case class Success(expanded: Tree) extends MacroStatus(expanded)
  case class Fallback(fallback: Tree) extends MacroStatus(fallback) { currentRun.seenMacroExpansionsFallingBack = true }
  case class Delayed(delayed: Tree) extends MacroStatus(delayed)
  case class Skipped(skipped: Tree) extends MacroStatus(skipped)
  case class Failure(failure: Tree) extends MacroStatus(failure)
  def Delay(expanded: Tree) = Delayed(expanded)
  def Skip(expanded: Tree) = Skipped(expanded)

  def macroExpandWithRuntime(typer: Typer, expandee: Tree, runtime: MacroRuntime): MacroStatus = {
    val wasDelayed  = isDelayed(expandee)
    val undetparams = calculateUndetparams(expandee)
    val nowDelayed  = !typer.context.macrosEnabled || undetparams.nonEmpty

    (wasDelayed, nowDelayed) match {
      case (true, true) =>
        Delay(expandee)
      case (true, false) =>
        val expanded = macroExpandAll(typer, expandee)
        if (expanded exists (_.isErroneous)) Failure(expandee)
        else Skip(expanded)
      case (false, true) =>
        macroLogLite("macro expansion is delayed: %s".format(expandee))
        delayed += expandee -> undetparams
        expandee updateAttachment MacroRuntimeAttachment(delayed = true, typerContext = typer.context, macroContext = Some(macroArgs(typer, expandee).c))
        Delay(expandee)
      case (false, false) =>
        import typer.TyperErrorGen._
        macroLogLite("performing macro expansion %s at %s".format(expandee, expandee.pos))
        val args = macroArgs(typer, expandee)
        try {
          val numErrors    = reporter.ERROR.count
          def hasNewErrors = reporter.ERROR.count > numErrors
          val expanded = { pushMacroContext(args.c); runtime(args) }
          if (hasNewErrors) MacroGeneratedTypeError(expandee)
          def validateResultingTree(expanded: Tree) = {
            macroLogVerbose("original:")
            macroLogLite("" + expanded + "\n" + showRaw(expanded))
            val freeSyms = expanded.freeTerms ++ expanded.freeTypes
            freeSyms foreach (sym => MacroFreeSymbolError(expandee, sym))
            val expandedPos = enclosingMacroPosition.focus
            def fixPosition(pos: Position) =
              if (pos == NoPosition) expandedPos else pos.focus
            expanded.foreach(t => t.pos = fixPosition(t.pos))

            val result = atPos(enclosingMacroPosition.focus)(expanded)
            Success(result)
          }
          expanded match {
            case expanded: Expr[_] if expandee.symbol.isTermMacro => validateResultingTree(expanded.tree)
            case expanded: Tree if expandee.symbol.isTermMacro => validateResultingTree(expanded)
            case _ => MacroExpansionHasInvalidTypeError(expandee, expanded)
          }
        } catch {
          case ex: Throwable =>
            popMacroContext()
            val realex = ReflectionUtils.unwrapThrowable(ex)
            realex match {
              case ex: AbortMacroException => MacroGeneratedAbort(expandee, ex)
              case ex: ControlThrowable => throw ex
              case ex: TypeError => MacroGeneratedTypeError(expandee, ex)
              case _ => MacroGeneratedException(expandee, realex)
            }
        } finally {
          expandee.removeAttachment[MacroRuntimeAttachment]
        }
    }
  }

  def macroExpandWithoutRuntime(typer: Typer, expandee: Tree): MacroStatus = {
    import typer.TyperErrorGen._
    val fallbackSym = expandee.symbol.nextOverriddenSymbol orElse MacroImplementationNotFoundError(expandee)
    macroLogLite(s"falling back to: $fallbackSym")

    def mkFallbackTree(tree: Tree): Tree = {
      tree match {
        case Select(qual, name) => Select(qual, name) setPos tree.pos setSymbol fallbackSym
        case Apply(fn, args) => Apply(mkFallbackTree(fn), args) setPos tree.pos
        case TypeApply(fn, args) => TypeApply(mkFallbackTree(fn), args) setPos tree.pos
      }
    }
    Fallback(mkFallbackTree(expandee))
  }

  var hasPendingMacroExpansions = false
  private val forced = perRunCaches.newWeakSet[Tree]
  private val delayed = perRunCaches.newWeakMap[Tree, scala.collection.mutable.Set[Int]]()
  private def isDelayed(expandee: Tree) = delayed contains expandee
  private def calculateUndetparams(expandee: Tree): scala.collection.mutable.Set[Int] =
    if (forced(expandee)) scala.collection.mutable.Set[Int]()
    else delayed.getOrElse(expandee, {
      val calculated = scala.collection.mutable.Set[Symbol]()
      expandee foreach (sub => {
        def traverse(sym: Symbol) = if (sym != null && (undetparams contains sym.id)) calculated += sym
        if (sub.symbol != null) traverse(sub.symbol)
        if (sub.tpe != null) sub.tpe foreach (sub => traverse(sub.typeSymbol))
      })
      macroLogVerbose("calculateUndetparams: %s".format(calculated))
      calculated map (_.id)
    })
  private val undetparams = perRunCaches.newSet[Int]()
  def notifyUndetparamsAdded(newUndets: List[Symbol]): Unit = {
    undetparams ++= newUndets map (_.id)
    if (macroDebugVerbose) newUndets foreach (sym => println("undetParam added: %s".format(sym)))
  }
  def notifyUndetparamsInferred(undetNoMore: List[Symbol], inferreds: List[Type]): Unit = {
    undetparams --= undetNoMore map (_.id)
    if (macroDebugVerbose) (undetNoMore zip inferreds) foreach { case (sym, tpe) => println("undetParam inferred: %s as %s".format(sym, tpe))}
    if (!delayed.isEmpty)
      delayed.toList foreach {
        case (expandee, undetparams) if !undetparams.isEmpty =>
          undetparams --= undetNoMore map (_.id)
          if (undetparams.isEmpty) {
            hasPendingMacroExpansions = true
            macroLogVerbose(s"macro expansion is pending: $expandee")
          }
        case _ =>
      }
  }

  def macroExpandAll(typer: Typer, expandee: Tree): Tree =
    new Transformer {
      override def transform(tree: Tree) = super.transform(tree match {
        case tree if (delayed contains tree) && calculateUndetparams(tree).isEmpty && !tree.isErroneous =>
          val context = tree.attachments.get[MacroRuntimeAttachment].get.typerContext
          delayed -= tree
          context.implicitsEnabled = typer.context.implicitsEnabled
          context.enrichmentEnabled = typer.context.enrichmentEnabled
          context.macrosEnabled = typer.context.macrosEnabled
          macroExpand(newTyper(context), tree, EXPRmode, WildcardType)
        case _ =>
          tree
      })
    }.transform(expandee)
}

object MacrosStats {
  import scala.reflect.internal.TypesStats.typerNanos
  val macroExpandCount    = Statistics.newCounter ("#macro expansions", "typer")
  val macroExpandNanos    = Statistics.newSubTimer("time spent in macroExpand", typerNanos)
}

class Fingerprint private[Fingerprint](val value: Int) extends AnyVal {
  def paramPos = { assert(isTag, this); value }
  def isTag = value >= 0
  override def toString = this match {
    case Other => "Other"
    case LiftedTyped => "Expr"
    case LiftedUntyped => "Tree"
    case _ => s"Tag($value)"
  }
}

object Fingerprint {
  def apply(value: Int) = new Fingerprint(value)
  def Tagged(tparamPos: Int) = new Fingerprint(tparamPos)
  val Other = new Fingerprint(-1)
  val LiftedTyped = new Fingerprint(-2)
  val LiftedUntyped = new Fingerprint(-3)
}