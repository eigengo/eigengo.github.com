package scala

import scala.collection.{ mutable, immutable, generic, SortedSetLike, AbstractSet }
import java.lang.reflect.{ Modifier, Method => JMethod, Field => JField }
import scala.reflect.NameTransformer._
import scala.util.matching.Regex

@SerialVersionUID(8476000850333817230L)
abstract class Enumeration (initial: Int) extends Serializable {
  thisenum =>

  def this() = this(0)

  protected def readResolve(): AnyRef = thisenum.getClass.getField(MODULE_INSTANCE_NAME).get(null)

  override def toString =
    ((getClass.getName stripSuffix MODULE_SUFFIX_STRING split '.').last split
       Regex.quote(NAME_JOIN_STRING)).last

  private val vmap: mutable.Map[Int, Value] = new mutable.HashMap

  @transient private var vset: ValueSet = null
  @transient @volatile private var vsetDefined = false

  private val nmap: mutable.Map[Int, String] = new mutable.HashMap

  def values: ValueSet = {
    if (!vsetDefined) {
      vset = (ValueSet.newBuilder ++= vmap.values).result()
      vsetDefined = true
    }
    vset
  }

  protected var nextId: Int = initial

  protected var nextName: Iterator[String] = _

  private def nextNameOrNull =
    if (nextName != null && nextName.hasNext) nextName.next() else null

  private var topId = initial

  private var bottomId = if(initial < 0) initial else 0

  final def maxId = topId

  final def apply(x: Int): Value = vmap(x)

  final def withName(s: String): Value = values.find(_.toString == s).get

  protected final def Value: Value = Value(nextId)

  protected final def Value(i: Int): Value = Value(i, nextNameOrNull)

  protected final def Value(name: String): Value = Value(nextId, name)

  protected final def Value(i: Int, name: String): Value = new Val(i, name)

  private def populateNameMap() {
    val fields = getClass.getDeclaredFields
    def isValDef(m: JMethod) = fields exists (fd => fd.getName == m.getName && fd.getType == m.getReturnType)

    val methods = getClass.getMethods filter (m => m.getParameterTypes.isEmpty &&
                                                   classOf[Value].isAssignableFrom(m.getReturnType) &&
                                                   m.getDeclaringClass != classOf[Enumeration] &&
                                                   isValDef(m))
    methods foreach { m =>
      val name = m.getName
      val value = m.invoke(this).asInstanceOf[Value]
      if (value.outerEnum eq thisenum) {
        val id = Int.unbox(classOf[Val] getMethod "id" invoke value)
        nmap += ((id, name))
      }
    }
  }

  private def nameOf(i: Int): String = synchronized { nmap.getOrElse(i, { populateNameMap() ; nmap(i) }) }

  @SerialVersionUID(7091335633555234129L)
  abstract class Value extends Ordered[Value] with Serializable {
    def id: Int
    private[Enumeration] val outerEnum = thisenum

    override def compare(that: Value): Int =
      if (this.id < that.id) -1
      else if (this.id == that.id) 0
      else 1
    override def equals(other: Any) = other match {
      case that: Enumeration#Value  => (outerEnum eq that.outerEnum) && (id == that.id)
      case _                        => false
    }
    override def hashCode: Int = id.##

    def + (v: Value) = ValueSet(this, v)
  }

  @SerialVersionUID(0 - 3501153230598116017L)
  protected class Val(i: Int, name: String) extends Value with Serializable {
    def this(i: Int)       = this(i, nextNameOrNull)
    def this(name: String) = this(nextId, name)
    def this()             = this(nextId)

    assert(!vmap.isDefinedAt(i), "Duplicate id: " + i)
    vmap(i) = this
    vsetDefined = false
    nextId = i + 1
    if (nextId > topId) topId = nextId
    if (i < bottomId) bottomId = i
    def id = i
    override def toString() =
      if (name != null) name
      else try thisenum.nameOf(i)
      catch { case _: NoSuchElementException => "<Invalid enum: no field for #" + i + ">" }

    protected def readResolve(): AnyRef = {
      val enum = thisenum.readResolve().asInstanceOf[Enumeration]
      if (enum.vmap == null) this
      else enum.vmap(i)
    }
  }

  object ValueOrdering extends Ordering[Value] {
    def compare(x: Value, y: Value): Int = x compare y
  }

  class ValueSet private[ValueSet] (private[this] var nnIds: immutable.BitSet)
  extends AbstractSet[Value]
     with immutable.SortedSet[Value]
     with SortedSetLike[Value, ValueSet]
     with Serializable {

    implicit def ordering: Ordering[Value] = ValueOrdering
    def rangeImpl(from: Option[Value], until: Option[Value]): ValueSet =
      new ValueSet(nnIds.rangeImpl(from.map(_.id - bottomId), until.map(_.id - bottomId)))

    override def empty = ValueSet.empty
    def contains(v: Value) = nnIds contains (v.id - bottomId)
    def + (value: Value) = new ValueSet(nnIds + (value.id - bottomId))
    def - (value: Value) = new ValueSet(nnIds - (value.id - bottomId))
    def iterator = nnIds.iterator map (id => thisenum.apply(bottomId + id))
    override def keysIteratorFrom(start: Value) = nnIds keysIteratorFrom start.id  map (id => thisenum.apply(bottomId + id))
    override def stringPrefix = thisenum + ".ValueSet"
    def toBitMask: Array[Long] = nnIds.toBitMask
  }

  object ValueSet {
    import generic.CanBuildFrom

    val empty = new ValueSet(immutable.BitSet.empty)
    def apply(elems: Value*): ValueSet = (newBuilder ++= elems).result()
    def fromBitMask(elems: Array[Long]): ValueSet = new ValueSet(immutable.BitSet.fromBitMask(elems))
    def newBuilder: mutable.Builder[Value, ValueSet] = new mutable.Builder[Value, ValueSet] {
      private[this] val b = new mutable.BitSet
      def += (x: Value) = { b += (x.id - bottomId); this }
      def clear() = b.clear()
      def result() = new ValueSet(b.toImmutable)
    }
    implicit def canBuildFrom: CanBuildFrom[ValueSet, Value, ValueSet] =
      new CanBuildFrom[ValueSet, Value, ValueSet] {
        def apply(from: ValueSet) = newBuilder
        def apply() = newBuilder
      }
  }
}