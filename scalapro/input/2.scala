package scala.tools.nsc

import java.io.{ FileNotFoundException, PrintWriter, FileOutputStream }
import java.security.SecureRandom
import io.{ File, Path, Directory, Socket }
import scala.tools.util.CompileOutputCommon
import scala.reflect.internal.util.StringOps.splitWhere
import scala.sys.process._

trait HasCompileSocket {
  def compileSocket: CompileSocket

  val errorMarkers = Set("error:", "error found", "errors found", "bad option")
  def isErrorMessage(msg: String) = errorMarkers exists (msg contains _)

  def compileOnServer(sock: Socket, args: Seq[String]): Boolean = {
    var noErrors = true

    sock.applyReaderAndWriter { (in, out) =>
      out println (compileSocket getPassword sock.getPort())
      out println (args mkString "\u0000")

      def loop(): Boolean = in.readLine() match {
        case null => noErrors
        case line =>
          if (isErrorMessage(line))
            noErrors = false

          compileSocket.echo(line)
          loop()
      }
      try loop()
      finally sock.close()
    }
  }
}

class CompileSocket extends CompileOutputCommon {
  protected lazy val compileClient: StandardCompileClient = CompileClient
  def verbose = compileClient.verbose

  protected lazy val dirName = "scalac-compile-server-port"
  protected def cmdName = Properties.scalaCmd

  protected val vmCommand = Properties.scalaHome match {
    case ""       => cmdName
    case dirname  =>
      val trial = File(dirname) / "bin" / cmdName
      if (trial.canRead) trial.path
      else cmdName
  }

  protected val serverClass     = "scala.tools.nsc.CompileServer"
  protected def serverClassArgs = if (verbose) List("-v") else Nil  // debug

  val tmpDir = {
    val udir  = Option(Properties.userName) getOrElse "shared"
    val f     = (Path(Properties.tmpDir) / ("scala-devel" + udir)).createDirectory()

    if (f.isDirectory && f.canWrite) {
      info("[Temp directory: " + f + "]")
      f
    }
    else fatal("Could not find a directory for temporary files")
  }

  val portsDir = (tmpDir / dirName).createDirectory()

  private def serverCommand(vmArgs: Seq[String]): Seq[String] =
    Seq(vmCommand) ++ vmArgs ++ Seq(serverClass) ++ serverClassArgs filterNot (_ == "")

  private def startNewServer(vmArgs: String) = {
    val cmd = serverCommand((vmArgs split " ").toSeq)
    info("[Executing command: %s]" format cmd.mkString(" "))

    Process(cmd) match {
      case x: ProcessBuilder.AbstractBuilder => x.daemonized().run()
      case x                                 => x.run()
    }
  }

  def portFile(port: Int) = portsDir / File(port.toString)

  private def pollPort(): Int = portsDir.list.toList match {
    case Nil      => -1
    case x :: xs  => try x.name.toInt finally xs foreach (_.delete())
  }

  def getPort(vmArgs: String): Int = {
    val maxPolls = 300
    val sleepTime = 25L

    var attempts = 0
    var port = pollPort()

    if (port < 0) {
      info("No compile server running: starting one with args '" + vmArgs + "'")
      startNewServer(vmArgs)
    }
    while (port < 0 && attempts < maxPolls) {
      attempts += 1
      Thread.sleep(sleepTime)
      port = pollPort()
    }
    info("[Port number: " + port + "]")
    if (port < 0)
      fatal("Could not connect to compilation daemon after " + attempts + " attempts.")
    port
  }

  def setPort(port: Int) {
    val file    = portFile(port)
    val secret  = new SecureRandom().nextInt.toString

    try file writeAll secret catch {
      case e @ (_: FileNotFoundException | _: SecurityException) =>
        fatal("Cannot create file: %s".format(file.path))
    }
  }

  def deletePort(port: Int) = portFile(port).delete()

  def getOrCreateSocket(vmArgs: String, create: Boolean = true): Option[Socket] = {
    val maxMillis = 10L * 1000   // try for 10 seconds
    val retryDelay = 50L
    val maxAttempts = (maxMillis / retryDelay).toInt

    def getsock(attempts: Int): Option[Socket] = attempts match {
      case 0    => warn("Unable to establish connection to compilation daemon") ; None
      case num  =>
        val port = if (create) getPort(vmArgs) else pollPort()
        if (port < 0) return None

        Socket.localhost(port).either match {
          case Right(socket)  =>
            info("[Connected to compilation daemon at port %d]" format port)
            Some(socket)
          case Left(err)      =>
            info(err.toString)
            info("[Connecting to compilation daemon at port %d failed; re-trying...]" format port)

            if (attempts % 2 == 0)
              deletePort(port)      // 50% chance to stop trying on this port

            Thread sleep retryDelay // delay before retrying
            getsock(attempts - 1)
        }
    }
    getsock(maxAttempts)
  }

  def parseInt(x: String): Option[Int] =
    try   { Some(x.toInt) }
    catch { case _: NumberFormatException => None }

  def getSocket(serverAdr: String): Socket = (
    for ((name, portStr) <- splitWhere(serverAdr, _ == ':', doDropIndex = true) ; port <- parseInt(portStr)) yield
      getSocket(name, port)
  ) getOrElse fatal("Malformed server address: %s; exiting" format serverAdr)

  def getSocket(hostName: String, port: Int): Socket =
    Socket(hostName, port).opt getOrElse fatal("Unable to establish connection to server %s:%d; exiting".format(hostName, port))

  def getPassword(port: Int): String = {
    val ff  = portFile(port)
    val f   = ff.bufferedReader()

    def check = {
      Thread sleep 100
      ff.length
    }
    if ((Iterator continually check take 50 find (_ > 0)).isEmpty) {
      ff.delete()
      fatal("Unable to establish connection to server.")
    }
    val result = f.readLine()
    f.close()
    result
  }
}


object CompileSocket extends CompileSocket {
}