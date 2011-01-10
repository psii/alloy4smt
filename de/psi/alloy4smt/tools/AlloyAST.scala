package de.psi.alloy4smt.tools

import scala.collection.JavaConversions._
import edu.mit.csail.sdg._
import alloy4compiler._
import alloy4._
import java.io.File
import java.lang.String

/**
 * Created by IntelliJ IDEA.
 * User: psi
 * Date: 03.01.11
 * Time: 07:32
 * To change this template use File | Settings | File Templates.
 */

class DebugReporter extends A4Reporter {
  override def bound(msg: String) = {
    println("bound: " + msg)
    super.bound(msg)
  }

  override def scope(msg: String) = {
    println("scope: " + msg)
    super.scope(msg)
  }

  override def warning(msg: ErrorWarning) = {
    println("warning: " + msg)
    super.warning(msg)
  }

  override def typecheck(msg: String) = {
    println("typecheck: " + msg)
    super.typecheck(msg)
  }

  override def parse(msg: String) = {
    println("parse: " + msg)
    super.parse(msg)
  }

  override def debug(msg: String) = {
    println("debug: " + msg)
    super.debug(msg)
  }
}

object AlloyAST {

  val intrefmod = """
  module util/intref

  abstract sig IntRef { v: Int, aqclass: IntRef }
  fact {
    all disj i, j: IntRef | (i.v=j.v) => (i.aqclass=j.aqclass)
    all i: IntRef | i.v=i.aqclass.v
  }

  one sig SomethingElse extends IntRef {}
  fact {
    no i: IntRef - SomethingElse | i.aqclass = SomethingElse.aqclass
  }
  """

  val doc = """
  open util/intref

  abstract sig Field { val: Int, f: univ ->one Int }
  one sig A extends Field {}
  one sig B extends Field {}
  one sig C extends Field {}

  sig X { lala: Field ->one IntRef, mm: univ->univ->X->Int }

  fact {
    int(A.val) fun/mul int(A.val) + int(B.val) fun/mul int(B.val) = int(C.val) fun/mul int(C.val)
    int(A.val) >= 3 and int(A.val) <= 8
    int(B.val) >= 3 and int(B.val) <= 8
    int(C.val) >= 3 and int(C.val) <= 8

    all m, n: X {
      all disj o, p: Field | m.lala[o] != n.lala[p]
    }
  }

  pred show {}
  run show for exactly 3 X, 5 int
  """

  def world = {
    val fm = new java.util.HashMap[String, String]
    fm.put("/tmp/x", doc)
    fm.put("/tmp/util/intref.als", intrefmod)
    parser.CompUtil.parseEverything_fromFile(null, fm, "/tmp/x", 2)
  }

  def etype(expr: ast.Expr): ast.Type =
    classOf[ast.Expr].getDeclaredMethod("type").invoke(expr).asInstanceOf[ast.Type]

  def options = {
    val opt = new translator.A4Options
    opt.tempDirectory = "/tmp"
    opt.solverDirectory = "/tmp"
    opt.solver = translator.A4Options.SatSolver.KK
    opt.skolemDepth = 4
    opt
  }

  def showBrowsableTree(b: ast.Browsable,  d: Int=0): String = {
    val desc = "*" * d + " " + b.getDescription
    val subn = if (d < 10) { b.getSubnodes.map(sn => showBrowsableTree(sn, d+1)).foldLeft("")(_ + _) } else { "" }
    desc + "\n" + subn
  }

  def browsableToHtml(b: ast.Browsable): String = {
    val html =
    <html>
      <head><title>Alloy4 Tree</title></head>
      <body>
        {scala.xml.XML.loadString("<pre>"+showBrowsableTree(b)+"</pre>")}
      </body>
    </html>
    val out = File.createTempFile("alloy", ".html")
    scala.xml.XML.save(out.getPath, html)
    out.getPath
  }

  def rundoc = {
    val m = world
    val opts = new translator.A4Options
    opts.tempDirectory = "/tmp"
    opts.solverDirectory = "/tmp"
    opts.solver = translator.A4Options.SatSolver.SAT4J
    opts.skolemDepth = 4
    val rep = new DebugReporter
    val sol = translator.TranslateAlloyToKodkod.execute_command(rep, m.getAllReachableSigs, m.getAllCommands.get(0), opts)
    sol
  }

}


class IntRefPreparer {

}

object IntRefPreparer {

  def fromCompModule(m: parser.CompModule) = {

  }
}