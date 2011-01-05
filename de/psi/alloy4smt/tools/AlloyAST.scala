package de.psi.alloy4smt.tools

import scala.collection.JavaConversions._
import edu.mit.csail.sdg._
import alloy4compiler._
import java.io.File

/**
 * Created by IntelliJ IDEA.
 * User: psi
 * Date: 03.01.11
 * Time: 07:32
 * To change this template use File | Settings | File Templates.
 */

object AlloyAST {

  val doc = """
  abstract sig Field { val: Int, f: univ->Int }
  one sig A extends Field {}
  one sig B extends Field {}
  one sig C extends Field {}

  fact {
    int(A.val) fun/mul int(A.val) + int(B.val) fun/mul int(B.val) = int(C.val) fun/mul int(C.val)
    int(A.val) >= 3 and int(A.val) <= 8
    int(B.val) >= 3 and int(B.val) <= 8
    int(C.val) >= 3 and int(C.val) <= 8
  }

  pred show {}
  run show for 5 int
  """

  def world = {
    val fm = new java.util.HashMap[String, String]
    fm.put("/tmp/x", doc)
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

}