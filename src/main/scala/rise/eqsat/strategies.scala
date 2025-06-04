package rise.eqsat

import PatternDSL._
import rise.core.{primitives => rcp, semantics => rcs}
import ElevateEqsat._
//import NamedRewriteDSL._

object strategies {
  def rwfrompatterns(name: String, lhs: Pattern, rhs: Pattern) : NamedStrategyS = {
    val rw = SRewrite(lhs, rhs)
    val s = new NamedStrategyS(
        name = name,
        strat = RewriteRule(rw),
    )
    s
  }

  // algorithmic 
   /*val mapFusion = NamedRewrite.init("map-fusion",
    app(app(map, "f"), app(app(map, "g"), "in"))
      -->
    app(app(map, lam("x", app("f", app("g", "x")))), "in")
    ) // need to adapt it */

    //val mapFusion = NamedStrategyS.init("rw-map-fusion", RewriteRule(SRewrite(Pattern.fromExpr(app(app(map, "f"), app(app(map, "g"), "in"))),
    //    Pattern.fromExpr(app(app(map, lam("x", app("f", app("g", "x")))), "in")))))

    //val plusComm = NamedStrategyS.init("rw-plus-comm", RewriteRule(SRewrite(app(app(add, ?(0)), ?(1)),
    // app(app(add, ?(1)), ?(0)))))
    val (lhs, rhs) = {
      import NamedRewriteDSL._
      NamedRewrite.toPatterns("add-comm", 
            (app(app(add, "x"), "y")
              -->
            app(app(add, "y"), "x")))
            // NamedRewrite.toPatterns("add-comm", 
            // (app(app(add, "x"), lf32(0.0f))
            //   -->
            // "x"))
    }
    val plusComm = NamedStrategyS.init("plus-comm", 
      RewriteRule(SRewrite(lhs, rhs)))
}
