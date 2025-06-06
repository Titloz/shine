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

    val skip = NamedStrategyS.init("skip", Skip)
    
    val plusComm = {
      val (lhs, rhs) = {
        import NamedRewriteDSL._
        NamedRewrite.toPatterns("add-comm", 
              (app(app(add, "x"), "y")
                -->
              app(app(add, "y"), "x")))
      }
      NamedStrategyS.init("plus-comm", 
      RewriteRule(SRewrite(lhs, rhs)))
    }

    val id_plusComm = NamedStrategyS.init("id-plus-comm",
      ComposeSeq(plusComm.to_strat(), plusComm.to_strat()))

    val plusComm_idplusComm = NamedStrategyS.init("pcipc",
      ComposeSeq(plusComm.to_strat(), id_plusComm.to_strat()))

    val plusComm_skip = NamedStrategyS.init("pc-skip",
      ComposeSeq(plusComm.to_strat(), skip.to_strat()))

     
    val timesZero = {
      val zero : Float = 0.0F
      val (lhs, rhs) = {
        import NamedRewriteDSL._
        NamedRewrite.toPatterns("times-zero", 
              (app(app(mul, "x"), l(rcs.FloatData(zero)))
                -->
              l(rcs.FloatData(zero))))
      }
      NamedStrategyS.init("times-zero",
      RewriteRule(SRewrite(lhs, rhs)))
    }

    val lc_plusComm_timesZero = NamedStrategyS.init("",
      LeftChoice(plusComm.to_strat(), timesZero.to_strat()))

    def `try`(s : StrategyS) : StrategyS = {
      ComposeSeq(s, Skip)
    }

    def repeat(s: StrategyS, n: Int) : StrategyS = {
      if (n == 0){
        `try`(s)
      } else {
        `try`(s, repeat(s, n-1))
      }
    }

}
