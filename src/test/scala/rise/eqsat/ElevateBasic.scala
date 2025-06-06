package rise.eqsat

import rise.{core => rc}
import rise.core.{types => rct}
import ProveEquiv.syntax._

import ElevateEqsat._
import elevate.core.{Strategy, Success, Failure, RewriteResult}
import rise.elevate.Rise
import Pattern._
import elevate.macros.StrategyMacro
import meta.parser.rise.Type

class ElevateBasic extends test_util.Tests {
    import Basic._

    import rise.core.DSL._
    import rise.core.DSL.Type._
    import rise.core.primitives._

    /*
    def fails(s : Strategy[Rise], t : Rise) : Boolean = 
        s(t) match {
            case Failure(_) => true;
            case _ => false;
        }

    test("prove_equiv_BENF"){
        val `__` = rct.TypePlaceholder
        def wrap(inner: ToBeTyped[rc.Expr] => ToBeTyped[rc.Expr])
            : rc.Expr =
            depFun((n: rct.Nat) =>
            depFun((dt1: rct.DataType) => depFun((dt2: rct.DataType) =>
            fun(f =>
            inner(f :: dt1 ->: dt2) :: ((n`.`dt1) ->: `__`)
        ))))
        val x = wrap(f => map(f) >> slide(3)(1) >> slide(4)(2))
        assert(prove_equiv_BENF(Seq(rules.mapFusion, rules.mapFission, rules.slideBeforeMapMapF))(x)(wrap(f =>
        slide(3)(1) >> slide(4)(2) >> map(map(map(f))))) == Success(x))
    } 

    test("prove_equiv_CNF"){
        val x = withArrayAndFuns(4, in => f => in |> map(f(0) >> f(1)) |> map(f(2) >> f(3)))
        assert(prove_equiv_CNF(Seq(rules.combinatory.compositionAssoc1,
        rules.combinatory.compositionAssoc2,
        rules.combinatory.mapFusion),Seq())(x)(withArrayAndFuns(4, in => f =>
        in |> map(f(0)) |> map(f(1)) |> map(f(2)) |> map(f(3)))) == Success(x))
    }

    test("runCNF"){
        //TODO
    }

    test("runBENF"){
        //TODO
    }

    test("termguided_pe_BENF"){
        val `__` = rct.TypePlaceholder
        def wrap(inner: ToBeTyped[rc.Expr] => ToBeTyped[rc.Expr])
            : rc.Expr =
            depFun((n: rct.Nat) =>
            depFun((dt1: rct.DataType) => depFun((dt2: rct.DataType) =>
            fun(f =>
            inner(f :: dt1 ->: dt2) :: ((n`.`dt1) ->: `__`)
        ))))
        val x = wrap(f => map(f) >> slide(3)(1) >> slide(4)(2))
        assert(termguided_pe_BENF(Seq(rules.mapFusion, rules.mapFission, rules.slideBeforeMapMapF), List(x))(wrap(f =>
        slide(3)(1) >> slide(4)(2) >> map(map(map(f))))) == Success(x))
    }

    test("termguided_pe_CNF"){
        //TODO
    }

    test("no_failure_termguided_pe_BENF"){
        val `__` = rct.TypePlaceholder
        def wrap(inner: ToBeTyped[rc.Expr] => ToBeTyped[rc.Expr])
            : rc.Expr =
            depFun((n: rct.Nat) =>
            depFun((dt1: rct.DataType) => depFun((dt2: rct.DataType) =>
            fun(f =>
            inner(f :: dt1 ->: dt2) :: ((n`.`dt1) ->: `__`)
        ))))
        val x = wrap(f => map(f) >> slide(3)(1) >> slide(4)(2))
        val y = withArrayAndFuns(4, in => f => in |> map(f(0) >> f(1)) |> map(f(2) >> f(3)))
        val s = termguided_pe_BENF(Seq(rules.mapFusion, rules.mapFission, rules.slideBeforeMapMapF), List(x))
        assert(fails(s,y))
        assert(no_failure_termguided_pe_BENF(Seq(rules.mapFusion, rules.mapFission, rules.slideBeforeMapMapF), List(x))(y) == Success(y)) 
    }

    test("no_failure_termguided_pe_CNF"){
        //TODO
    }

    test("runOne_acc"){
        //TODO
    }

    test("runOne"){
        //TODO
    }

    test("guided_eqsat"){
        import rise.eqsat.SketchDSL._

        // see shine/src/main/scala/benchmarks/eqsat/tiling.scala lines 116-140
    }

    test("no_failure_guided_eqsat"){
        //TODO
    }

    test("toStrategyRise"){
        //TODO
    }

    test("basic, plusComm"){
        val plusComm = {
            import NamedRewriteDSL._
            NamedRewrite.init("plus-comm",
            app(app(add, "x"), "y")
                -->
            app(app(add, "y"), "x"))
        }


        //import ExprDSL._
        import ExprDSL._
        import ProveEquiv.syntax._

        ProveEquiv.init().runBENF2(
            one(app(app(add(f32 ->: f32 ->: f32), %(0, f32)), %(1, f32))),
            one(app(app(add(f32 ->: f32 ->: f32), %(1, f32)), %(0, f32))),
            Seq(plusComm)
        )
    }
    */
    test("srun basic, plusComm"){
        /*import ExprDSL._*/
        /*import rise.core.DSL._
        import rise.core.DSL.Type._
        import rise.core.primitives._*/
        import ExprDSL._
        import SProveEquiv.syntax._

        SProveEquiv.init().run(
            one(app(app(add(f32 ->: f32 ->: f32), %(0, f32)), %(1, f32))),
            one(app(app(add(f32 ->: f32 ->: f32), %(1, f32)), %(0, f32))),
            Seq(strategies.plusComm)
        )
        
    }

    test("srun basic, id_plusComm"){
        import ExprDSL._
        import SProveEquiv.syntax._

        SProveEquiv.init().run(
            one(app(app(add(f32 ->: f32 ->: f32), %(0, f32)), %(1, f32))),
            one(app(app(add(f32 ->: f32 ->: f32), %(1, f32)), %(0, f32))),
            Seq(strategies.plusComm_idplusComm)
        )
    }

    test("srun basic, skip"){
        import ExprDSL._
        import SProveEquiv.syntax._

        SProveEquiv.init().run(
            one(app(app(add(f32 ->: f32 ->: f32), %(0, f32)), %(1, f32))),
            one(app(app(add(f32 ->: f32 ->: f32), %(1, f32)), %(0, f32))),
            Seq(strategies.plusComm_skip)
        )
    }

    test("srun, left choice"){
        import rise.core.semantics._
        import ExprDSL._
        import SProveEquiv.syntax._
        
        val zero : Float = 0.0F
        SProveEquiv.init().run(
            one(app(app(mul(f32 ->: f32 ->: f32), app(app(add(f32 ->: f32 ->: f32), %(0, f32)), %(1, f32))), l(FloatData(zero)))),
            one(l(FloatData(zero))),
            Seq(strategies.lc_plusComm_timesZero)
        )
    }
}