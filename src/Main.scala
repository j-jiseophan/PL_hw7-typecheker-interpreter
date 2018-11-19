import Util._

object Main extends Homework07 {
//TODO: storelookup, envlookup
    trait CORELValue
    case class NumV(n: Int) extends CORELValue
    case class CloV(param: String,body: COREL, var env: Env) extends CORELValue
    case class RecV(recs: Map[String, CORELValue]) extends CORELValue
    case class BoolV(b: Boolean) extends CORELValue
    case class ConstructorV(name: String) extends CORELValue
    case class VariantV(name: String, value: CORELValue) extends CORELValue
    type Env = Map[String, CORELValue]

    
    // type environment
    case class TypeEnv(
        vars  : Map[String, Type] = Map(),
        tbinds: Map[String, Map[String, Type]] = Map()
    ){
        def addVar(x: String, t: Type): TypeEnv =
            copy(vars = vars + (x -> t))
        def addTBind(x: String, cs: Map[String, Type]): TypeEnv =
            copy(tbinds = tbinds + (x -> cs))
    }


    def run(str: String): String={
        def mustSame(left: Type, right: Type): Type =
            if (same(left, right)) left
            else error(s"$left is not equal to $right")
        def same(left: Type, right: Type): Boolean =
            (left, right) match {
                case (NumT, NumT) => true
                case (ArrowT(p1, r1), ArrowT(p2, r2)) =>
                same(p1, p2) && same(r1, r2)
                case _ => false
        }
        def validType(ty: Type, tyEnv: TypeEnv): Type = ty match {
            case NumT => ty
            case ArrowT(p, r) =>
            ArrowT(validType(p, tyEnv), validType(r, tyEnv))
            case IdT(x) =>
                if (tyEnv.tbinds.contains(x)) ty
                else error(s"$x is a free type")
        }
        def repeated_addVar(tenv: TypeEnv, m: Map[String, Type], tn: String): TypeEnv={
            m.isEmpty match{
                case false =>
                    repeated_addVar(tenv.addVar(m.last._1,
                                        ArrowT(m.last._2, IdT(tn))), m-m.last._1, tn)
                case true => tenv
            }
        }
        /*
        def repeated_caseCheck(tenv: TypeEnv, cases: Map[String, (String, COREL)], lst: List[Type]): List[Type]={
            cases.isEmpty match{
                case false =>
                    repeated_caseCheck(tenv, cases-cases.last._1, lst + typeCheck(cases.last._2._2,
                        tyEnv.addVar(cases.last._2._1, cs.getOrElse(cases.last._1._1,error(s"$cases.last._1._1 is free")))))
                case true => lst
            }
        }
        def repeated_mustSame(lst: List[Type]): Type = {
            lst.length match{
                case 1 => lst(0)
                case _ =>
                    mustSame(lst(0), lst(1))
                    repeated_mustSame(lst.drop(1))
            }
        }
*/
        def NumAdd(l: CORELValue, r: CORELValue): CORELValue={
            l match{
                case NumV(ln) => r match{
                    case NumV(rn) => NumV(ln+rn)
                }
            }
        }
        def NumSub(l: CORELValue, r: CORELValue): CORELValue={
            l match{
                case NumV(ln) => r match{
                    case NumV(rn) => NumV(ln-rn)
                }
            }
        }
        def NumEqual(l: CORELValue, r: CORELValue): CORELValue={
            l match{
                case NumV(ln) => r match{
                    case NumV(rn) => BoolV(ln==rn)
                }
            }
        }
        def lookup(name: String, env: Env): CORELValue =
            env.get(name) match {
                case Some(v) => v
                case None => error(s"free identifier: $name")
            }
        def appendall(target: Env, obj: Map[String, Type]) : Env ={
            obj.isEmpty match{
                case true => target
                case false => appendall(target+(obj.last._1 -> ConstructorV(obj.last._1)), obj-obj.last._1)
            }
        }
        def checkname(name: String, cases: Map[String, (String, COREL)]): (String, COREL)={
            if(cases.isEmpty) error(s"$name is a free constructor")
            if(name == cases.last._1) cases.last._2
            else checkname(name, cases-cases.last._1)
        }/*
        def typeCheck(expr: COREL, tenv: TypeEnv): Type = {
            expr match{
                case Num(n) => NumT
                case Bool(b) => BoolT
                case Add(l, r) => 
                    mustSame(typeCheck(l, tenv), NumT)
                    mustSame(typeCheck(r, tenv), NumT)
                    NumT
                case Sub(l, r) =>
                    mustSame(typeCheck(l, tenv), NumT)
                    mustSame(typeCheck(r, tenv), NumT)
                    NumT
                case Equ(l, r) =>
                    mustSame(typeCheck(l, tenv), NumT)
                    mustSame(typeCheck(r, tenv), NumT)
                    BoolT
                case Id(x) =>
                    tyEnv.getOrElse(x,error(s"$x is a free identifier"))
                case Fun(p, pt, b) =>
                    validType(pt, tyEnv)
                    ArrowT(pt, typeCheck(b, teEnv + (p -> pt)))
                case App(f, a) =>
                    val typef = typeCheck(f, tenv)
                    val typea = typeCheck(a, tenv)
                    typef match {
                        case ArrowT(t1, t2)=>
                            mustSame(t1, typea)
                        case _ => error(s"apply $typea to $typef")
                    }
                case IfThenElse(c, t, f) =>
                    mustSame(c, boolT)
                    type1=typeCheck(t, tenv)
                    type2=typeCheck(f, tenv)
                    mustSame(type1, type2)
                case Rec(f, ft, x, xt, b) =>
                    mustSame(ft, ArrowT(xt,typeCheck(b, tyEnv + (f -> ft, x -> xt))))
                case WithType(name, cons, b) =>
                    val tyEnvT = tenv.addTBind(tn, cons)
                    val tyEnvV = repeated_addVar(tyEnvT, cons, name)
                    validType(vft, tyEnvT)
                    validType(vst, tyEnvT)
                    typeCheck(b, tyEnvV)
                case Cases(name, c, cases)=>
                    val cs = tenv.tbinds.getOrElse(name, error(s"$tn is a free type"))
                    mustSame(typeCheck(c, tyEnv), IdT(name))
                    val lst = repeated_caseCheck(tenv, cases, List[Type]())
                    if(lst.length>1) repeated_mustSame(lst)
                    else lst(0)
                case TFun(p, e) =>
                    PolyT(p, typeCheck(e, tenv))
                case TApp(b, t) => typeCheck(b) match {
                    case PolyT(p, pb) => 
                        ArrowT(typeCheck(t, fenv), typecheck(pb, fenv+(p+typecheck(t, fenv))))
                    case _ => error(s"TAPP temporary error message")
                }



            }
        }*/
        def interp(w : COREL, env : Env): CORELValue={
            w match{
                case Num(n) => NumV(n)
                case Bool(b) => BoolV(b)
                case Add(l, r) => 
                    NumAdd(interp(l, env), interp(r, env))
                case Sub(l, r) => 
                    NumSub(interp(l, env), interp(r, env))
                case Equ(l, r)=>
                    NumEqual(interp(l, env), interp(r, env))
                case Id(id) => (lookup(id, env))
                case Fun(p, pt, b) => (CloV(p, b, env))
                
                case App(f, a) => interp(f, env) match{
                    case CloV(p, b ,fenv) =>
                        interp(b, fenv+(p->interp(a, env)))
                    case ConstructorV(name)=>
                        VariantV(name, interp(a, env))
                    case fv =>  error(s"not a closure: $fv")
                }
                case IfThenElse(c, t, f) => interp(c, env) match {
                    case BoolV(true) => interp(t, env)
                    case BoolV(false) => interp(f, env)
                }
                case Rec(name, _, param, _, body) =>
                    val cloV = CloV(param, body, env)
                    cloV.env = env + (name -> cloV)
                    cloV
                case WithType(name, cons, b) =>
                    val nenv = appendall(env, cons)
                    interp(b, nenv)
                case Cases(_, c, cases) => interp(c, env) match {
                    case VariantV(name, av) =>
                        val (p, b) = checkname(name, cases)
                        interp(b, env+(p -> av))
                    case v => error(s"not a variant: $v")
                }
                case TFun(n, e) => 
                    interp(e, env)
                case TApp(b, t) =>
                    interp(b, env)
                
                    
            }
        }
        def stringConversion(input: CORELValue): String={
            input match{
                case NumV(n) => n.toString
                case RecV(rec) => "record"
                case CloV(p, b, e) => "function"
            }
        }
        
        val result = interp(COREL(str), Map[String, CORELValue]())
        stringConversion(result)

    }
    def ownTests: Unit = {/*
        test(typeCheck("{tyfun {a} 3}"), Type("{^ a num}"))
        test(typeCheck("{tyfun {a} {tyfun {b} 3}}"), Type("{^ a {^ b num}}"))
        test(typeCheck("{tyfun {a} {fun {x: a} x}}"), Type("{^ a {a -> a}}"))
        test(typeCheck("{tyfun {a} {tyfun {b} {fun {x: {^ a {^ b a}}} x}}}"), Type("{^ a {^ b {{^ a {^ b a}} -> {^ a {^ b a}}}}}"))
        test(typeCheck("{@ {tyfun {a} {tyfun {b} {fun {x: {^ a {^ b a}}} x}}} num}"), Type("{^ b {{^ a {^ b a}} -> {^ a {^ b a}}}}"))
        test(typeCheck("{fun {x: {^ a a}} x}"), Type("{{^ a a} -> {^ a a}}"))
        testExc(typeCheck("{fun {x: {^ a {a -> b}}} x}"), "free")
        testExc(typeCheck("{tyfun {a} {fun {x: b} x}}"), "free")
        testExc(typeCheck("{@ {tyfun {a} {fun {x: b} x}} num}"), "free")
        testExc(typeCheck("{tyfun {a} {fun {x: a} {tyfun {b} {fun {y: b} {+ x y}}}}}"), "no")
        test(typeCheck("{tyfun {a} 3}"), Type("{^ a num}"))
        test(typeCheck("{tyfun {a} {tyfun {b} 3}}"), Type("{^ a {^ b num}}"))
        test(typeCheck("{tyfun {a} {fun {x: a} x}}"), Type("{^ a {a -> a}}"))
        test(typeCheck("{@ {tyfun {a} {fun {x: a} x}} {^ b {b -> b}}}"), Type("{{^ b {b -> b}} -> {^ b {b -> b}}}"))//good example
        test(typeCheck("{tyfun {a} {tyfun {b} 3}}"), Type("{^ a {^ b num}}"))
        test(typeCheck("{tyfun {a} {fun {x: a} x}}"), Type("{^ a {a -> a}}"))
        test(typeCheck("{tyfun {a} {tyfun {b} {fun {x: a} x}}}"), Type("{^ a {^ b {a -> a}}}"))
        test(typeCheck("{if true {tyfun {a} {fun {x: a} x}} {tyfun {b} {fun {y: b} y}}}"), Type("{^ a {a -> a}}"))
        test(typeCheck("{if true {tyfun {b} {fun {y: b} y}} {tyfun {a} {fun {x: a} x}}}"), Type("{^ b {b -> b}}"))
        test(typeCheck("{if {= 8 8} {tyfun {a} {tyfun {b} {fun {x: a} x}}} {tyfun {b} {tyfun {a} {fun {x: b} x}}}}"), Type("{^ a {^ b {a -> a}}}"))
        test(typeCheck("{tyfun {a} {fun {x: a} {tyfun {b} {fun {y: a} {if true x y}}}}}"), Type("{^ a {a -> {^ b {a -> a}}}}"))
        test(typeCheck("{tyfun {a} {fun {a: {num -> num}} {fun {x: a} x}}}"), Type("{^ a {{num -> num} -> {a -> a}}}"))
        test(typeCheck("{fun {a: {num -> num}} {tyfun {a} {fun {x: a} x}}}"), Type("{{num -> num} -> {^ a {a -> a}}}"))
        test(typeCheck("{@ {tyfun {a} {fun {x: {^ a {a -> a}}} x}} num}"), Type("{{^ a {a -> a}} -> {^ a {a -> a}}}"))
        test(typeCheck("{@ {tyfun {a} {fun {x: a} 5}} num}"), Type("{num -> num}"))
        test(typeCheck("{if {= 8 10} {tyfun {a} {tyfun {b} {fun {x: a} {fun {y: b} y}}}} {tyfun {b} {tyfun {a} {fun {x: b} {fun {y: a} y}}}}}"), Type("{^ a {^ b {a -> {b -> b}}}}"))
        test(typeCheck("{@ {tyfun {a} {fun {a: a} {{fun {x: {^ a {a -> a}}} {{@ x num} 10}} {tyfun {b} {fun {b: b} b}}}}} {num -> num}}"), Type("{{num -> num} -> num}"))
        test(typeCheck("{@ {tyfun {a} {fun {a: a} {{fun {x: {^ a {a -> a}}} {{@ x num} 10}} {tyfun {b} {fun {b: b} b}}}}} num}"), Type("{num -> num}"))
        test(typeCheck("{@ {tyfun {a} {fun {a: a} {{fun {x: {^ a {a -> a}}} {{@ x num} 10}} {tyfun {a} {fun {a: a} a}}}}} num}"), Type("{num -> num}"))
        test(typeCheck("{tyfun {a} 3}"), Type("{^ a num}"))
        test(typeCheck("{tyfun {a} {tyfun {b} 3}}"), Type("{^ a {^ b num}}"))
        test(typeCheck("{tyfun {a} {fun {x: a} x}}"), Type("{^ a {a -> a}}"))
        test(typeCheck("{if true {tyfun {a} {fun {x: a} x}} {tyfun {b} {fun {y: b} y}}}"), Type("{^ a {a -> a}}"))
        test(typeCheck("{if true {tyfun {b} {fun {y: b} y}} {tyfun {a} {fun {x: a} x}}}"), Type("{^ b {b -> b}}"))
        test(typeCheck("{if true {tyfun {a} {tyfun {b} {fun {x: a} x}}} {tyfun {b} {tyfun {a} {fun {x: b} x}}}}"), Type("{^ a {^ b {a -> a}}}"))
        test(typeCheck("{tyfun {a} {fun {x: a} {tyfun {b} {fun {y: a} {if true x y}}}}}"), Type("{^ a {a -> {^ b {a -> a}}}}"))
        test(typeCheck("{fun {x: {^ a a}} x}"), Type("{{^ a a} -> {^ a a}}"))
        test(typeCheck("{@ {tyfun {a} {tyfun {b} {fun {x: {^ a {^ b a}}} x}}} num}"), Type("{^ b {{^ a {^ b a}} -> {^ a {^ b a}}}}"))
        test(typeCheck("{{@ {@ {tyfun {a} {tyfun {b} {fun {x: a} x}}} num} num} 10}"), Type("num"))
*/
        test(run("{{{@ {tyfun {a} {fun {f: a} f}} {num -> num}} {fun {x: num} x}} 10}"), "10")
        test(run("{@ {tyfun {a} {fun {f: a} f}} {num -> num}}"), "function")
        test(run("{@ {@ {tyfun {a} {tyfun {b} 3}} num} num}"), "3")
        test(run("{tyfun {a} {fun {x: b} x}}"), "function")
        test(run("{{fun {x: num} {{fun {f: {num -> num}} {+ {f 1} {{fun {x: num} {f 2}} 3}}} {fun {y: num} {+ x y}}}} 0}"), "3")
        test(run("{@ {tyfun {a} {fun {x: a} x}} num}"), "function")
        test(run("{tyfun {a} {tyfun {b} 3}}"), "3")
        test(run("{{{@ {tyfun {a} {fun {f: a} f}} {num  -> num}} {fun {x: num} x}} 10}"), "10")
        test(run("{@ {tyfun {a} {fun {f: a} f}} {num -> num}}"), "function")
        test(run("{@ {@ {tyfun {a} {tyfun {b} 3}} num} num}"), "3")
        test(run("{@ {tyfun {a} {fun {f: a} f}} {num -> num}}"), "function")
        test(run("{{@ {if true {tyfun {a} {fun {x: a} x}} {tyfun {b} {fun {x: b} b}}} x} 30}"), "30")
        test(run("{{fun {x: {^ a {a -> a}}} {{@ x num} 10}} {tyfun {b} {fun {y: b} y}}}"), "10")
        test(run("{@ {tyfun {a} {fun {x: a} 5}} num}"), "function")
        test(run("{@ {tyfun {a} {fun {x: {^ a {a -> a}}} x}} num}"), "function")
        test(run("{{{@ {@ {tyfun {a} {tyfun {b} {fun {x: {a -> b}} x}}} num} num} {fun {x: num} {+ 5 x}}} 3}"), "8")
        test(run("{{{@ {@ {tyfun {a} {tyfun {a} {fun {x: {a -> a}} x}}} num} num} {fun {x: num} {+ 5 x}}} 3}"), "8")
        test(run("{@ {@ {tyfun {a} {tyfun {b} 3}} num} num}"), "3")
        test(run("{{@ {@ {tyfun {a} {tyfun {b} {fun {x: a} x}}} num} num} 10}"), "10")
        test(run("{{recfun {f: {num -> num} x: num} {if {= x 0} 0 {+ {f {- x 1}} x}}} 10}"), "55")

    }

}
