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
    def typeCheck(exp_str: String): Type ={
        val new_tenv = new TypeEnv
        def typeCheckCOREL(expr: COREL, tenv: TypeEnv = new_tenv): Type = {
            //println("-----------")
            //println("expr :" + expr)
            //println("tenv : " + tenv.vars)
            def mustSame(left: Type, right: Type): Type =
                if (same(left, right)) left
                else error(s"$left is not equal to $right")
            def same(left: Type, right: Type): Boolean =
                (left, right) match {
                    case (NumT, NumT) => true
                    case (BoolT, BoolT) => true
                    case (ArrowT(p1, r1), ArrowT(p2, r2)) =>
                        same(p1, p2) && same(r1, r2)
                    case (PolyT(p1, pb1), PolyT(p2, pb2)) =>
                        same(pb1, pb2)
                    case (IdT(x1), IdT(x2)) => true
                    case _ => false
            }
            def validType(ty: Type, tyEnv: TypeEnv): Type = ty match {
                case NumT => ty
                case BoolT => ty
                case ArrowT(p, r) =>
                ArrowT(validType(p, tyEnv), validType(r, tyEnv))
                case IdT(x) =>
                    println("x is " + x)
                    if (tyEnv.tbinds.contains(x)) ty
                    else if(tyEnv.vars.contains(x)) ty
                    else error(s"$x is a free type")
                case PolyT(p, b) =>
                    validType(b, tyEnv.addVar(p, IdT(p)))
            }
            def repeated_addVar(tenv: TypeEnv, m: Map[String, Type], tn: String): TypeEnv={
                m.isEmpty match{
                    case false =>
                        repeated_addVar(tenv.addVar(m.last._1,
                                            ArrowT(m.last._2, IdT(tn))), m-m.last._1, tn)
                    case true => tenv
                }
            }
            def repeated_validType(cons: Map[String, Type], tenv: TypeEnv): Type={
                cons.size match{
                    case 1 =>
                        validType(cons.last._2, tenv)
                    case _ =>
                        validType(cons.last._2, tenv)
                        repeated_validType(cons-cons.last._1, tenv)
                }

            }
            def repeated_caseCheck(tenv: TypeEnv, cases: Map[String, (String, COREL)], lst: List[Type], cs: Map[String, Type]): List[Type]={
                cases.isEmpty match{
                    case false =>
                        repeated_caseCheck(tenv, cases-cases.last._1, lst ++ List(typeCheckCOREL(cases.last._2._2,
                            tenv.addVar(cases.last._2._1, cs.apply(cases.last._1)))), cs)
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
            def type_replacer(target: Type, tenv: TypeEnv): Type={
                target match{
                    case IdT(x) => tenv.vars.apply(x)
                    case ArrowT(p, r) => ArrowT(type_replacer(p, tenv), type_replacer(r, tenv))
                    case _ => target
                }
            }
            expr match{
                case Num(n) => NumT
                case Bool(b) => BoolT
                case Add(l, r) => 
                    mustSame(typeCheckCOREL(l, tenv), NumT)
                    mustSame(typeCheckCOREL(r, tenv), NumT)
                    NumT
                case Sub(l, r) =>
                    mustSame(typeCheckCOREL(l, tenv), NumT)
                    mustSame(typeCheckCOREL(r, tenv), NumT)
                    NumT
                case Equ(l, r) =>
                    mustSame(typeCheckCOREL(l, tenv), NumT)
                    mustSame(typeCheckCOREL(r, tenv), NumT)
                    BoolT
                case Id(x) =>
                    tenv.vars.apply(x)
                    //tenv.getOrElse(x,error(s"$x is a free identifier")) TODO:error messaging
                case Fun(p, pt, b) =>
                    validType(pt, tenv)
                    ArrowT(pt, typeCheckCOREL(b, tenv.addVar(p, pt)))
                case App(f, a) =>
                    val typef = typeCheckCOREL(f, tenv)
                    val typea = typeCheckCOREL(a, tenv)
                    typef match {
                        case ArrowT(t1, t2)=>
                            mustSame(t1, typea)
                        case _ => error(s"apply $typea to $typef")
                    }
                case IfThenElse(c, t, f) =>
                    mustSame(typeCheckCOREL(c, tenv), BoolT)
                    val type1=typeCheckCOREL(t, tenv)
                    val type2=typeCheckCOREL(f, tenv)
                    mustSame(type1, type2)
                case Rec(f, ft, x, xt, b) =>
                    mustSame(ft, ArrowT(xt, typeCheckCOREL(b, tenv.addVar(f, ft).addVar(x, xt))))
                case WithType(name, cons, b) =>
                    val tyEnvT = tenv.addTBind(name, cons)
                    val tyEnvV = repeated_addVar(tyEnvT, cons, name)
                    repeated_validType(cons, tyEnvT)
                    typeCheckCOREL(b, tyEnvV)
                case Cases(name, c, cases)=>
                    val cs =  tenv.tbinds.apply(name)
                    mustSame(typeCheckCOREL(c, tenv), IdT(name))
                    val lst = repeated_caseCheck(tenv, cases, List[Type](), cs)// list of types
                    if(lst.length>1) repeated_mustSame(lst)
                    else lst(0)
                case TFun(p, e) =>
                    PolyT(p, typeCheckCOREL(e, tenv.addVar(p, IdT(p))))
                case TApp(b, t) => 
                    validType(t, tenv)
                    typeCheckCOREL(b, tenv) match {
                        case PolyT(p, pb) => 
                            type_replacer(pb, tenv.addVar(p,t))
                        case _ => error(s"TAPP temporary error message")
                }



            }
        }
        typeCheckCOREL(COREL(exp_str), new_tenv)
    }

    def run(str: String): String={
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
        }
        
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
    def ownTests: Unit = {
        test(typeCheck("{@ {tyfun {a} {fun {a: a} {{fun {x: {^ a {a -> a}}} {{@ x num} 10}} {tyfun {b} {fun {b: b} b}}}}} {num -> num}}"), Type("{{num -> num} -> num}"))//this fails
        test(typeCheck("{@ {tyfun {a} {fun {a: a} {{fun {x: {^ a {a -> a}}} {{@ x num} 10}} {tyfun {b} {fun {b: b} b}}}}} num}"), Type("{num -> num}"))//fails
        test(typeCheck("{@ {tyfun {a} {fun {a: a} {{fun {x: {^ a {a -> a}}} {{@ x num} 10}} {tyfun {a} {fun {a: a} a}}}}} num}"), Type("{num -> num}"))//fails
        test(typeCheck("{{@ {@ {tyfun {a} {tyfun {b} {fun {x: a} x}}} num} num} 10}"), Type("num")) //fails
        test(typeCheck("{withtype {foo {a num} {b num}} {cases foo {a 3} {a {n} {+ n 3}} {b {n} {+ n 4}}}}"), Type("num")) //fails

    }

}
