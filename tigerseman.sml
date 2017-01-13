structure tigerseman :> tigerseman =
struct

open tigerabs
open tigersres
open tigertrans
open tigertemp

type expty = {exp: unit, ty: Tipo}

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList(
    tabNueva(),
    [("int", TInt), ("string", TString)])

val levelPila: tigertrans.level tigerpila.Pila = tigerpila.nuevaPila1(tigertrans.outermost) 
fun pushLevel l = tigerpila.pushPila levelPila l
fun popLevel() = tigerpila.popPila levelPila 
fun topLevel() = tigerpila.topPila levelPila

val tab_vars : (string, EnvEntry) Tabla = tabInserList(
    tabNueva(),
    [("print", Func{level=topLevel(), label="print",
        formals=[TString], result=TUnit, extern=true}),
    ("flush", Func{level=topLevel(), label="flush",
        formals=[], result=TUnit, extern=true}),
    ("getchar", Func{level=topLevel(), label="getstr",
        formals=[], result=TString, extern=true}),
    ("ord", Func{level=topLevel(), label="ord",
        formals=[TString], result=TInt, extern=true}),
    ("chr", Func{level=topLevel(), label="chr",
        formals=[TInt], result=TString, extern=true}),
    ("size", Func{level=topLevel(), label="size",
        formals=[TString], result=TInt, extern=true}),
    ("substring", Func{level=topLevel(), label="substring",
        formals=[TString, TInt, TInt], result=TString, extern=true}),
    ("concat", Func{level=topLevel(), label="concat",
        formals=[TString, TString], result=TString, extern=true}),
    ("not", Func{level=topLevel(), label="not",
        formals=[TInt], result=TInt, extern=true}),
    ("exit", Func{level=topLevel(), label="exit",
        formals=[TInt], result=TUnit, extern=true})
    ])

fun checkRepetidos ls = let val conjunto = Binaryset.addList (Binaryset.empty (String.compare), ls)
                        in (Binaryset.numItems conjunto) <> (length ls) end

fun tipoReal (TTipo (s, ref (SOME (t)))) = tipoReal t
  | tipoReal t = t

fun tiposIguales (TRecord _) TNil = true
  | tiposIguales TNil (TRecord _) = true 
  | tiposIguales (TRecord (_, u1)) (TRecord (_, u2 )) = (u1=u2)
  | tiposIguales (TArray (_, u1)) (TArray (_, u2)) = (u1=u2)
  | tiposIguales (TTipo (_, r)) b =
        let
            val a = case !r of
                SOME t => t
                | NONE => raise Fail "No debería pasar! (1)"
        in
            tiposIguales a b
        end
  | tiposIguales a (TTipo (_, r)) =
        let
            val b = case !r of
                SOME t => t
                | NONE => raise Fail "No debería pasar! (2)"
        in
            tiposIguales a b
        end
  | tiposIguales a b = (a=b)

fun transExp(venv, tenv) =
    let fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")
        fun trexp(VarExp v) = trvar(v)
        | trexp(UnitExp _) = {exp=unitExp(), ty=TUnit}
        | trexp(NilExp _)= {exp=nilExp(), ty=TNil}
        | trexp(IntExp(i, _)) = {exp=intExp i, ty=TInt}
        | trexp(StringExp(s, _)) = {exp=stringExp(s), ty=TString}
        | trexp(CallExp({func, args}, nl)) =
            let
                fun aux [] [] r = r
                  | aux [] _ _ = error("Sobran argumentos en la llamada a "^func, nl)
                  | aux _ [] _ = error("Faltan argumentos en la llamada a "^func, nl)
                  | aux (t::tt) (a::aa) r =
                      let val {exp=ae', ty=te'} = trexp a
                          val _ = if tiposIguales t te' then () else error("Error de tipos en la llamada a "^func, nl)
                      in aux tt aa r@[{exp=ae', ty=te'}] end

                val (targs, ext, tret, lab, level) =
                    case tabBusca (func, venv) of
                          NONE => error("No existe la función "^func, nl)
                        | SOME (Func {formals, extern, result, label, level}) => (formals, extern, result, label, level)
                        | SOME _ => error(func^" no es una funcion", nl)
                val leargs = aux targs args []
                val leargs' = map (#exp) leargs 
                val isproc = (tret = TUnit) 
            in
                {exp=callExp(lab,ext,isproc,level,leargs'),ty=tret}
            end
        | trexp(OpExp({left, oper=EqOp, right}, nl)) =
            let
                val {exp=expl, ty=tyl} = trexp left
                val {exp=expr, ty=tyr} = trexp right
            in
                if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then 
                    {exp=if tiposIguales tyl TString then binOpStrExp {left=expl,oper=EqOp,right=expr} else binOpIntRelExp {left=expl,oper=EqOp,right=expr}, ty=TInt}
                    else error("Tipos no comparables", nl)
            end
        | trexp(OpExp({left, oper=NeqOp, right}, nl)) = 
            let
                val {exp=expl, ty=tyl} = trexp left
                val {exp=expr, ty=tyr} = trexp right
            in
                if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then 
                    {exp=if tiposIguales tyl TString then binOpStrExp {left=expl,oper=NeqOp,right=expr} else binOpIntRelExp {left=expl,oper=NeqOp,right=expr}, ty=TInt}
                    else error("Tipos no comparables", nl)
            end
        | trexp(OpExp({left, oper, right}, nl)) = 
            let
                val {exp=expl, ty=tyl} = trexp left
                val {exp=expr, ty=tyr} = trexp right
            in
                if tiposIguales tyl tyr then
                    case oper of
                        PlusOp => if tipoReal tyl =TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
                        | MinusOp => if tipoReal tyl =TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
                        | TimesOp => if tipoReal tyl  =TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
                        | DivideOp => if tipoReal tyl =TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
                        | LtOp => if tipoReal tyl =TInt orelse tipoReal tyl =TString then
                            {exp=if tipoReal tyl =TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt} 
                            else error("Error de tipos", nl)
                        | LeOp => if tipoReal tyl =TInt orelse tipoReal tyl =TString then 
                            {exp=if tipoReal tyl =TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt} 
                            else error("Error de tipos", nl)
                        | GtOp => if tipoReal tyl =TInt orelse tipoReal tyl =TString then
                            {exp=if tipoReal tyl =TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt} 
                            else error("Error de tipos", nl)
                        | GeOp => if tipoReal tyl =TInt orelse tipoReal tyl =TString then
                            {exp=if tipoReal tyl =TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt} 
                            else error("Error de tipos", nl)
                        | _ => raise Fail "No debería pasar! (3)"
                else error("Error de tipos", nl)
            end
        | trexp(RecordExp({fields, typ}, nl)) =
            let
                (* Buscar el tipo *)
                val (tyr, cs) = case tabBusca(typ, tenv) of
                    SOME t => (case tipoReal t  of
                        TRecord (cs, u) => (TRecord (cs, u), cs)
                        | r => error(typ^" no es de tipo record. Es "^(printTipo r), nl))
                    | NONE => error("Tipo inexistente ("^typ^")", nl)
                
                (* Verificar que cada campo esté en orden y tenga una expresión del tipo que corresponde *)
                val exp_ord = Listsort.sort (fn ((a,_),(b,_))=> String.compare(a,b)) fields

                (* Traducir cada expresión de fields *)
                val tfields = map (fn (sy,ex) => (sy, trexp ex)) exp_ord
                fun verificar  [] [] = []
                  | verificar  (c::cs) [] = error("Faltan campos", nl)
                  | verificar  [] (c::cs) = error("Sobran campos", nl)
                  | verificar  ((s,t,n)::cs) ((sy,{exp,ty})::ds) =
                        if s<>sy then error("Error de campo", nl)
                        else if tiposIguales ty t then (exp, n)::(verificar cs ds)
                             else error("Error de tipo del campo "^s, nl)
                val lf = verificar cs tfields

            in
                {exp=recordExp lf, ty=tyr}
            end
        | trexp(SeqExp(s, nl)) =
            let val lexti = map trexp s
                val exprs = map (fn{exp, ty} => exp) lexti
                val {exp, ty=tipo} = hd(rev lexti)
            in { exp=seqExp (exprs), ty=tipo } end
        | trexp(AssignExp({var=SimpleVar s, exp}, nl)) =
            let
                val _ = case tabBusca (s,venv) of
                                NONE => error("Variable "^s^" no declarada",nl)
                              | SOME (VIntro _) => error("Variable "^s^" de solo lectura",nl)
                              | SOME (Func _) => error(s^" no es una variable",nl)
                              | SOME (Var _) => ()
                val {ty=tVar,exp=expvar} = trvar ((SimpleVar s),nl)
                val {ty=tExp,exp=expval} = trexp exp
            in
                if tiposIguales tExp tVar then
                   {exp=assignExp{var=expvar,exp=expval}, ty=TUnit}
                else
                   error("Error de tipos en la asignación",nl)
            end
        | trexp(AssignExp({var, exp}, nl)) =
            let
                val {ty=tVar,exp=expvar} = trvar (var, nl)
                val {ty=tExp,exp=expval} = trexp exp
            in
                if tiposIguales tExp tVar then
                   {exp=assignExp{var=expvar,exp=expval}, ty=TUnit}
                else
                   error("Error de tipos en la asignación",nl)
            end
        | trexp(IfExp({test, then', else'=SOME else'}, nl)) =
            let val {exp=testexp, ty=tytest} = trexp test
                val {exp=thenexp, ty=tythen} = trexp then'
                val {exp=elseexp, ty=tyelse} = trexp else'
            in
                if tipoReal tytest =TInt andalso tiposIguales tythen tyelse then
                {exp=if tipoReal tythen =TUnit then ifThenElseExpUnit {test=testexp,then'=thenexp,else'=elseexp} else ifThenElseExp {test=testexp,then'=thenexp,else'=elseexp}, ty=tythen}
                else error("Error de tipos en if" ,nl)
            end
        | trexp(IfExp({test, then', else'=NONE}, nl)) =
            let val {exp=exptest,ty=tytest} = trexp test
                val {exp=expthen,ty=tythen} = trexp then'
            in
                if tipoReal tytest =TInt andalso tythen=TUnit then
                {exp=ifThenExp{test=exptest, then'=expthen}, ty=TUnit}
                else error("Error de tipos en if", nl)
            end
        | trexp(WhileExp({test, body}, nl)) =
            let
                val {ty=ttest,exp=etest} = trexp test
                val _ = preWhileForExp()
                val {ty=tbody,exp=ebody} = trexp body
                val bodyInterCode = whileExp{test=etest,body=ebody}
                val _ = postWhileForExp()
            in
                if tipoReal ttest  = TInt andalso tbody = TUnit then {exp=bodyInterCode, ty=TUnit}
                else if tipoReal ttest  <> TInt then error("Error de tipo en la condición", nl)
                else error("El cuerpo de un while no puede devolver un valor", nl)
            end
        | trexp(ForExp({var, escape, lo, hi, body}, nl)) =
            let
                   val {ty=tylo,exp=explo} = trexp lo
                   val {ty=tyhi,exp=exphi} = trexp hi
                   val _ = if (tiposIguales tylo TInt) andalso (tiposIguales tyhi TInt) then ()
                           else error("Los límites del for deben ser enteros",nl)
                   val acc' = allocLocal (topLevel()) (!escape)
                   val lev = getActualLev()
                   val venv' = tabRInserta(var, VIntro {access=acc',level=lev}, venv)
                   val _ = preWhileForExp()
                   val {ty=tybody,exp=expbody} = transExp (venv', tenv) body
                   val _ = if tiposIguales tybody TUnit then () else error("El cuerpo de un for no puede devolver un valor", nl)
                   val ev' = simpleVar(acc',lev)
                   val ef' = forExp {lo=explo, hi=exphi, var=ev',body=expbody}
                   val _ = postWhileForExp()
               in
                   {exp=ef',ty=TUnit}
            end
        | trexp(LetExp({decs, body}, _)) =
            let
                fun transDecs (v,t) l [] = ((v,t),l)
                  | transDecs (v,t) l (h::td) =
                                    let val (v', t', l') = trdec (v,t) h
                                    in transDecs (v',t') (l@l') td end
                val ((venv',tenv'),le') = transDecs (venv,tenv) [] decs
                val {exp=be', ty=te'} = transExp (venv',tenv') body
            in 
                {exp=seqExp(le'@[be']), ty=te'}
            end
        | trexp(BreakExp nl) =
            ({exp=breakExp(), ty=TUnit}
             handle Empty => error("break fuera de bucle!!", nl))
        | trexp(ArrayExp({typ, size, init}, nl)) =
            let
                val (typArr,un) = case tabBusca (typ,tenv) of
                                       SOME t => (case tipoReal t  of 
                                                   TArray (t,u) => (t,u)
                                                 | _ => error("El tipo "^typ^" no es un arreglo",nl))
                                     | _ => error("El tipo "^typ^" no existe",nl)
                val {ty=tySize,exp=expsize} = trexp size
                   val {ty=tyInit,exp=expinit} = trexp init
               in
                   if (tiposIguales tySize TInt) andalso (tiposIguales typArr tyInit) 
                   then {exp=arrayExp{size=expsize,init=expinit},ty=TArray (typArr,un)}
                else error("Error en la definición del array",nl)
            end
        and trvar(SimpleVar s, nl) =
            (case tabBusca (s,venv) of
                  NONE => error("Variable "^s^" no declarada",nl)
                | SOME (VIntro {access,level}) => {exp=simpleVar(access,level),ty=TInt}
                | SOME (Var {ty=typ,access,level}) => {exp=simpleVar(access,level),ty=typ}
                | SOME _ => error(s^" no es una variable",nl))
        | trvar(FieldVar(v, s), nl) =
                 let val {exp=e',ty=t'} = trvar(v,nl)
                     val ltv = case (tipoReal t' ) of
                                    TRecord(l,_) => l
                                  | _ => error("No es un record (!)",nl)
                     val (tipo,lugar) = case List.find (fn x => #1 x = s) ltv of
                                             SOME s => (#2 s, #3 s)
                                           | NONE => error(s^" no es field",nl)
                 in {exp=fieldVar(e',lugar),ty=tipo} end
        | trvar(SubscriptVar(v, e), nl) = 
                 let val {exp=e',ty=t'} = trvar(v,nl)
                     val t = case (tipoReal t' ) of
                                    TArray(t,_) => t
                                  | _ => error("No es un array (!)",nl)
                     val {exp=e'', ty=tInd} = trexp e
                 in if tiposIguales tInd TInt then {exp=subscriptVar(e',e''),ty=t}
                                              else error("Se indexa con un no-entero",nl)
                 end

        and trdec (venv, tenv) (VarDec ({name,escape,typ=NONE,init},pos)) = 
            let val {ty=tipoInit,exp=einit} = transExp (venv,tenv) init
                val acc' = allocLocal (topLevel()) (!escape)
                val lev = getActualLev()
                val tReal = case tipoReal tipoInit  of
                               TFunc _ => error ("Una variable no puede almacenar una función. Var: "^name,pos) (* No creo que pueda pasar, pero por las dudas *)
                             | TNil => error ("No se puede inferir el tipo de Nil, en la declaración de "^name, pos)
                             | t => t
                val venv' = tabRInserta(name, Var {ty=tReal,access=acc',level=lev}, venv) 
            in  (venv',tenv,[assignExp{var=varDec(acc'),exp=einit}]) end
        | trdec (venv,tenv) (VarDec ({name,escape,typ=SOME s,init},pos)) =
            let val {ty=tipoInit,exp=einit} = transExp (venv,tenv) init
                val tReal = case tipoReal tipoInit  of
                               TFunc _ => error ("Una variable no puede almacenar una función. Var: "^name,pos) 
                             | t => t
                val tipoDef = case tabBusca(s,tenv) of
                                  SOME t => t
                                | _ => error("El tipo "^s^" no esta",pos)
                val acc' = allocLocal (topLevel()) (!escape)
                val lev = getActualLev()
            in  if tiposIguales tipoInit tipoDef then (tabRInserta(name, Var {ty=tipoDef,access=acc', level=lev}, venv),tenv,[assignExp{var=varDec(acc'),exp=einit}])
                                            else error("En la declaración de "^name^" los tipos no coinciden",pos) end
        | trdec (venv,tenv) (FunctionDec fs) =
            let fun formalsToTipos forms nl fc = List.map
                       (fn ({name,typ,escape}) =>
                                  case typ of
                                       NameTy t => 
                                           (case tabBusca(t,tenv) of 
                                                SOME tipo => fc (name, tipoReal tipo , escape)
                                              | _ => error("El tipo "^t^" no esta definido",nl))
                                     | _ => error ("Error interno 333",nl)
                       ) forms
                fun funcToEntry {name, params, result=NONE, body} nl =
                              let val _ = if checkRepetidos (map #name params) then error("Argumentos repetidos en "^name, nl) else ()
                                  val labName = if name="_tigermain" then name else  name^"_"^newlabel()
                                  val l = newLevel {parent=topLevel(),name=labName,formals=map (! o #escape) params}
                              in Func {level = l, label = labName,
                                    formals = formalsToTipos params nl #2,
                                    extern = false,
                                    result = TUnit} end
                  | funcToEntry {name, params, result=SOME s, body} nl =
                              let val tipResult = case tabBusca(s,tenv) of 
                                                   SOME t => tipoReal t 
                                                 | _ => error("El tipo "^s^" no esta definido",nl)
                                  val _ = if checkRepetidos (map #name params) then error("Argumentos repetidos en "^name,nl) else ()
                                  val labName = if name="_tigermain" then name else  name^"_"^newlabel()
                                  val l = newLevel {parent=topLevel(),name=labName,formals=map (! o #escape) params} 

                              in Func {level = l, label = labName, 
                                       formals = formalsToTipos params nl #2,
                                       extern = false,
                                       result = tipResult} end
                val _ = if checkRepetidos (map (#name o #1) fs) then error("Nombres repetidos en funciones", (#2 o hd) fs) else ()
                val venv' = List.foldl (fn ((fDec,pos),venvAnt) => tabRInserta(#name fDec, funcToEntry fDec pos,venvAnt)) venv fs
                fun funAlloc l (name,tipo,esc) = let val lev = getActualLev()
                                                     val acc = allocArg (topLevel()) (!esc)
                                                 in (name, Var {ty=tipo,access=acc,level=lev}) end
                fun checkBody(({name, params, result=NONE, body},nl),ret) = 
                             let val _ = preFunctionDec()
                                 val l = case tabBusca(name,venv') of
                                              NONE => error("No deberia pasar, en functionDec",nl)
                                            | SOME (Func {level,...}) => level
                                            | SOME _ => error("No es función, pero no deberia pasar",nl)
                                 val _ = pushLevel l
                                 val venvBody = tabInserList (venv', formalsToTipos params nl (funAlloc l))
                                 val {ty=tip, exp=ebody} = transExp (venvBody,tenv) body
                                 val fintercode = functionDec(ebody,topLevel(),true)
                                 val _ = popLevel()
                                 val _ = postFunctionDec()
                             in if tiposIguales tip TUnit then fintercode::ret else error("Error en el tipo de retorno del body de "^name,nl) end
                  | checkBody(({name, params, result=SOME s, body},nl),ret) = 
                             let val _ = preFunctionDec()
                                 val l = case tabBusca(name,venv') of
                                              NONE => error("No deberia pasar, en functionDec",nl)
                                            | SOME (Func {level,...}) => level
                                            | SOME _ => error("No es función, pero no deberia pasar",nl)
                                 val _ = pushLevel l
                                 val venvBody = tabInserList (venv', formalsToTipos params nl (funAlloc l))
                                 val {ty=tip, exp=ebody} = transExp (venvBody,tenv) body
                                 val fintercode = functionDec(ebody,topLevel(),false)
                                 val _ = popLevel()
                                 val _ = postFunctionDec()
                                 val tipResult = case tabBusca(s,tenv) of 
                                                   SOME t => t
                                                 | _ => error("El tipo "^s^" no esta definido",nl)  
                             in if tiposIguales tip tipResult then fintercode::ret else error("Error en el tipo de retorno del body de "^name,nl) end
                val lstFuncs = List.foldr checkBody [] fs
            in (venv',tenv,lstFuncs) end
        | trdec (venv,tenv) (TypeDec []) =
            (venv, tenv, []) 
        | trdec (venv,tenv) (TypeDec ldecs) =
            let val ldecs' = List.map #1 ldecs
                val _ = if checkRepetidos (map #name ldecs') then error("Nombres de tipos repetidos",(#2 o hd) ldecs) else ()
                val tenv' = tigertopsort.fijaTipos ldecs' tenv
                            handle tigertopsort.Ciclo => error("Ciclo!!",(#2 o hd) ldecs)
            in (venv,tenv',[]) end
    in trexp end
fun transProg ex =
    let val main =
                LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
                                result=SOME "int", body=ex}, 0)]],
                        body=UnitExp 0}, 0)
        val _ = transExp(tab_vars, tab_tipos) main
    in print "bien!\n" end
end
