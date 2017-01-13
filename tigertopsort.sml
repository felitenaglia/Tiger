structure tigertopsort :> tigertopsort =
struct

open tigerabs
open tigersres

infix -- --- (* resta de listas *)
infix rs ls (* right y left sections*)

fun x ls f = fn y => f (x,y)
fun f rs y = fn x => f (x,y)
fun l -- e = List.filter (op <> rs e) l
fun fst(x,_) = x and snd(_,y) = y
fun lp --- e = List.filter ((op<> rs e) o fst) lp
exception Ciclo

(* Debug *)
fun printDBG s = print s
fun printPares (a,b) = printDBG("("^a^", "^b^") ")
fun printTipEntry (a,b) = printDBG("{"^a^", "^printTipo b^"} ")


fun checkRepetidos lst = let val conjunto = Binaryset.addList (Binaryset.empty (String.compare), lst)
                         in (Binaryset.numItems conjunto) <> (length lst) end

fun topsort p = 
       let fun candidatos p e = List.filter (fn e => List.all((op<> rs e) o snd) p) e
           fun tsort p [] res = rev res
             | tsort [] st res = rev (st@res)
             | tsort p (st as (h::t)) res =
                    let val x = (hd(candidatos p st)) handle Empty => raise Ciclo
                    in tsort (p---x) (st--x) (x::res) end
           fun elementos lt =
                  List.foldr (fn((x,y),l)=>
                                     let val l1 = case List.find (op= rs x) l of
                                                       NONE => x::l
                                                     | _ => l 
                                         val l2 = case List.find (op= rs y) l1 of
                                                       NONE => y::l1
                                                     | _ => l1
                                     in l2 end) [] lt
       in tsort p (elementos p) [] end
       
fun buscaRecords lt = 
       let fun buscaRecs [] recs = recs
             | buscaRecs ((r as {name,ty=RecordTy _})::t) recs = buscaRecs t (r::recs)
             | buscaRecs (_::t) recs = buscaRecs t recs
       in buscaRecs lt [] end

fun genPares lt =
       let val lrecs = buscaRecords lt
           fun genP [] res = res
             | genP ({name,ty=NameTy s}::t) res = genP t ((s,name)::res)
             | genP ({name,ty=ArrayTy s}::t) res = genP t ((s,name)::res)
             | genP ({name,ty=RecordTy lf}::t) res = genP t res(*
                        let fun recorre({typ=NameTy x,...}::t) =
                                 (case List.find ((op= rs x) o #name) lrecs of
                                       SOME _ => recorre t
                                     | NONE => x::recorre t)
                              | recorre(_::t) = recorre t
                              | recorre [] = []
                            val res' = recorre lf
                            val res'' = List.map (fn x => (x, name)) res'
                        in genP t (res''@res) end*)
       in genP lt [] end
      
fun procesa [] pares recs env = env
  | procesa (sorted as (h::t)) (pares : {name: symbol, ty: ty} list) (recs : {name: symbol, ty: ty} list) env =
       let fun filt h {name,ty=NameTy t} = h = t
             | filt h {name,ty=ArrayTy t} = h = t
             | filt h {name,ty=RecordTy lt} = false 
           val (ps,ps') = List.partition (filt h) pares
           val tt = case List.find ((h ls op=) o #name) recs of
                          SOME {name,...} => TTipo (name, ref NONE)
                        | NONE => case tabBusca(h,env) of
                                      SOME t => t
                                     | _ => raise Fail (h^" no existe")
           val env' = List.foldr (fn ({name,ty=NameTy ty},env') => (tabRInserta(name,tt,env'))
                                    |({name,ty=ArrayTy ty},env') => tabRInserta(name,TArray (tt, ref ()), env')
                                    |({name,...},_) => raise Fail ("Error interno 666+2 "^name)) env ps
       in procesa t ps' recs env' end

fun procRecords recs env =
       let fun buscaEnv env' t = case tabBusca (t,env) of
                                      SOME (x as (TRecord _)) => TTipo (t,ref (SOME x))
                                    | SOME t' => t'
                                    | _ => case tabBusca(t,env') of
                                                SOME (x as (TRecord _)) => TTipo (t, ref (SOME x))
                                              | SOME t' => t'
                                              | _ => case List.find (fn {name,...} => name = t) recs of
                                                          SOME {name,...} => TTipo (name, ref NONE)
                                                        | _ => raise Fail (t^" *** no existe!!")
           fun precs [] env' = env'
             | precs ({name, ty=RecordTy lf}::t) env' =
                     let val _ = if checkRepetidos (map #name lf) then raise Fail ("Campos repetidos en "^name) else ()
                         val lf' = List.foldl (fn  ({name,typ=NameTy t,...},l) => (name, buscaEnv env' t)::l
                                               | _ => raise Fail "No deberia pasar 324") [] lf
                         val (_, lf'') = List.foldl (fn ((x,y),(n,l)) => (n-1,(x,y,n)::l)) (length(lf)-1,[]) lf'
                         val lf3 = Listsort.sort (fn ((a,_,_),(b,_,_))=> String.compare(a,b)) lf''
                         val env'' = tabRInserta (name, TRecord (lf3, ref()), env')
                     in precs t env'' end
             | precs _ _ = raise Fail "Error interno 666"
       in precs recs env end

fun fijaNone (name, TArray ((TTipo (s, r),u))) env =
		(case r of
 		    ref (SOME _) => ()
		  | ref NONE => (case tabBusca(s,env) of 
				SOME (t as (TRecord _)) => r := SOME t
                              | _ => raise Fail "Error interno 666+1"))
  | fijaNone (name, TRecord (lf,_)) env =
                let fun busNone (s,TTipo (t,r),n) = 
			(case r of
	 		    ref (SOME _) => ()
			  | ref NONE => (case tabBusca(t,env) of 
					SOME (tt as (TRecord _)) => r := SOME tt
		                      | _ => raise Fail "Error interno 666+1"))
                      | busNone _ = ()
                in List.app busNone lf end
  | fijaNone _ _ = ()
fun fijaTipos batch env =
    let val pares = genPares batch
        val recs = buscaRecords batch
        val ordered = topsort pares
        val env' = procesa ordered batch recs env
        val env'' = procRecords recs env'
        val _ = List.app (fn e => fijaNone e env'') (tabAList env'')
    in env'' end

end
