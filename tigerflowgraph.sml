structure tigerflowgraph :> tigerflowgraph =
struct
    open tigergraph
    open tigerassem
    open Splayset
    open Splaymap
    open tigertab
    datatype flowgraph = FGRAPH of {control: graph,
				    def: tigertemp.temp set nodeDict,
				    use: tigertemp.temp set nodeDict,
				    ismove: bool nodeDict}

  (* Note:  any "use" within the block is assumed to be BEFORE a "def" 
        of the same variable.  If there is a def(x) followed by use(x)
       in the same block, do not mention the use in this data structure,
       mention only the def.

     More generally:
       If there are any nonzero number of defs, mention def(x).
       If there are any nonzero number of uses BEFORE THE FIRST DEF,
           mention use(x).

     For any node in the graph,  
           Graph.Table.look(def,node) = SOME(def-list)
           Graph.Table.look(use,node) = SOME(use-list)
   *)

   fun setFromList xs = addList (empty String.compare, xs)

   fun setSingleton x = singleton String.compare x

   fun printNodos ls = List.app (fn (a,n) => print((nodename n)^" => "^(assemToString  a))) ls

   fun printLabels labs = List.app (fn (l,n)=>print(l^" => "^(nodename n)^"\n")) (tabAList labs)

   fun printDatosNodo (n:node) (d:tigertemp.temp set nodeDict) u m =
                           (print("Nodo: "^nodename n^"\n  Pred: ");
                            List.app (fn n => print(nodename n^" ")) (pred n);
                            print("\n  Succ: ");
                            List.app (fn n => print(nodename n^" ")) (succ n);
                            if isSome(peek(d,n)) then (
                                print("\n  Def: ");
                                List.app (fn l => print(l^" ")) (Splayset.listItems (find(d,n)));
                                print("\n  Use: ");
                                List.app (fn l => print(l^" ")) (Splayset.listItems (find(u,n)));
                                print("\n  Move: ");
                                print(if find(m,n) then "True" else "False")) else ();
                            print("\n"))

   fun printFlowGraph g d u m = List.app (fn n => printDatosNodo n d u m) (nodes g)

   fun makeGraph instrLs dbg = 
               let val grafo = newGraph()
                   val labels = ref(tabNueva())

                   fun nodosYlabels [] = []
                     | nodosYlabels ((OPER a) :: xs) = (OPER a, newNode grafo) :: nodosYlabels xs
                     | nodosYlabels ((MOVE a) :: xs) = (MOVE a, newNode grafo) :: nodosYlabels xs
                     | nodosYlabels ((LABEL (a as {lab,...})) :: xs) = let val nYl = nodosYlabels xs
                                                                           val nodoProx = case nYl of
                                                                                             ((_,n)::_) => n
                                                                                           | _ => raise Fail ("Label "^lab^" sin destino")
                                                                           val _ = labels := tabInserta(lab,nodoProx,!labels)
                                                                       in nYl end
                   val nodos = nodosYlabels instrLs

                   val _ = if dbg then print("Comienza flujo: -----------------------------------\n") else ()
                   val _ = if dbg then printNodos nodos else ()
                   val _ = if dbg then printLabels (!labels) else ()


                   fun makeGraph' [] r = r
                     | makeGraph' [(OPER {dst,src,jump=NONE,...},nod)] (def,use,move) = 
                          let val nDef = insert (def, nod, setFromList dst)
                              val nUse = insert (use, nod, setFromList src)
                              val nMove = insert (move, nod, false)
                          in (nDef, nUse, nMove) end
                     | makeGraph' ((OPER {dst,src,jump=NONE,...},nod)::(pr,pNod)::xs) (def,use,move) = 
                          let val nDef = insert (def, nod, setFromList dst)
                              val nUse = insert (use, nod, setFromList src)
                              val nMove = insert (move, nod, false)
                              val _ = mk_edge{from=nod,to=pNod}
                          in makeGraph' ((pr,pNod)::xs) (nDef, nUse, nMove) end
                     | makeGraph' ((OPER {dst,src,jump=SOME js,...},nod)::xs) (def,use,move) = 
                          let val nDef = insert (def, nod, setFromList dst)
                              val nUse = insert (use, nod, setFromList src)
                              val nMove = insert (move, nod, false)
                              fun addArista j = let val nDes = tabSaca(j,!labels)
                                                in mk_edge{from=nod,to=nDes} end
                              val _ = List.app addArista js
                          in makeGraph' xs (nDef, nUse, nMove) end
                     | makeGraph' [(MOVE {dst,src,...},nod)] (def,use,move) = 
                          let val nDef = insert (def, nod, setSingleton dst)
                              val nUse = insert (use, nod, setSingleton src)
                              val nMove = insert (move, nod, true)
                          in (nDef, nUse, nMove) end
                     | makeGraph' ((MOVE {dst,src,...},nod)::(pr,pNod)::xs) (def,use,move) = 
                          let val nDef = insert (def, nod, setSingleton dst)
                              val nUse = insert (use, nod, setSingleton src)
                              val nMove = insert (move, nod, true)
                              val _ = mk_edge{from=nod,to=pNod}
                          in makeGraph' ((pr,pNod)::xs) (nDef, nUse, nMove) end
                     | makeGraph' _ _ =  raise Fail "Algo que no matchea en makeGraph"
                   val (d,u,m) = makeGraph' nodos (mkDict cmpNode,mkDict cmpNode,mkDict cmpNode)
                   val _ = if dbg then printFlowGraph grafo d u m else ()
                   val _ = if dbg then print("Termina flujo -----------------------------------\n") else ()
               in (FGRAPH {control=grafo,def=d,use=u,ismove=m},nodos) end

   fun flowGraph ls = makeGraph ls false
   fun flowGraphDebugging ls = makeGraph ls true
end
