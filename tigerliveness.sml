structure tigerliveness :> tigerliveness =
struct
    open tigergraph
    open tigerflowgraph
    open Splayset
    open Splaymap
    datatype igraph = IGRAPH of {graph: graph,
                                 tnode: tigertemp.temp -> node,
                                 gtemp: node -> tigertemp.temp,
                                 moves: (node * node) list}

    fun calculaInOut (FGRAPH {control,def,use,ismove}) =
        let
           val inicial = List.foldr (fn (n,dict) => insert(dict, n, (empty String.compare, empty String.compare))) (mkDict cmpNode)(nodes control)
           fun calcNodo anterior (nodo,(inAnt,outAnt)) = let val inNue = union(Splaymap.find(use,nodo),difference(outAnt,Splaymap.find(def,nodo)))
                                                              fun getInAnt n = #1 (Splaymap.find(anterior,n))
                                                              val outNue = List.foldr (fn (n,st) => union(getInAnt n,st)) (empty String.compare) (succ nodo)
                                                         in (inNue, outNue) end
           fun iguales d1 d2 = List.foldr (fn ((k,(s1,s2)),b) =>
                                           let val (c1,c2) = Splaymap.find(d1,k)
                                           in b andalso
                                              Splayset.equal(s1,c1) andalso
                                              Splayset.equal(s2,c2) end) true (Splaymap.listItems d2)
           fun calcTodo anterior = let val nueva = Splaymap.map (calcNodo anterior) anterior
                                   in if iguales anterior nueva then nueva
                                                                else calcTodo nueva
                                   end
        in calcTodo inicial end

    fun liveMap fg = let val inOut = calculaInOut fg
                     in fn n => #2 (Splaymap.find(inOut,n)) end

    fun interferenceGraph (fgr as (FGRAPH  {control,def,use,ismove})) =
        let val inOut = calculaInOut fgr
            val igr = newGraph()
            fun getOut n = #2 (Splaymap.find(inOut,n))
            fun getDef n = Splaymap.find(def,n)
            fun getUse n = Splaymap.find(use,n)
            fun isMove n = Splaymap.find(ismove,n)
            fun getNodo t m inv = (case Splaymap.peek(m,t) of
                                        SOME n => (n,m,inv)
                                      | NONE => let val nod = newNode igr
                                                    val nM = insert(m,t,nod)
                                                    val nInv = insert(inv,nod,t)
                                                in (nod,nM,nInv) end)
            fun procesaNodo (n,r) =
                let val outSet = getOut n
                    val defSet = getDef n
                    val dstMove = if isMove n then SOME (hd(Splayset.listItems defSet)) else NONE
                    val srcMove = if isMove n then SOME (hd(Splayset.listItems(getUse n))) else NONE
                    fun aplicaADef (tempDef,res) = 
                        let fun aplicaAOut (tempOut,(mT,mG,lM)) =
                                let val (nodDef,nuemT,nuemG) = getNodo tempDef mT mG
                                    val (nodOut,nuemT',nuemG') = getNodo tempOut nuemT nuemG
                                in if (isSome(srcMove) andalso valOf(srcMove) = tempOut)
                                      orelse tempDef = tempOut
                                      then (nuemT',nuemG',lM)
                                      else (mk_edge {from=nodDef,to=nodOut};
                                            (nuemT',nuemG',lM))                
                                end
                        in Splayset.foldl aplicaAOut res outSet end
                    val (mT,mG,lM) = Splayset.foldl aplicaADef r defSet
                    val res = if isSome srcMove
                                 then let val (ndSr,mpT,mpG) = getNodo (valOf(srcMove)) mT mG
                                          val (ndDes,mpT',mpG') = getNodo (valOf(dstMove)) mpT mpG
                                      in (mpT',mpG',(ndSr,ndDes)::lM) end
                                 else (mT,mG,lM)
                in res end
            val (mapT,mapG,listaMoves) = List.foldl procesaNodo (mkDict String.compare,mkDict cmpNode, []) (nodes control)
            fun liveOut n = Splayset.listItems(getOut n)
        in (IGRAPH {graph=igr,
                    tnode=fn t => Splaymap.find(mapT,t),
                    gtemp=fn n => Splaymap.find(mapG,n),
                    moves=listaMoves},liveOut) end

    fun show (IGRAPH {graph,tnode,gtemp,moves}) =
              (List.app (fn n => (print(gtemp n^": ");
                                  Splayset.app (fn t => print(gtemp t^" ")) (addList(empty cmpNode, (adj n)));
                                  print("\n"))) (nodes graph);
               print("Moves: ");List.app (fn (t1,t2) => print("("^gtemp t1^","^gtemp t2^") ")) moves;
               print("\n")) 
end

