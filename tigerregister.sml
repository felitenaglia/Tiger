structure tigerregister :> tigerregister = struct

    open Splayset
    open Splaymap
    open tigerframe
    open tigerflowgraph
    open tigerassem

    type allocation = (tigertemp.temp, register) dict

    val precolored = addList(empty String.compare,registers)
    val k = length(registers)
    val colorInit = List.foldl (fn (r,d) => insert(d,r,r)) (mkDict String.compare) registers

    val vacSetStr = empty String.compare
    val vacSetNod = empty tigergraph.cmpNode

    fun pop s = (hd(!s) before s:=tl(!s))

    fun push s e = (s := e::(!s))

    fun cmpParS ((a1,b1),(a2,b2)) = (case String.compare(a1,a2) of
                                       EQUAL => String.compare(b1,b2)
                                      | x => x)

    fun addToSet s e = (s:=add(!s,e))
    fun addListToSet s ls = (s:=addList(!s,ls))
    fun sacaElem s e = (if member(!s,e) then s:=delete(!s,e) else ())

    fun findElem m k n = (case peek(!m,k) of
                              NONE => n
                            | SOME v => v)

    fun allocAux (fr,bd,init,flagDebug) =
      let 
          val inicial = ref init
          val simplifyWorklist = ref (empty String.compare)
          val freezeWorklist = ref (empty String.compare)
          val spillWorklist = ref (empty String.compare)
          val spilledNodes = ref (empty String.compare)
          val coalescedNodes = ref (empty String.compare)
          val coloredNodes = ref (empty String.compare)
          val selectStack = ref []
          val coalescedMoves = ref (empty tigergraph.cmpNode)
          val constrainedMoves = ref (empty tigergraph.cmpNode)
          val frozenMoves = ref (empty tigergraph.cmpNode)
          val worklistMoves = ref (empty tigergraph.cmpNode)
          val activeMoves = ref (empty tigergraph.cmpNode)
          val adjSet = ref (empty cmpParS)
          val adjList = ref (mkDict String.compare) 
          val degree = ref (mkDict String.compare)
          val moveList = ref (mkDict String.compare)
          val alias = ref (mkDict String.compare)
          val color = ref colorInit
          val (flujo,nodosInstr) = tigerflowgraph.flowGraph bd
          val (def,use,ismove) = case flujo of FGRAPH {def,use,ismove,...} => (def,use,ismove)
          val liveMap = tigerliveness.liveMap flujo
          val spillCost = ref (mkDict String.compare)

          fun printDbg s = if flagDebug then print(s) else ()

          fun addEdge(u,v) =
              if not(member(!adjSet,(u,v))) andalso u<>v then
                 (addListToSet adjSet [(u,v),(v,u)];
                  if not(member(precolored,u)) then
                     (adjList := insert(!adjList,u,add(findElem adjList u vacSetStr,v));
                      degree := insert(!degree,u,1+findElem degree u 0)) else ();
                  if not(member(precolored,v)) then 
                     (adjList := insert(!adjList,v,add(findElem adjList v vacSetStr,u));
                      degree := insert(!degree,v,1+findElem degree v 0)) else ())
              else ()

          fun build() = if not(null(nodosInstr)) then 
                         (let val revInstr = rev nodosInstr
                              val live = ref (empty String.compare)
                              fun procInstruc (_,i) = 
                                 (live := liveMap i;
                                  if find(ismove,i) then
                                     (live:=difference(!live,find(use,i));
                                      Splayset.app (fn n => moveList := insert(!moveList,n,add(findElem moveList n vacSetNod,i))) (find(def,i));
                                      Splayset.app (fn n => moveList := insert(!moveList,n,add(findElem moveList n vacSetNod,i))) (find(use,i));
                                      addToSet worklistMoves i ) else ();
                                  Splayset.app (fn n => spillCost := insert(!spillCost,n,1.0+findElem spillCost n 0.0)) (find(def,i));
                                  Splayset.app (fn n => spillCost := insert(!spillCost,n,1.0+findElem spillCost n 0.0)) (find(use,i));
                                  live:=union(!live,find(def,i));
                                  Splayset.app (fn d => Splayset.app (fn l => addEdge(l,d)) (!live)) (find(def,i)))
                          in (List.app procInstruc revInstr; 
                              spillCost := Splaymap.map (fn (k,n) => let val d = Real.fromInt(findElem degree k 0)
                                                                     in  if d = 0.0 then 999999999.0 else n/d end) (!spillCost)) end) else ()

          fun nodeMoves(n) = intersection(findElem moveList n vacSetNod,union(!activeMoves, !worklistMoves))

          fun moveRelated(n) = not(isEmpty(nodeMoves(n)))

          fun makeWorkList() =
              Splayset.app (fn n => if findElem degree n 0 >= k then 
                                       addToSet spillWorklist n
                                    else if moveRelated(n) then
                                       addToSet freezeWorklist n
                                    else
                                       addToSet simplifyWorklist n ) (!inicial)

          fun adjacent(n) = difference(findElem adjList n vacSetStr, union(addList(vacSetStr,!selectStack),!coalescedNodes))

          fun enableMoves(nodes) =
              Splayset.app (fn n => Splayset.app (fn m =>
                                          if member(!activeMoves,m) then
                                             (sacaElem activeMoves m;
                                              addToSet worklistMoves m)
                                          else ()) (nodeMoves(n))) nodes

          fun decrementDegree(m) = 
              let val d = findElem degree m 0
                  val _ = insert(!degree,m,d-1)
              in if d = k then
                    (enableMoves(add(adjacent(m),m));
                     sacaElem spillWorklist m;
                     if moveRelated(m) then addToSet freezeWorklist m else addToSet simplifyWorklist m)
                 else () end

          fun simplify() = 
              let val n = hd(Splayset.listItems(!simplifyWorklist))
              in (sacaElem simplifyWorklist n;
                  push selectStack n;
                  Splayset.app (fn m => decrementDegree(m)) (adjacent(n))) end

          fun addWorkList(u) = if (not(member(precolored,u)) andalso not(moveRelated(u)))
                                  andalso findElem degree u 0 < k then
                                      (sacaElem freezeWorklist u;
                                       addToSet simplifyWorklist u) else ()

          fun ok(t,r) = findElem degree t 0 < k orelse member(precolored,t) orelse member(!adjSet, (t,r))

          fun conservative(nodes) = 
              (Splayset.foldl (fn (n,r) => if findElem degree n 0 >= k then r+1 else r) 0 nodes) < k

          fun getAlias(n) = if member(!coalescedNodes, n) then getAlias(find(!alias, n)) else n

          fun combine(u,v) = 
              (if member(!freezeWorklist,v) then sacaElem freezeWorklist v else sacaElem spillWorklist v;
               addToSet coalescedNodes v;
               alias := insert(!alias,v,u);
               moveList := insert(!moveList,u,union(findElem moveList u vacSetNod,findElem moveList v vacSetNod));
               enableMoves(singleton String.compare v);
               Splayset.app (fn t => (addEdge(t,u);decrementDegree(t))) (adjacent(v));
               if findElem degree u 0 >= k andalso member(!freezeWorklist, u) then
                  (sacaElem freezeWorklist u;addToSet spillWorklist u) else ())
 
          fun coalesce() = let val m = hd(Splayset.listItems(!worklistMoves))
                               val x = getAlias(hd(Splayset.listItems(find(def,m))))
                               val y = getAlias(hd(Splayset.listItems(find(use,m))))
                               val (u,v) = if member(precolored,y) then (y,x) else (x,y)
                               val _ = sacaElem worklistMoves m
                           in if u = v then
                                 (addToSet coalescedMoves m;addWorkList(u))
                              else if member(precolored,v) orelse member(!adjSet,(u,v)) then
                                 (addToSet constrainedMoves m;addWorkList(u);addWorkList(v))
                              else if member(precolored,u) andalso Splayset.foldl (fn (t,r) => r andalso ok(t,u)) true (adjacent(v))
                                      orelse not(member(precolored,u)) andalso 
                                             conservative(union(adjacent(u),adjacent(v))) then
                                 (addToSet coalescedMoves m;combine(u,v);addWorkList(u))
                              else addToSet activeMoves m end

          fun assignColors() =
             (List.app (fn n => let val okColors = ref (addList(empty String.compare,registers))
                                in (Splayset.app
                                      (fn w => let val aliW = getAlias(w) in
                                                if member(!coloredNodes, aliW) orelse 
                                                   member(precolored, aliW) then
                                                      sacaElem okColors (findElem color aliW "") else ()
                                                end) (findElem adjList n vacSetStr);
                                    if isEmpty(!okColors) then
                                       addToSet spilledNodes n
                                    else
                                       (addToSet coloredNodes n;
                                        color := insert(!color,n,hd(Splayset.listItems(!okColors))))) end) (!selectStack);
             Splayset.app (fn n => color := insert(!color,n,findElem color (getAlias(n)) "")) (!coalescedNodes);
             selectStack:=[])
 
          fun freezeMoves(u) = Splayset.app
              (fn m => let val x = hd(Splayset.listItems(find(def,m)))
                           val y = hd(Splayset.listItems(find(use,m)))
                           val v = if getAlias(y) = getAlias(u) then getAlias(x) else getAlias(y)
                       in (sacaElem activeMoves m;
                           addToSet frozenMoves m;
                           if isEmpty(nodeMoves(v)) andalso findElem degree v k < k then
                              (sacaElem freezeWorklist v;addToSet simplifyWorklist v) else ()) end) (nodeMoves(u))

          fun freeze() =
              let val u =  hd(Splayset.listItems(!freezeWorklist))
              in (sacaElem freezeWorklist u;addToSet simplifyWorklist u;freezeMoves(u)) end

          fun selectSpill()= let val (m,cos) = Splayset.foldl (fn (n,(r,w)) => let val p = findElem spillCost n w
                                                                         in if p < w then (n,p) else (r,w) end) ("",9999999999.0) (!spillWorklist)
                             in (printDbg("Spilled: "^m^"\n");sacaElem spillWorklist m;addToSet simplifyWorklist m;freezeMoves(m)) end

          fun rewriteProgram() =
              let val spill = Splayset.foldl (fn (n,d) => insert(d,n,allocLocal fr true)) (mkDict String.compare) (!spilledNodes)
                  val newTemps = ref(empty String.compare)
                  fun genStore s off =
                      if abs(off) < 4096 then
                         [OPER {assem="str `s0, [`s1,#"^tigercodegen.itoa off^"]\n",src=[s,fp],dst=[],jump=NONE}]
                      else let val n1 = tigertemp.newtemp()
                               val _ = addToSet newTemps n1
                               val (hi,lo) = tigercodegen.divAltaBaja off
                           in [OPER {assem="movw `d0, #"^tigercodegen.itoa lo^"\n",src=[],dst=[n1],jump=NONE},
                               OPER {assem="movt `d0, #"^tigercodegen.itoa hi^"\n",src=[],dst=[n1],jump=NONE},
                               OPER {assem="str, `s0 [`s1,`s2]\n",src=[s,fp,n1],dst=[],jump=NONE}] end

                  fun genLoad d off =
                      if abs(off) < 4096 then
                         [OPER {assem="ldr `d0, [`s0,#"^tigercodegen.itoa off^"]\n",src=[fp],dst=[d],jump=NONE}]
                      else let val n1 = tigertemp.newtemp()
                               val _ = addToSet newTemps n1
                               val (hi,lo) = tigercodegen.divAltaBaja off
                           in [OPER {assem="movw `d0, #"^tigercodegen.itoa lo^"\n",src=[],dst=[n1],jump=NONE},
                               OPER {assem="movt `d0, #"^tigercodegen.itoa hi^"\n",src=[],dst=[n1],jump=NONE},
                               OPER {assem="ldr `d0, [`s0,`s1]\n",src=[fp,n1],dst=[d],jump=NONE}] end

                  fun procDst [] = ([],[])
                    | procDst (d::ds) = (case peek(spill,d) of
                                            NONE => let val (r,s) = procDst ds in (d::r,s) end
                                          | SOME (InFrame acc) =>
                                                        let val t = tigertemp.newtemp()
                                                            val _ = addToSet newTemps t
                                                            val st = genStore t acc
                                                            val (r,s) = procDst ds
                                                        in (t::r,st@s) end
                                          | _ => raise Fail "El allocLocal devolvio cualquiera")

                  fun procSrc [] = ([],[])
                    | procSrc (s::ss) = (case peek(spill,s) of
                                            NONE => let val (r,l) = procSrc ss in (s::r,l) end
                                          | SOME (InFrame acc) =>
                                                        let val t = tigertemp.newtemp()
                                                            val _ = addToSet newTemps t
                                                            val ld = genLoad t acc
                                                            val (r,l) = procSrc ss
                                                        in (t::r,ld@l) end
                                          | _ => raise Fail "El allocLocal devolvio cualquiera")

                  fun reesc [] = []
                    | reesc ((LABEL a)::r) = (LABEL a)::reesc r
                    | reesc ((MOVE {dst,src,assem})::r) =
                                 (case (peek(spill,dst),peek(spill,src)) of
                                       (NONE, NONE) => [MOVE {dst=dst,src=src,assem=assem}]
                                     | (SOME (InFrame ac1), NONE) => genStore src ac1
                                     | (NONE, SOME (InFrame ac2)) => genLoad dst ac2
                                     | (SOME (InFrame ac1), SOME (InFrame ac2)) =>
                                                               let val t1 = tigertemp.newtemp()
                                                                   val _ = addToSet newTemps t1
                                                               in genLoad t1 ac2@genStore t1 ac1 end
                                     | (_,_) => raise Fail "El allocLocal devolvio cualquiera") @reesc r
                    | reesc ((OPER {dst,src,assem,jump})::r) =
                                 let val (nueDst,stores) = procDst dst
                                     val (nueSrc,loads) = procSrc src
                                 in loads@[OPER {assem=assem,dst=nueDst,src=nueSrc,jump=jump}]@stores@reesc r end
                  val nueInstr = reesc bd
              in (inicial := union(!coalescedNodes, union(!newTemps,!coloredNodes));
                  spilledNodes := empty String.compare;
                  coloredNodes := empty String.compare;
                  coalescedNodes := empty String.compare;
                  nueInstr) end

          fun bucle() = (
                        if not(isEmpty(!simplifyWorklist)) then (simplify(); bucle())
                        else if not(isEmpty(!worklistMoves)) then (coalesce(); bucle())
                        else if not(isEmpty(!freezeWorklist)) then (freeze(); bucle())
                        else if not(isEmpty(!spillWorklist)) then (selectSpill(); bucle())
                        else ())

      in (build();
          makeWorkList();
          bucle();
          assignColors();
          if not(isEmpty(!spilledNodes)) then (allocAux(fr,rewriteProgram(),!inicial,flagDebug)) else (!color,bd))
          
end

    fun alloc (fr,bd,flagDebug) =
      let fun sacaRegs (MOVE {src=sc, dst=ds,...}, s) = addList(s,[sc,ds])
            | sacaRegs (OPER {src=sc, dst=ds,...}, s) = addList(s,sc@ds)
            | sacaRegs (LABEL _, s) = s
          val todoTemp = List.foldl sacaRegs (empty String.compare) bd
          val ini = difference(todoTemp, precolored)
          val _ = if flagDebug then print(name(fr)^":\n") else ()
      in allocAux(fr,bd,ini,flagDebug) end

end
