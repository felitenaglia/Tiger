structure tigercodegen :> tigercodegen = 
struct

open tigerassem
open tigertree
open tigerframe

val wrdHi64 = valOf(Word.fromString("FFFFFFFF00000000"))
val wrd1s = valOf(Word.fromString("FFFFFFFF"))
val wrd0 = Word.fromInt(0)
val wrd3 = Word.fromInt(3)
val wrd2 = Word.fromInt(2)
val wrd30 = Word.fromInt(30)
val wrd255 = Word.fromInt(255)
val maskHi = valOf(Word.fromString("FFFF0000"))
val maskLo = valOf(Word.fromString("FFFF"))

(* Hace fuerza bruta para ver si el número se puede expresar como 8bits+rotacion
   Tambien verifica que el entero sea de 32 bits.
   El 'b' como argumento dice si hay que verificar tambien el complemento a 1 *)
fun esReducible n b = let val wrdControl = Word.andb(Word.fromInt(n), wrdHi64)
                          val wrdN = Word.andb(Word.fromInt(n), wrd1s)
                          fun rota2bits w = let val baja = Word.<<(Word.andb(w,wrd3),wrd30)
                                            in Word.andb(Word.orb(Word.>>(w,wrd2),baja),wrd1s) end
                          fun esRed _ 16 = false
                            | esRed w m = Word.<=(w,wrd255) orelse esRed (rota2bits w) (m+1)
                      in if wrdControl = wrdHi64 orelse wrdControl = wrd0
                         then (esRed wrdN 0) orelse (b andalso esRed (Word.xorb(wrdN,wrd1s)) 0)
                         else (print("Warning: la constante "^makestring n^" es mas larga que una palabra\n");false)
                      end

fun divAltaBaja n = let val wN = Word.fromInt(n)
                    in (Word.toInt(Word.>>(Word.andb(maskHi, wN), Word.fromInt(16))),Word.toInt(Word.andb(maskLo, wN))) end

fun branchStr EQ = "beq"
  | branchStr NE = "bne"
  | branchStr LT = "blt"
  | branchStr GT = "bgt"
  | branchStr LE = "ble"
  | branchStr GE = "bge"
  | branchStr ULT = "bcc"
  | branchStr ULE = "bls"
  | branchStr UGT = "bhi"
  | branchStr UGE = "bcs"

fun binOp PLUS x y = x+y
  | binOp MINUS x y = x-y
  | binOp MUL x y = x*y
  | binOp DIV x 0 = raise Fail "División por cero, pero no deberia aparecer" (* No deberia aparecer porque en munchExp hay un pattern aparte *)
  | binOp DIV x y = x div y
  | binOp AND x y = Word.toInt(Word.andb(Word.fromInt(x), Word.fromInt(y)))
  | binOp OR x y = Word.toInt(Word.orb(Word.fromInt(x), Word.fromInt(y)))
  | binOp LSHIFT x y = Word.toInt(Word.<<(Word.fromInt(x), Word.fromInt(y)))
  | binOp RSHIFT x y = Word.toInt(Word.>>(Word.fromInt(x), Word.fromInt(y)))
  | binOp ARSHIFT x y = Word.toInt(Word.~>>(Word.fromInt(x), Word.fromInt(y)))
  | binOp XOR x y = Word.toInt(Word.xorb(Word.fromInt(x), Word.fromInt(y)))

fun itoa i = let val str = Int.toString(abs(i)) in if i<0 then "-"^str else str end

fun codegen frame stm =
    let val ilist = ref [] : instr list ref
        fun emit x = ilist := x :: !ilist
        and result gen = let val t = tigertemp.newtemp() in gen t; t end

        and munchStm (SEQ (a,b)) = (munchStm a; munchStm b)

          | munchStm (LABEL l) =
                   emit(tigerassem.LABEL{assem=l^":\n", lab=l})

          | munchStm (MOVE(TEMP d,TEMP s)) =
                   emit(tigerassem.MOVE {assem="mov `d0, `s0\n",src=s,dst=d})
          | munchStm (MOVE(TEMP d,CONST i)) =
                   if esReducible i true then
                        emit(OPER {assem="mov `d0, #"^ itoa i ^"\n",src=[],dst=[d],jump=NONE})
                   else let val (hi,lo) = divAltaBaja i
                        in emit(OPER {assem="movw `d0, #"^ itoa lo ^"\n\tmovt `d0, "^ itoa hi ^"\n",src=[],dst=[d],jump=NONE}) end

         | munchStm (MOVE(TEMP d,MEM(BINOP(PLUS, e1, BINOP (LSHIFT, e2, CONST i)  )))) =
                   if i>0 then
                         emit(OPER {assem="ldr `d0, [`s0, `s1, LSL #"^itoa (Int.min(i,31))^"]\n",src=[munchExp e1, munchExp e2],dst=[d],jump=NONE})
                   else 
                         emit(OPER {assem="ldr `d0, [`s0, `s1, ASR #"^itoa (Int.min(~i,31))^"]\n",src=[munchExp e1, munchExp e2],dst=[d],jump=NONE})

          | munchStm (MOVE(TEMP d,MEM(BINOP(PLUS, TEMP t, CONST i)))) =
                   if abs(i) < 4096 then
                         emit(OPER {assem="ldr `d0, [`s0, #"^itoa i^"]\n",src=[t],dst=[d],jump=NONE})
                   else
                         emit(OPER {assem="ldr `d0, [`s0, `s1]\n",src=[t, munchExp (CONST i)],dst=[d],jump=NONE})
          | munchStm (MOVE(TEMP d,MEM(BINOP(PLUS, e, CONST i)))) =
                   if abs(i) < 4096 then
                         emit(OPER {assem="ldr `d0, [`s0, #"^itoa i^"]\n",src=[munchExp e],dst=[d],jump=NONE})
                   else
                         emit(OPER {assem="ldr `d0, [`s0, `s1]\n",src=[munchExp e, munchExp (CONST i)],dst=[d],jump=NONE})


          | munchStm (MOVE(TEMP d,MEM(BINOP(PLUS, e1, e2)))) =
                   emit(OPER {assem="ldr `d0, [`s0, `s1]\n",src=[munchExp e1, munchExp e2],dst=[d],jump=NONE})
          | munchStm (MOVE(TEMP d, MEM e)) =
                      emit(OPER {assem="ldr `d0, [`s0]\n",src=[munchExp e],dst=[d],jump=NONE})
          | munchStm (MOVE(TEMP d, e)) =
                      emit(tigerassem.MOVE {assem="mov `d0, `s0\n",src=munchExp e,dst=d})

          | munchStm (MOVE(MEM(BINOP(PLUS, e1, BINOP (LSHIFT, e2, CONST i))), e)) =
                   if i>0 then
                         emit(OPER {assem="str `s0, [`s1, `s2, LSL #"^itoa (Int.min(i,31))^"]\n",src=[munchExp e, munchExp e1, munchExp e2],dst=[],jump=NONE})
                   else 
                         emit(OPER {assem="str `s0, [`s1, `s2, ASR #"^itoa (Int.min(~i,31))^"]\n",src=[munchExp e, munchExp e1, munchExp e2],dst=[],jump=NONE})

          | munchStm (MOVE(MEM (BINOP(PLUS,TEMP t, CONST i)), e)) =
                   if abs(i) < 4096 then
                         emit(OPER {assem="str `s0, [`s1, #"^itoa i^"]\n",src=[munchExp e, t],dst=[],jump=NONE})
                   else
                         emit(OPER {assem="str `s0, [`s1, `s2]\n",src=[munchExp e, t, munchExp (CONST i)],dst=[],jump=NONE})
          | munchStm (MOVE(MEM (BINOP(PLUS,e1, CONST i)), e2)) =
                   if abs(i) < 4096 then
                         emit(OPER {assem="str `s0, [`s1, #"^itoa i^"]\n",src=[munchExp e2, munchExp e1],dst=[],jump=NONE})
                   else
                         emit(OPER {assem="str `s0, [`s1, `s2]\n",src=[munchExp e2, munchExp e1, munchExp (CONST i)],dst=[],jump=NONE})
          | munchStm (MOVE(MEM (BINOP(PLUS,e1, e2)), e3)) =
                   emit(OPER {assem="str `s0, [`s1, `s2]\n",src=[munchExp e3, munchExp e1, munchExp e2],dst=[],jump=NONE})
          | munchStm (MOVE(MEM e1, e2)) =
                      emit(OPER {assem="str `s0, [`s1]\n",src=[munchExp e2, munchExp e1],dst=[],jump=NONE})
          | munchStm (MOVE(d,s)) = raise Fail ("Cayó en el caso general del MOVE, no debería. Código:\n "^tigerit.tree (MOVE(d,s)))


          | munchStm (EXP (CALL ((NAME e),args))) = (saveCallerSaves();
                                                     emit(OPER{assem="bl "^e^"\n",src = munchArgs args argregs, dst=calldefs,jump=NONE});
                                                     if length args - length argregs > 0 then
                                                        let val stackOff = (length args - length argregs)*wSz
                                                            val (strConst,temps) = 
                                                                if esReducible stackOff true then ("#"^itoa stackOff,[])
                                                                else let val (hi,lo) = divAltaBaja stackOff
                                                                     in ("`s1",[result(fn r => emit(OPER {assem="movw `d0, #"^ itoa lo ^"\n\tmovt `d0, "^ itoa hi ^"\n",src=[],dst=[r],jump=NONE}))]) end
                                                        in emit(OPER{assem="add `d0, `s0, "^strConst^"\n",src=sp::temps,dst=[sp],jump=NONE})
                                                        end
                                                     else ();
                                                     restoreCallerSaves())
          | munchStm (EXP (CALL _)) =raise Fail "Call en algo que no es NAME"
          | munchStm (EXP e) = (munchExp e; ())


          | munchStm (JUMP (NAME l,_)) =
                   emit(OPER {assem="b "^l^"\n",src=[],dst=[],jump=SOME [l]})
          | munchStm (JUMP _) = raise Fail "Jump no implementado ¿Pasara alguna vez?. Si apareció esto sí..."


          | munchStm (CJUMP (rel,CONST x,CONST y,tr,fl)) =
                   let val res = case rel of
                                   EQ => x = y
                                 | NE => x <> y
                                 | LT => x < y
                                 | GT => x > y
                                 | LE => x <= y
                                 | GE => x >= y
                                 | ULT => Word.<(Word.fromInt(x),Word.fromInt(x))
                                 | ULE => Word.<=(Word.fromInt(x),Word.fromInt(x))
                                 | UGT => Word.>(Word.fromInt(x),Word.fromInt(x))
                                 | UGE => Word.>=(Word.fromInt(x),Word.fromInt(x))
                       val l = if res then tr else fl
                   in emit(OPER {assem="b "^l^"\n",src=[],dst=[],jump=SOME [l] })
                   end
          | munchStm (CJUMP (rel,e,CONST x,tr,fl)) =
                   let val (strConst,temps) = 
                             if esReducible x true then ("#"^itoa x,[])
                             else let val (hi,lo) = divAltaBaja x
                                  in ("`s1",[result(fn r => emit(OPER {assem="movw `d0, #"^ itoa lo ^"\n\tmovt `d0, "^ itoa hi ^"\n",src=[],dst=[r],jump=NONE}))]) end 
                       val _ = emit(OPER {assem="cmp `s0, "^strConst^"\n",src=[munchExp e]@temps,dst=[],jump=NONE})
                   in emit(OPER {assem=branchStr rel^" "^tr^"\n",src=[],dst=[],jump=SOME [tr,fl] })
                   end
          | munchStm (CJUMP (rel,e1,e2,tr,fl)) =
                   let val _ = emit(OPER {assem="cmp `s0, `s1\n",src=[munchExp e1, munchExp e2],dst=[],jump=NONE})
                   in emit(OPER {assem=branchStr rel^" "^tr^"\n",src=[],dst=[],jump=SOME [tr,fl] })
                   end


        and munchExp (TEMP t) = t

          | munchExp (NAME l) =
                   result(fn r => emit(OPER {assem="movw `d0, #:lower16:"^l^"\n\tmovt `d0, #:upper16:"^l^"\n",src=[],dst=[r],jump=NONE}))

          | munchExp (CONST i) = 
                   if esReducible i true then
                        result(fn r => emit(OPER {assem="mov `d0, #"^ itoa i ^"\n",src=[],dst=[r],jump=NONE}))
                   else let val (hi,lo) = divAltaBaja i
                        in result(fn r => emit(OPER {assem="movw `d0, #"^ itoa lo ^"\n\tmovt `d0, "^ itoa hi ^"\n",src=[],dst=[r],jump=NONE})) end


         | munchExp (MEM(BINOP(PLUS, e1, BINOP (LSHIFT, e2, CONST i)))) =
                   if i>0 then
                         result(fn r => emit(OPER {assem="ldr `d0, [`s0, `s1, LSL #"^itoa (Int.min(i,31))^"]\n",src=[munchExp e1, munchExp e2],dst=[r],jump=NONE}))
                   else 
                         result(fn r => emit(OPER {assem="ldr `d0, [`s0, `s1, ASR #"^itoa (Int.min(~i,31))^"]\n",src=[munchExp e1, munchExp e2],dst=[r],jump=NONE}))

          | munchExp (MEM (BINOP(PLUS,e,CONST x))) =
                   if abs(x) < 4096 then
                         result(fn r => emit(OPER {assem="ldr `d0, [`s0, #"^itoa x^"]\n",src=[munchExp e],dst=[r],jump=NONE}))
                   else
                         result(fn r => emit(OPER {assem="ldr `d0, [`s0, `s1]\n",src=[munchExp e, munchExp (CONST x)],dst=[r],jump=NONE}))

          | munchExp (MEM (BINOP(PLUS,e1,e2))) =
                   result(fn r => emit(OPER {assem="ldr `d0, [`s0, `s1]\n",src=[munchExp e1, munchExp e2],dst=[r],jump=NONE}))

          | munchExp (MEM e) =
                   result(fn r => emit(OPER {assem="ldr `d0, [`s0]\n",src=[munchExp e],dst=[r],jump=NONE}))

          | munchExp (BINOP (DIV, x, y)) =
                   result(fn r => (munchStm (EXP (CALL ((NAME "__aeabi_idiv"),[x,y])));
                                   emit(tigerassem.MOVE {assem="mov `d0, `s0\n",src=rv,dst=r})))

          | munchExp (BINOP (oper,CONST x,CONST y)) = 
                   let val i = binOp oper x y
                   in 
                   if esReducible i true then
                         result(fn r => emit(OPER {assem="mov `d0, #"^ itoa i ^"\n",src=[],dst=[r],jump=NONE}))
                   else let val (hi,lo) = divAltaBaja i
                        in result(fn r => emit(OPER {assem="movw `d0, #"^ itoa lo ^"\n\tmovt `d0, "^ itoa hi ^"\n",src=[],dst=[r],jump=NONE})) end
                   end

          | munchExp (BINOP (MINUS,CONST x,e)) =
                   if esReducible x false then
                        result(fn r => emit(OPER {assem="rsb `d0, `s0, #"^ itoa x ^"\n",src=[munchExp e],dst=[r],jump=NONE}))
                   else let val (hi,lo) = divAltaBaja x
                            val tmp = tigertemp.newtemp()
                        in emit(OPER {assem="movw `d0, #"^ itoa lo ^"\n\tmovt `d0, "^ itoa hi ^"\n",src=[],dst=[tmp],jump=NONE});
                           result(fn r => emit(OPER {assem="sub `d0, `s0, `s1\n",src=[tmp, munchExp e],dst=[r],jump=NONE})) end

	  (* A estos casos los puse aparte porque hay que restringir a los shift *)
          | munchExp (BINOP (LSHIFT,e,CONST x)) =
                   if x < 0 then result(fn r => emit(OPER {assem="asr `d0, `s0, #"^itoa (Int.min(~x,31))^"\n",src=[munchExp e],dst=[r],jump=NONE}))
                            else result(fn r => emit(OPER {assem="lsl `d0, `s0, #"^itoa (Int.min(x,31))^"\n",src=[munchExp e],dst=[r],jump=NONE}))
          | munchExp (BINOP (RSHIFT,e,CONST x)) =
                   if x < 0 then result(fn r => emit(OPER {assem="lsl `d0, `s0, #"^itoa (Int.min(~x,31))^"\n",src=[munchExp e],dst=[r],jump=NONE}))
                            else result(fn r => emit(OPER {assem="lsr `d0, `s0, #"^itoa (Int.min(x,31))^"\n",src=[munchExp e],dst=[r],jump=NONE}))
          | munchExp (BINOP (ARSHIFT,e,CONST x)) =
                   if x < 0 then result(fn r => emit(OPER {assem="lsl `d0, `s0, #"^itoa (Int.min(~x,31))^"\n",src=[munchExp e],dst=[r],jump=NONE}))
                            else result(fn r => emit(OPER {assem="asr `d0, `s0, #"^itoa (Int.min(x,31))^"\n",src=[munchExp e],dst=[r],jump=NONE}))

          | munchExp (BINOP (MUL,e,CONST x)) =
                   result(fn r => emit(OPER {assem="mul `d0, `s0, `s1\n",src=[munchExp e, munchExp (CONST x)],dst=[r],jump=NONE}))

          | munchExp (BINOP (oper,e,CONST x)) =
                   let val (strConst,temps) = 
                             if esReducible x true then ("#"^itoa x,[])
                             else let val (hi,lo) = divAltaBaja x
                                  in ("`s1",[result(fn r => emit(OPER {assem="movw `d0, #"^ itoa lo ^"\n\tmovt `d0, "^ itoa hi ^"\n",src=[],dst=[r],jump=NONE}))]) end
                       fun genAssem PLUS = "add `d0, `s0, "^strConst^"\n"
                         | genAssem MINUS = "sub `d0, `s0, "^strConst^"\n"
                         | genAssem AND = "and `d0, `s0, "^strConst^"\n"
                         | genAssem OR = "orr `d0, `s0, "^strConst^"\n"
                         | genAssem XOR = "eor `d0, `s0, "^strConst^"\n"
                         | genAssem _ = raise Fail "Tiene pattern propio, no deberia aparecer"
                   in result(fn r => emit(OPER {assem=genAssem oper,src=[munchExp e]@temps,dst=[r],jump=NONE})) end


          (* Casos generales *)
          | munchExp (BINOP (oper,e1,e2)) =
                   let fun genAssem PLUS = "add `d0, `s0, `s1\n"
                         | genAssem MINUS = "sub `d0, `s0, `s1\n"
                         | genAssem MUL = "mul `d0, `s0, `s1\n"
                         | genAssem DIV = raise Fail "Tiene pattern propio, no deberia aparecer"
                         | genAssem AND = "and `d0, `s0, `s1\n"
                         | genAssem OR = "orr `d0, `s0, `s1\n"
                         | genAssem LSHIFT = "lsl `d0, `s0, `s1\n"
                         | genAssem RSHIFT = "lsr `d0, `s0, `s1\n"
                         | genAssem ARSHIFT = "asr `d0, `s0, `s1\n"
                         | genAssem XOR = "eor `d0, `s0, `s1\n"
                   in result(fn r => emit(OPER {assem=genAssem oper,src=[munchExp e1, munchExp e2],dst=[r],jump=NONE})) end

          | munchExp (ESEQ _) = raise Fail "Sin canonizar!"

          | munchExp (CALL _) = (* Este caso creo que no pasa nunca. Pattern en munchStm : EXP(CALL...) *)
                   raise Fail "Call en munchExp"

        and srcList 0 _ = ""
          | srcList 1 off = "`s"^makestring off
          | srcList n off = (srcList (n-1) off) ^ ", `s"^makestring (n-1+off)

        and dstList 0 _ = ""
          | dstList 1 off = "`d"^makestring off
          | dstList n off = (srcList (n-1) off) ^ ", `d"^makestring (n-1+off)

        and saveCallerSaves() = if callersaves <> [] then emit(OPER {assem="stmfd `d0!, {"^(srcList (length callersaves) 0)^"}\n",dst=[sp],src=callersaves,jump=NONE}) else ()

        and restoreCallerSaves() = if callersaves <> [] then emit(OPER {assem="ldmfd `d0!, {"^(dstList (length callersaves) 1)^"}\n",src=[],dst=sp::callersaves,jump=NONE}) else ()

        and munchArgs [] _ = []
          | munchArgs l [] =
                      let fun aStack [] = []
                            | aStack (x::xs) =
                                let val (instr, e) = 
                                       case x of
                                          TEMP t => (OPER{assem="str `s0, [`s1, #-4]!\n",src=[t,sp],dst=[],jump=NONE},[])
                                        | e => let val tmp = munchExp e
                                               in (OPER {assem="str `s0, [`s1, #-4]!\n",src=[tmp,sp],dst=[],jump=NONE}, [tmp]) end
                                in emit instr;e@aStack xs end 
                      in aStack (rev l) end
          | munchArgs (h::t) (reg::regs) = 
                      let val (instr, e) = 
                               case h of
                                  CONST i => if esReducible i true then
                                                 (OPER {assem="mov `d0, #"^ itoa i ^"\n",src=[],dst=[reg],jump=NONE},reg)
                                             else let val (hi,lo) = divAltaBaja i
                                                  in (OPER {assem="movw `d0, #"^ itoa lo ^"\n\tmovt `d0, "^ itoa hi ^"\n",src=[],dst=[reg],jump=NONE},reg) end
                                | NAME l => (OPER {assem="movw `d0, #:lower16:"^l^"\n\tmovt `d0, #:upper16:"^l^"\n",src=[],dst=[reg],jump=NONE},reg)
                                | TEMP t => (tigerassem.MOVE {assem="mov `d0, `s0\n",src=t,dst=reg},reg)
                                | MEM(BINOP(PLUS, e, CONST i)) =>
                                     if abs(i) < 4096 then
                                           (OPER {assem="ldr `d0, [`s0, #"^itoa i^"]\n",src=[munchExp e],dst=[reg],jump=NONE},reg)
                                     else
                                           (OPER {assem="ldr `d0, [`s0, `s1]\n",src=[munchExp e, munchExp (CONST i)],dst=[reg],jump=NONE},reg)

                                | MEM e => (OPER {assem="ldr `d0, [`s0]\n",src=[munchExp e],dst=[reg],jump=NONE},reg)
                                | e => (tigerassem.MOVE {assem="mov `d0, `s0\n",src=munchExp e,dst=reg}, reg)
                      in emit instr; e::munchArgs t regs end
                                        
    in munchStm stm;
        rev(!ilist)
    end
end
