(*

|    argn    |	fp+4*n
|    ...     |
|    arg2    |	fp+8
|    arg1    |	fp+4
|   fp ant   |  fp
|   local1   |	fp-4
|   local2   |	fp-8
|    ...     |
|   localn   |	fp-4*n
*)

structure tigerframe :> tigerframe = struct

open tigertree

type level = int

val fp = "fp"				(* frame pointer *)
val sp = "sp" (*SP*)				(* stack pointer *)
val rv = "r0" (*RV*)				(* return value  *)
val ov = "OV"				(* overflow value (edx en el 386) *)
val wSz = 4					(* word size in bytes *)
val log2WSz = 2				(* base two logarithm of word size in bytes *)
val fpPrev = 0				(* offset (bytes) *)
val fpPrevLev = ~4		(* 8 *)	(* offset (bytes) *)
val argsInicial = 0			(* words *)
val argsOffInicial = 1		(* 2 *) (* words *)
val argsGap = wSz			(* bytes *)
val regInicial = 1			(* reg *)
val localsInicial = ~2		(* words *)
val localsGap = ~4 			(* bytes *)
val registers = ["r0","r1","r2","r3","r4","r5","r6","r7","r8","r9","r10","lr","sp","fp"]
val calldefs = [rv,"r1","r2","r3","lr"]
val specialregs = [rv, fp, sp]
val argregs = ["r0","r1","r2","r3"]
val callersaves = []
val calleesaves = ["r4","r5","r6","r7","r8","r9","r10","lr"]
val cantArgReg = length argregs

datatype access = InFrame of int | InReg of tigertemp.label

type frame = {
	name: string,
	formals: bool list,
	locals: bool list,
	actualArg: int ref,
	actualLocal: int ref,
	actualReg: int ref,
	ftAccesos : access list ref
}
type register = string

datatype frag = PROC of {body: tigertree.stm, frame: frame}
	| STRING of tigertemp.label * string
fun newFrame{name, formals} = {
	name=name,
	formals=true::formals,
	locals=[],
	actualArg=ref argsInicial,
	actualLocal=ref localsInicial,
	actualReg=ref regInicial,
    ftAccesos = ref [InFrame(fpPrevLev)]
}
fun name(f: frame) = #name f
fun string(l, s) = l^tigertemp.makeString(s)^"\n"
(* fun formals({ftAccesos=fta,...}: frame) = !fta *)
fun formals({formals=f,...}:frame) = let fun armaAccesos [] _ n = []
                                       | armaAccesos (_::xs) [] n = (InFrame (n*wSz))::armaAccesos xs [] (n+1)
                                       | armaAccesos (_::xs) (r::rs) n = (InReg r)::armaAccesos xs rs n
                                     in armaAccesos f argregs argsOffInicial end

fun allocArg (f: frame) b = 
        if !(#actualReg f) < cantArgReg then
              if b then
		           let val ret = (!(#actualLocal f)*wSz)
                       val _ = (#ftAccesos f) := (!(#ftAccesos f) @ [InFrame ret])
                       val _ = (#actualReg f) := (!(#actualReg f)+1)
                       val _ = (#actualLocal f) := (!(#actualLocal f)-1)
		           in InFrame ret end                   
              else let val tmp = tigertemp.newtemp()
                       val _ = (#ftAccesos f) := (!(#ftAccesos f) @ [InReg tmp])
                       val _ = (#actualReg f) := (!(#actualReg f)+1)
                   in InReg tmp end
        else let val ret = (!(#actualArg f)+argsOffInicial)*wSz
                 val _ = #actualArg f := !(#actualArg f)+1
                 val _ = (#ftAccesos f) := (!(#ftAccesos f) @ [InFrame ret])
             in InFrame ret end

fun allocLocal (f: frame) b = 
	case b of
	true =>
		let	val ret = InFrame(!(#actualLocal f)*wSz)
		in	#actualLocal f:=(!(#actualLocal f)-1); ret end
	| false => InReg(tigertemp.newtemp())

fun exp(InFrame k) e = MEM(BINOP(PLUS, TEMP(fp), CONST k))
| exp(InReg l) e = TEMP l
fun externalCall(s, l) = ESEQ(EXP(CALL(NAME s, l)),TEMP rv)

fun recorreArgs [] _ = []
  | recorreArgs _ [] = []
  | recorreArgs ((InReg t) :: xs) (reg::regs) = MOVE(TEMP t, TEMP reg) :: recorreArgs xs regs
  | recorreArgs ((InFrame k)::xs) (reg::regs) = MOVE(MEM(BINOP(PLUS, TEMP fp ,CONST k)), TEMP reg) :: recorreArgs xs regs

fun seq [] = EXP (CONST 0)
	| seq [s] = s
	| seq (x::xs) = SEQ (x, seq xs)

fun procEntryExit1 (fr : frame,body) = let val (entry,exit) = List.foldl 
                                                (fn (r,(ent,exi)) => let val nt = tigertemp.newtemp()
                                                                     in (MOVE (TEMP nt, TEMP r)::ent,MOVE (TEMP r, TEMP nt)::exi) end ) ([],[]) calleesaves
                                           val acomodaArgs = rev(recorreArgs (!(#ftAccesos fr)) argregs)
					   (*val bajaStack = wSz*(abs(!(#actualLocal fr))-1)*)
					   (*val acomoda = (MOVE (TEMP sp, (BINOP(MINUS,TEMP sp,CONST bajaStack))))::acomodaArgs*)
                                             val acomoda = (MOVE (TEMP sp, (BINOP(MINUS,TEMP sp, MEM(NAME (#name fr^"_fs"))))))::acomodaArgs
                                  in seq(entry@acomoda@[body]@exit) end

fun procEntryExit2 (fr : frame, body:tigerassem.instr list) = body@[tigerassem.OPER{assem="\n",src=rv::sp::calleesaves,dst=[] ,jump = NONE}]

fun procEntryExit3 (fr : frame, body) = {prolog="\t.global "^(#name fr)^"\n"
                                               ^(#name fr)^"_fs:\n"
                                               ^"\t.long "^makestring(wSz*(abs(!(#actualLocal fr))-1))^"\n"
                                               ^(#name fr)^":\n"
                                               ^"\tstmfd sp!, {fp}\n"
                                               ^"\tmov fp, sp\n",
                                         body=body,
                                         epilog="\tmov sp, fp\n"
                                               ^"\tldmfd sp!, {fp}\n"
                                               ^"\tbx lr\n"}
end
