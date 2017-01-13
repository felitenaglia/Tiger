open tigerlex
open tigergrm
open tigerescap
open tigerseman

open BasicIO Nonstdio

fun lexstream(is: instream) =
	Lexing.createLexer(fn b => fn n => buff_input is b 0 n);
fun errParsing(lbuf) = (print("Error en parsing!("
	^(makestring(!num_linea))^
	")["^(Lexing.getLexeme lbuf)^"]\n"); raise Fail "fin!")
fun main(args) =
	let	fun arg(l, s) =
			(List.exists (fn x => x=s) l, List.filter (fn x => x<>s) l)
		val (arbol, l1)		= arg(args, "-arbol")
		val (escapes, l2)	= arg(l1, "-escapes") 
		val (ir, l3)		= arg(l2, "-ir") 
		val (canon, l4)		= arg(l3, "-canon") 
		val (code, l5)		= arg(l4, "-code") 
		val (inter, l6)		= arg(l5, "-inter")
 		val (interp, l7)	= arg(l6, "-interp")
		val (interdbg, l8)	= arg(l7, "-interpdbg")
                val (regs, l9)		= arg(l8, "-register")
                val (emitAsm, l10)	= arg(l9, "-S")
                val (crossComp, l11)	= arg(l10, "-cc")
		val (entrada,binName) =
			case l11 of
			[n] => (((open_in n), n)
					handle _ => raise Fail (n^" no existe!"))
			| [] => (std_in, "stdin")
			| _ => raise Fail "opcio'n dsconocida!"
		val lexbuf = lexstream entrada
		val expr = prog Tok lexbuf handle _ => errParsing lexbuf
		val _ = findEscape(expr)
		val _ = if arbol then tigerpp.exprAst expr else ()
		val _ = transProg(expr)
		val fragmentos = tigertrans.getResult()
		val _ = if ir then print(tigertrans.Ir(fragmentos)) else ()

		val fcCanon = (tigercanon.traceSchedule o tigercanon.basicBlocks o tigercanon.linearize)

		(* Divide los fragmentos y canoniza los que son PROC *)
		fun divideFrags [] = ([],[])
		  | divideFrags (tigerframe.PROC {body,frame} :: t) = let val (stm,str) = divideFrags t in ((frame,fcCanon body)::stm,str) end
		  | divideFrags (tigerframe.STRING s :: t) = let val (stm,str) = divideFrags t in (stm,s::str) end

		val (canonizado, roData) = divideFrags fragmentos

		val _ = if canon then List.app (fn (f,b) => (print((tigerframe.name f)^":\n");List.app (print o tigerit.tree) b)) canonizado else ()

		val _ = if interp orelse interdbg then tigerinterp.inter interdbg canonizado roData else ()

                (* map que emite código, aplana la lista y le aplica procEntryExit2 *)
		val codAsem = map (fn (f,b) => (f,tigerframe.procEntryExit2(f,List.concat(map (tigercodegen.codegen f) b)))) canonizado

		val _ = if code then List.app (fn (f,b) => (print(tigerframe.name f^":\n");
                                                            List.app print (map (tigerassem.format (fn x => x)) b))) codAsem
                                else ()
		val enregistrado = map (fn (f,b) => (f,tigerregister.alloc(f,b,regs))) codAsem


                val tempFileAsm = FileSys.tmpName()^".s"
		val outAssem = (TextIO.openOut (tempFileAsm))
                                         handle _ => raise Fail "Falló al abrir el archivo de salida"
                fun printArchivo s = TextIO.output(outAssem,s)

		fun imprCodigo say {prolog: string, body: tigerassem.instr list, epilog: string} =
                    (printArchivo prolog;
                     List.app printArchivo (map (tigerassem.format say) body);
                     printArchivo epilog)
		fun imprROData (lab,st) = (if lab <> "" then printArchivo(lab^":\n") else (); printArchivo("\t"^st^"\n"))


                val _ = printArchivo("\t.section .rodata\n")
                val _ = List.app imprROData roData;
                val _ = printArchivo("\t.text\n");
                val _ = List.app (fn (f,(mp,bd)) => imprCodigo (fn r => Splaymap.find(mp,r)) (tigerframe.procEntryExit3(f,bd))) enregistrado
                val _ = TextIO.closeOut(outAssem)

                (* Si -S esta activado, no ensambla ni linkea *)
                val st = if emitAsm then Process.success
                                    else
                                    if crossComp then Process.system("arm-linux-gnueabi-gcc -marm -mfloat-abi=softfp -march=armv7-a -mfpu=vfpv3-d16 -g runtime.c "^tempFileAsm^" -o "^binName^".out")
                                                 else Process.system("gcc -marm -g runtime.c "^tempFileAsm^" -o "^binName^".out")

                (* Si -S esta activado, copia el .s desde /tmp *)
                val _ = if emitAsm then (Process.system("cp "^tempFileAsm^" "^binName^".s");()) else ()
                (* Borra el archivo temporario *)
                val _ = Process.system("rm "^tempFileAsm)
                (* Falla si gcc falló *)
                val _ = if Process.isSuccess(st) then () else raise Fail "Falló al ensamblar"
	in
		print "yes!!\n"
	end	handle Fail s => print("Fail: "^s^"\n")

val _ = main(CommandLine.arguments())
