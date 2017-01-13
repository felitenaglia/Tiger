structure tigerassem = struct

  type reg = string
  type temp = tigertemp.temp
  type label = tigertemp.label

  datatype instr = OPER of {assem: string,
			    dst: temp list,
			    src: temp list,
			    jump: label list option}
                 | LABEL of {assem: string, lab: tigertemp.label}
                 | MOVE of {assem: string, 
			    dst: temp,
			    src: temp}

  fun format saytemp =
    let 
	fun speak(assem,dst,src,jump) =
	    let fun saylab s = s
		fun f(#"`":: #"s":: i::rest) = 
		    (explode(saytemp(List.nth(src,ord i - ord #"0"))) @ f rest)
		  | f( #"`":: #"d":: i:: rest) = 
		    (explode(saytemp(List.nth(dst,ord i - ord #"0"))) @ f rest)
		  | f( #"`":: #"j":: i:: rest) = 
		    (explode(saylab(List.nth(jump,ord i - ord #"0"))) @ f rest)
		  | f( #"`":: #"`":: rest) = #"`" :: f rest
		  | f( #"`":: _ :: rest) = raise Fail "bad Assem format"
		  | f(c :: rest) = (c :: f rest)
		  | f nil = nil
	    in implode(f(explode assem))
	    end
      in fn OPER{assem,dst,src,jump=NONE} => "\t"^speak(assem,dst,src,nil)
          | OPER{assem,dst,src,jump=SOME j} => "\t"^speak(assem,dst,src,j)
	  | LABEL{assem,...} => assem
	  | MOVE{assem,dst,src} => if ((saytemp dst) = (saytemp src)) then "" else "\t"^speak(assem,[dst],[src],nil)
     end

  fun assemToString (OPER {assem,dst,src,jump=NONE}) = "OPER: "^assem^" D:["^(String.concatWith "," dst)^"] S:["^(String.concatWith "," src)^"]\n"
    | assemToString (OPER {assem,dst,src,jump=SOME j}) = "OPER: "^assem^" D:["^(String.concatWith "," dst)^"] S:["^(String.concatWith "," src)^"] J:["^(String.concatWith "," j)^"]\n"
    | assemToString (MOVE {assem,dst,src}) = "MOVE: "^assem^" D:"^dst^" S:"^src^"\n"
    | assemToString (LABEL {lab,...}) = "LABEL: "^lab^"\n"

end

