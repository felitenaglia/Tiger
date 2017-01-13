signature tigerregister =
sig
    type allocation = (tigertemp.temp, tigerframe.register) Splaymap.dict
    val alloc : tigerframe.frame * tigerassem.instr list * bool -> allocation * tigerassem.instr list
end
