signature tigertopsort =
sig

val fijaTipos : {name: tigerabs.symbol, ty: tigerabs.ty} list -> (string, tigertips.Tipo) tigertab.Tabla -> (string, tigertips.Tipo) tigertab.Tabla

exception Ciclo
end
