signature tigerflowgraph =
sig
    datatype flowgraph = FGRAPH of {control: tigergraph.graph,
				    def: tigertemp.temp Splayset.set tigergraph.nodeDict,
				    use: tigertemp.temp Splayset.set tigergraph.nodeDict,
				    ismove: bool tigergraph.nodeDict
                                   }

    val flowGraph : tigerassem.instr list -> flowgraph * (tigerassem.instr * tigergraph.node) list
    val flowGraphDebugging : tigerassem.instr list -> flowgraph * (tigerassem.instr * tigergraph.node) list

end
