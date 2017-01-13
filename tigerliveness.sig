signature tigerliveness =
sig
    datatype igraph = IGRAPH of {graph: tigergraph.graph,
                                 tnode: tigertemp.temp -> tigergraph.node,
                                 gtemp: tigergraph.node -> tigertemp.temp,
                                 moves: (tigergraph.node * tigergraph.node) list}

    val liveMap : tigerflowgraph.flowgraph -> (tigergraph.node -> tigertemp.temp Splayset.set)

    val interferenceGraph : tigerflowgraph.flowgraph -> igraph*(tigergraph.node -> tigertemp.temp list)

    val show : igraph -> unit

end
