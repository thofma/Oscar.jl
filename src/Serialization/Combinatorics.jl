using JSON

###############################################################################
## Graphs
###############################################################################
@register_serialization_type Graph{Directed} "Graph{Directed}"
@register_serialization_type Graph{Undirected} "Graph{Undirected}"

function save_object(s::SerializerState, g::Graph{T}) where T <: Union{Directed, Undirected}
  smallobject = pm_object(g)
  serialized = Polymake.call_function(Symbol("Core::Serializer"), :serialize, smallobject)
  jsonstr = Polymake.call_function(:common, :encode_json, serialized)
  save_data_json(s, jsonstr)
end


function load_object(s::DeserializerState, g::Type{Graph{T}}, dict::Dict) where T <: Union{Directed, Undirected}
  smallobj = Polymake.call_function(:common, :deserialize_json_string, json(dict))
  return g(smallobj)
end

###############################################################################
## IncidenceMatrix
###############################################################################
@register_serialization_type Polymake.IncidenceMatrixAllocated{Polymake.NonSymmetric}

function save_object(s::SerializerState, IM::IncidenceMatrix)
  serialized = Polymake.call_function(Symbol("Core::Serializer"), :serialize, IM)
  jsonstr = Polymake.call_function(:common, :encode_json, serialized)
  save_data_json(s, jsonstr)
end

function load_object(s::DeserializerState, ::Type{<: IncidenceMatrix}, dict::Dict)
  IM = Polymake.call_function(:common, :deserialize_json_string, json(dict))
  return IM
end


###############################################################################
## SimplicialComplex
###############################################################################
@register_serialization_type SimplicialComplex

function save_object(s::SerializerState, K::SimplicialComplex)
  save_object(s, pm_object(K))
end

function load_object(s::DeserializerState, K::Type{SimplicialComplex}, dict::Dict)
  bigobject = Polymake.call_function(:common, :deserialize_json_string, json(dict))
  return K(bigobject)
end

###############################################################################
## Phylogenetic Trees
###############################################################################
@register_serialization_type PhylogeneticTree 

function save_object(s::SerializerState, PT::PhylogeneticTree)
  save_object(s, pm_object(PT))
end

function load_object(s::DeserializerState, T::Type{PhylogeneticTree}, dict::Dict)
  bigobject = Polymake.call_function(:common, :deserialize_json_string, json(dict))
  return T(bigobject)
end
