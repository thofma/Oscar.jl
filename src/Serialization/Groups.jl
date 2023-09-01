
# Cache families of GAP objects that have been serialized,
# in order to be able to deserialize the objects in the *same* GAP session,
# and to get equal objects.
# If deserialization takes place in a *different* GAP session then
# we have to create the families in question anew.

const _GAP_Families = Dict{String, Dict{String, GapObj}}()
const _GAP_session_id = Ref{String}("")

function __init_group_serialization()
  _GAP_session_id[] = string(objectid(GAP))
  _GAP_Families[_GAP_session_id[]] = Dict{UInt64, GapObj}()
end


################################################################################
# PermGroup

@register_serialization_type PermGroup uses_id

function save_object(s::SerializerState, G::PermGroup)
  n = degree(G)
  generators = [Vector{Int}(GAP.Globals.ListPerm(x.X)) for x in gens(G)]

  save_data_dict(s) do
    save_object(s, n, :degree)

    save_data_array(s, :gens) do
      for x in gens(G)
        vector_int = Vector{Int}(GAP.Globals.ListPerm(x.X))

        # we do this since we don't need any type information
        # inside the array
        save_data_array(s) do
          for i in vector_int
            save_object(s, i)
          end
        end
      end
    end
  end
end

function load_object(s::DeserializerState, ::Type{PermGroup}, dict::Dict)
  n = parse(Int, dict[:degree])
  generators = load_object(s, Vector, dict[:gens], Vector{Int})

  return permutation_group(n, [perm(x) for x in generators])
end


################################################################################
# PermGroupElem

@register_serialization_type PermGroupElem uses_params

function save_type_params(s::SerializerState, p::PermGroupElem)
  # this has just been more or less copied from the Rings section
  # and might be removed from this file during a future refactor
  save_data_dict(s) do
    save_object(s, encode_type(PermGroupElem), :name)
    parent_p = parent(p)
    if serialize_with_id(parent_p)
      parent_ref = save_as_ref(s, parent_p)
      save_object(s, parent_ref, :params)
    else
      save_typed_object(s, parent_x, :params)
    end
  end
end

function load_type_params(s::DeserializerState, ::Type{<:PermGroupElem},
                          dict::Dict{Symbol, Any})
  return load_typed_object(s, dict)
end


function save_object(s::SerializerState, p::PermGroupElem)
  vector_int = Vector{Int}(GAP.Globals.ListPerm(p.X))
  # again, here we dont need to store as a vector
  save_data_array(s) do 
    for i in vector_int
      save_object(s, i)
    end
  end
end

function load_object(s::DeserializerState, T::Type{PermGroupElem}, imgs_data::Vector,
                     parent_group::PermGroup)
  imgs = load_object(s, Vector, imgs_data, Int)
  return perm(parent_group, imgs)
end

################################################################################
# FPGroup

# @register_serialization_type(FPGroup)
# 
# function save_internal(s::SerializerState, G::FPGroup)
#   elfam = GAPWrap.ElementsFamily(GAPWrap.FamilyObj(G.X))
#   id = string(objectid(elfam))
#   D = _GAP_Families[_GAP_session_id[]]
#   if !haskey(D, id)
#     D[id] = elfam
#   end
# 
#   free = GAP.getbangproperty(elfam, :freeGroup)::GapObj
#   elfam = GAPWrap.ElementsFamily(GAPWrap.FamilyObj(free))
#   names = GAP.getbangproperty(elfam, :names)::GapObj
# 
#   res = Dict(
#     :session => _GAP_session_id[],
#     :family => string(id),
#     :symbols => save_type_dispatch(s, Vector{Symbol}(names)),
#   )
# 
#   if !is_full_fp_group(G)
#     # We have no Oscar object corresponding to the full f.p. group.
#     whole = GAP.getbangproperty(GAPWrap.FamilyObj(G.X), :wholeGroup)::GapObj
#     generators = Vector{Vector{Int}}(GAP.Globals.List(GAPWrap.GeneratorsOfGroup(G.X), GAPWrap.ExtRepOfObj))
#     res[:generators] = save_type_dispatch(s, generators)
#     if !GAP.Globals.IsFreeGroup(G.X)
#       rels = Vector{Vector{Int}}(GAP.Globals.List(GAPWrap.RelatorsOfFpGroup(whole), GAPWrap.ExtRepOfObj))
#       res[:relators] = save_type_dispatch(s, rels)
#     end
#   elseif !GAP.Globals.IsFreeGroup(G.X)
#     rels = map(syllables, Oscar.relators(G))
#     rels = [vcat([[x[1], x[2]] for x in l]...) for l in rels]
#     res[:relators] = save_type_dispatch(s, rels)
#   end
# 
#   return res
# end
# 
# function load_internal(s::DeserializerState, ::Type{FPGroup}, dict::Dict)
#   if !haskey(_GAP_Families, dict[:session])
#     # This is the first time we deserialize an object from that session id.
#     _GAP_Families[dict[:session]] = Dict{UInt64, GapObj}()
#   end
#   D = _GAP_Families[dict[:session]]
# 
#   if !haskey(dict, :relators)
#     # (subgroup of) a free group,
#     if haskey(D, dict[:family])
#       # Use the stored elements family.
#       elfam = D[dict[:family]]
#       G = FPGroup(GAP.getbangproperty(elfam, :freeGroup))
#     else
#       # Create the family anew, and store it (under the *old* key).
#       names = load_type_dispatch(s, Vector{Symbol}, dict[:symbols])
#       G = free_group(names)
#       elfam = GAPWrap.ElementsFamily(GAPWrap.FamilyObj(G.X))
#       D[dict[:family]] = elfam
#     end
#   else
#     # (subgroup of) quotient of a free group
#     if haskey(D, dict[:family])
#       # Use the stored elements family.
#       elfam = D[dict[:family]]
#       G = FPGroup(GAP.getbangproperty(GAPWrap.CollectionsFamily(elfam), :wholeGroup))
#     else
#       # Create the family anew, and store it (under the *old* key).
#       names = load_type_dispatch(s, Vector{Symbol}, dict[:symbols])
#       F = free_group(names)
#       rels = load_type_dispatch(s, Vector{Vector{Int}}, dict[:relators])
#       rels_pairs = Vector{Pair{Int, Int}}[]
#       for l in rels
#         rel = Pair{Int, Int}[]
#         for i in 1:2:(length(l)-1)
#           push!(rel, Pair{Int, Int}(l[i], l[i+1]))
#         end
#         push!(rels_pairs, rel)
#       end
#       G = quo(F, [F(l) for l in rels_pairs])[1]
#       elfam = GAPWrap.ElementsFamily(GAPWrap.FamilyObj(G.X))
#       D[dict[:family]] = elfam
#     end
#   end
# 
#   if haskey(dict, :generators)
#     generators = load_type_dispatch(s, Vector{Vector{Int}}, dict[:generators])
#     gens_pairs = Vector{Pair{Int, Int}}[]
#     for l in generators
#       gen = Pair{Int, Int}[]
#       for i in 1:2:(length(l)-1)
#         push!(gen, Pair{Int, Int}(l[i], l[i+1]))
#       end
#       push!(gens_pairs, gen)
#     end
# 
#     G = sub(G, [G(l) for l in gens_pairs])[1]
#   end
#   return G
# end
# 
# ################################################################################
# # FPGroupElem
# 
# @register_serialization_type(FPGroupElem)
# 
# function save_internal(s::SerializerState, g::FPGroupElem)
#   return Dict(
#     :parent => save_type_dispatch(s, parent(g)),
#     :extrep => save_type_dispatch(s, vcat([[x[1], x[2]] for x in syllables(g)]...))
#   )
# end
# 
# function load_internal(s::DeserializerState, T::Type{FPGroupElem}, dict::Dict)
#   parent_group = load_unknown_type(s, dict[:parent])
#   return load_internal_with_parent(s, T, dict, parent_group)
# end
# 
# function load_internal_with_parent(s::DeserializerState,
#                                    ::Type{FPGroupElem},
#                                    dict::Dict,
#                                    parent_group::FPGroup)
#   l = load_type_dispatch(s, Vector{Int}, dict[:extrep])
#   elfam = GAPWrap.ElementsFamily(GAPWrap.FamilyObj(parent_group.X))
#   free = GAP.getbangproperty(elfam, :freeGroup)::GapObj
#   freefam = GAPWrap.ElementsFamily(GAPWrap.FamilyObj(free))
#   v = GapObj(l)
#   w = GAPWrap.ObjByExtRep(freefam, v)
#   return group_element(parent_group, GAP.Globals.ElementOfFpGroup(elfam, w))
# end
# 
# 
