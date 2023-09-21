################################################################################
##  Constructing
################################################################################

struct ValuatedMatroid{Addition} 
  pm_matroid::Polymake.BigObject
  groundset::AbstractVector # groundset of the matroid 
  gs2num::Dict{Any,IntegerUnion}# dictionary to map the groundset to the integers from 1 to its size
end

pm_object(VM::ValuatedMatroid) = VM.pm_matroid

function valuated_matroid_from_bases(
  bases::Union{AbstractVector{T},AbstractSet{T}},
  groundset::GroundsetType,
  valuation,
  addition;
  check::Bool=true,
) where {T<:GroundsetType}
  groundset = collect(groundset)
  bases = collect(bases)

  if check && length(groundset) != length(Set(groundset))
    error("Input is not a valid groundset of a matroid")
  end
  if check && !all([e in groundset for S in bases for e in S])
    error("The bases contain elements that are not in the groundset")
  end
  if length(bases) == 0
    error("The collection of bases can not be empty")
  end

  gs2num = create_gs2num(groundset)
  pm_bases = Vector{Int}[[gs2num[i] - 1 for i in B] for B in bases]
  M = Polymake.matroid.ValuatedMatroid{addition}(;
    BASES=pm_bases, N_ELEMENTS=length(groundset), VALUATION_ON_BASES=valuation
  )
  if check && !Polymake.matroid.check_basis_exchange_axiom(M.BASES)
    error("Input is not a collection of bases")
  end
  return ValuatedMatroid{addition}(M, groundset, gs2num)
end
valuated_matroid_from_bases(
  bases::Union{AbstractVector{T},AbstractSet{T}},
  nelements::IntegerUnion,
  valuation,
  addition;
  check::Bool=true,
) where {T<:GroundsetType} =
  valuated_matroid_from_bases(bases, Vector(1:nelements), valuation, addition; check=check)
export valuated_matroid_from_bases

function valuated_matroid_from_circuits(
  circuits::Union{AbstractVector{T},AbstractSet{T}},
  groundset::GroundsetType,
  valuation,
  addition;
  check::Bool=true,
) where {T<:GroundsetType}
  groundset = collect(groundset)
  circuits = collect(circuits)

  if check && length(groundset) != length(Set(groundset))
    error("Input is not a valid groundset of a matroid")
  end
  if check && !all([e in groundset for S in circuits for e in S])
    error("The bases contain elements that are not in the groundset")
  end

  gs2num = create_gs2num(groundset)
  pm_circuits = [[gs2num[i] - 1 for i in C] for C in circuits]
  M = Polymake.matroid.ValuatedMatroid{addtion}(;
    CIRCUITS=pm_circuits, N_ELEMENTS=length(groundset), VALUATION_ON_CIRCUIOTS=valuation
  )
  #TODO check_circuit_exchange_axiom (requires an update of polymake)
  #if check && !Polymake.matroid.check_circuit_exchange_axiom(M.CIRCUITS)
  #   error("Input is not a collection of circuits")
  #end
  return ValuatedMatroid{addition}(M, groundset, gs2num)
end
valuated_matroid_from_circuits(
  circuits::Union{AbstractVector{T},AbstractSet{T}},
  nelements::IntegerUnion,
  valuation,
  addition,
) where {T<:GroundsetType} =
  valuated_matroid_from_circuits(circuits, Vector(1:nelements), valuation, addition)
export valuated_matroid_from_circuits
