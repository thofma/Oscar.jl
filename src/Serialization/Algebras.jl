################################################################################
# FreeAssAlgebra

# Free associative algebra serialization
@registerSerializationType(FreeAssAlgebra, true)

function save_object(s::SerializerState, A::FreeAssAlgebra)
  data_dict(s) do
    save_typed_object(s, base_ring(A), :base_ring),
    save_object(s, symbols(A), :symbols)
  end
end

function load_object(s::DeserializerState, ::Type{<:FreeAssAlgebra}, dict::Dict)
  R = load_typed_object(s, dict[:base_ring])
  gens = map(Symbol, dict[:symbols])
  return free_associative_algebra(R, gens)[1]
end

# Free associative algebra element serialization
@register_serialization_type(FreeAssAlgElem)
type_needs_params(::Type{<:FreeAssAlgElem}) = true

# see save_type_params in Rings

function save_object(s::SerializerState, f::FreeAssAlgElem)
  data_array(s) do
    for term in terms(f)
      data_array(s) do
        save_object(s, collect(exponent_words(term))[1])
        save_object(s, collect(coefficients(term))[1])
      end
    end
  end
end

function load_object(s::DeserializerState, ::Type{<:FreeAssAlgElem},
                     terms::Vector, parents::Vector)
  parent_algebra = parents[end]
  coeff_type = elem_type(base_ring(parent_algebra))
  elem = parent_algebra(0)
  for term  in terms
    loaded_coeff = load_object(s, coeff_type, term[2])
    loaded_term = parent_algebra(loaded_coeff)
    for word in term[1]
      loaded_term *= parent_algebra[parse(Int, word)]
    end
    elem += loaded_term
  end

  return elem
end

# Ideals
@register_serialization_type(FreeAssAlgIdeal)
type_needs_params(::Type{<:FreeAssAlgIdeal}) = true
