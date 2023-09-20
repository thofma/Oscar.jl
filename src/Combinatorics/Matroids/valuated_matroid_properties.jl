@doc raw"""                                                            
    subdivision_of_matroid_polytope(VM::ValuatedMatroid)
                                                                       
Construct the subdivision of the matroid polytope of `VM` induced by the
valuation.
"""  
function subdivision_of_matroid_polytope(VM::ValuatedMatroid)
  P = matroid_polytope(VM)
  V = matrix(QQ, vertices(P))
  cells = map(s->[i for i in s], Polymake.to_one_based_indexing(pm_object(VM).SUBDIVISION))
  return subdivision_of_points(V, cells)
end
export subdivision_of_matroid_polytope
