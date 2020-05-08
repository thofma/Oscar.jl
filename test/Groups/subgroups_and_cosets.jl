@testset "Subgroups" begin
   G = symmetric_group(7)
   x = cperm(G,[1,2,3,4,5,6,7])
   y = cperm(G,[1,2,3])
   z = cperm(G,[1,2])

   H,f=sub(G,[x,y])
   K,g=sub(x,y)
   @test H isa PermGroup
   @test H==alternating_group(7)
   @test domain(f)==H
   @test codomain(f)==G
   @test [f(x) for x in gens(H)]==gens(H)
   @test (H,f)==(K,g)
   @test issubgroup(G,K)[1]
   @test g==issubgroup(G,K)[2]
   @test g==embedding(G,K)
   @test isnormal(G,H)
   H,f=sub(G,[x,z])
   @test H==G
   @test f==id_hom(G)

   H=sub(G,[G([2,3,1]),G([2,1])])[1]
   @test H != symmetric_group(3)
   @test isisomorphic(H, symmetric_group(3))[1]
   @test isisomorphic(H, symmetric_group(3))[2]==id_hom(H)       # TODO: this in future may change to false.
   @test listperm(H[1])==[2,3,1,4,5,6,7]
   @test listperm(symmetric_group(3)(H[1]))==[2,3,1]

   G = symmetric_group(4)
   A = alternating_group(4)
   L = subgroups(G)
   @test length(L)==30
   @test L[1] isa Tuple{PermGroup,Oscar.GAPGroupHomomorphism{PermGroup,PermGroup}}
   L1 = [x for x in L if isnormal(G,x[1])]
   K = [H[1] for H in normal_subgroups(G)]
   @test length(K)==4
   for H in L1
      @test H[1] in K
   end
   @test length(maximal_subgroups(G))==8
   @test (A,embedding(G,A)) in maximal_subgroups(G)
   @test maximal_normal_subgroups(G)==[(A,embedding(G,A))]
   H = sub(G,[G([3,4,1,2]), G([2,1,4,3])])
   @test minimal_normal_subgroups(G)==[H]
   @test length(characteristic_subgroups(G))==4
   @test H in characteristic_subgroups(G)
   @test ischaracteristic_subgroup(G,H[1])

   H1,h1 = sub(G, gens(symmetric_group(3)))
   H2,h2 = sub(G, gens(alternating_group(4)))
   K,f1,f2 = intersection(H1,H2)
   @test domain(f1)==K
   @test domain(f2)==K
   @test codomain(f1)==H1
   @test codomain(f2)==H2
   @test f1*h1==f2*h2
   @test degree(K)==degree(G)
   @test (K,f1*h1)==sub(G, gens(alternating_group(3)))

   @test derived_subgroup(G)[1] == alternating_group(4)
   L = derived_series(G)
   @test L[1][1] == G
   @test L[2][1] == alternating_group(4)
   @test L[3][1] == sub(G, [cperm([1,2],[3,4]), cperm([1,3],[2,4])])[1]
   @test L[4][1] == sub(G, [one(G)])[1]
end

@testset "Centralizers and Normalizers in Sym(n)" begin
   G = symmetric_group(6)
   x = cperm(G,[1,2])
   y = cperm(G,[1,2,3,4])

   Cx = centralizer(G,x)[1]
   Cy = centralizer(G,y)[1]
   @testset for i in 1:ngens(Cx)
      @test Cx[i]*x == x*Cx[i]
   end
   @testset for i in 1:ngens(Cy)
      @test Cy[i]*y == y*Cy[i]
   end
   notx = setdiff(G,Cx)
   noty = setdiff(G,Cy)
   @testset for i in 1:3
      z=rand(notx)
      @test z*x != x*z
      z=rand(noty)
      @test z*y != y*z
   end
   @test x in Cx
   @test one(G) in Cx
   @test isisomorphic(Cx, direct_product(symmetric_group(2),symmetric_group(4))[1])[1]
   @test isisomorphic(Cy, direct_product(sub(G,[y])[1], symmetric_group(2))[1])[1]

   Nx = normalizer(G,Cx)[1]
   Ny = normalizer(G,Cy)[1]
   @test isnormal(Nx,Cx)
   @test isnormal(Ny,Cy)
   notx = setdiff(G,Nx)
   noty = setdiff(G,Ny)
   @testset for i in 1:3
      z=rand(notx)
      @test Cx^z != Cx
      z=rand(noty)
      @test Cy^z != Cy
   end

   CCx = centralizer(G,Cx)[1]
   CCy = centralizer(G,Cy)[1]
   @testset for i in 1:ngens(Cx)
      for j in 1:ngens(CCx)
         @test Cx[i]*CCx[j] == CCx[j]*Cx[i]
      end
   end
   @testset for i in 1:ngens(Cy)
      for j in 1:ngens(CCy)
         @test Cy[i]*CCy[j] == CCy[j]*Cy[i]
      end
   end
   notx = setdiff(G,CCx)
   noty = setdiff(G,CCy)
   @testset for i in 1:3
      z=rand(notx)
      @test 1 in [z*k != k*z for k in gens(Cx)]
      z=rand(noty)
      @test 1 in [z*k != k*z for k in gens(Cy)]
   end
end

@testset "Cosets" begin
  
   G = dihedral_group(8)
   H, mH = centre(G)
  
   @test index(G, H) == 4
  
   C = right_coset(H, G[1])
   @test order(C) == length(elements(C))
  
   @test length(right_transversal(G, H)) == index(G, H)

   @testset "set comparation for cosets in PermGroup" begin
      G=symmetric_group(5)
      x = G(cperm([1,2,3]))
      y = G(cperm([1,4,5]))
      z = G(cperm([1,2],[3,4]))
      H = sub(G,[y])[1]
      K = sub(G,[z])[1]

      @test_throws ArgumentError rc = right_coset(H,K(z))
      @test_throws ArgumentError rc = left_coset(H,K(z))
      @test_throws ArgumentError dc = double_coset(H,K(z),K)
      @test_throws ArgumentError dc = double_coset(K,K(z),H)
      rc = right_coset(H,x)
      lc = left_coset(H,x)
      dc = double_coset(H,x,K)
      @test acting_domain(rc) == H
      @test acting_domain(lc) == H
      @test left_acting_group(dc) == H
      @test right_acting_group(dc) == K
      @test representative(rc) == x
      @test representative(lc) == x
      @test representative(dc) == x
      @test Set(elements(rc)) == Set([z for z in rc])          # test iterator
      @test Set(elements(dc)) == Set([z for z in dc])
      @test Set(elements(rc)) == Set([h*x for h in H])
      @test Set(elements(lc)) == Set([x*h for h in H])
      @test Set(elements(dc)) == Set([h*x*k for h in H for k in K])
      @test order(rc) == 3
      @test order(dc) == 6
      r1=rand(rc)
      r2=rand(dc)
      @test r1 in rc
      @test r2 in dc
      @test r1 in dc
      @test issubset(rc,dc)
      @test issubset(left_coset(K,x),dc)
      @test !isbicoset(rc)
   end

   H = sub(G, [cperm(G,[1,2,3]), cperm(G,[2,3,4])])[1]
   L = right_cosets(G,H)
   T = right_transversal(G,H)
   @test length(L)==10
   @test length(T)==10
   @testset for t in T
       @test sum([t in l for l in L]) == 1
   end
   rc = L[1]
   r = representative(rc)
   rc1 = right_coset(H, H[1]*r)
   @test representative(rc1) != representative(rc)
   @test rc1 == rc
   L = left_cosets(G,H)
   T = left_transversal(G,H)
   @test length(L)==10
   @test length(T)==10
   @testset for t in T
       @test sum([t in l for l in L]) == 1
   end
   lc = L[1]
   r = representative(lc)
   lc1 = left_coset(H, r*H[1])
   @test representative(lc1) != representative(lc)
   @test lc1 == lc

end

@testset "Predicates for groups" begin
   @test !issimple(alternating_group(4))
   @test issimple(alternating_group(5))
   @test issimple(quo(SL(4,3), centre(SL(4,3))[1])[1])

   @test isalmostsimple(symmetric_group(5))
   @test !issimple(symmetric_group(5))

   @test isperfect(alternating_group(5))
   @test !isperfect(alternating_group(4))
   
   @test !ispgroup(alternating_group(4))[1]
   @test ispgroup(alternating_group(3)) == (true,3)
   @test ispgroup(quaternion_group(8)) == (true,2)
end

@testset "Sylow and Hall subgroups" begin
   G = symmetric_group(4)

   P = sylow_subgroup(G,2)[1]
   @test order(P)==8
   @test isisomorphic(P,dihedral_group(8))[1]
   P = sylow_subgroup(G,3)[1]
   @test order(P)==3
   @test isconjugate(G, P, sub(G, [cperm(1:3)])[1])[1]
   P = sylow_subgroup(G,5)[1]
   @test P==sub(G,[one(G)])[1]
   @test_throws ArgumentError P=sylow_subgroup(G,4)

   G = cyclic_group(210)
   g = G[1]
   @testset for i in [2,3,5,7]
      @test sylow_subgroup(G,i) == sub(G,[g^(210 ÷ i)])
   end
   L = [[2],[3],[5],[7],[2,3],[2,5],[2,7],[3,5],[3,7],[5,7],[2,3,5],[2,3,7],[2,5,7],[3,5,7],[2,3,5,7]]
   @testset for l in L
      @test hall_subgroup(G,l) == sub(G,[g^(210÷lcm(l))])
   end
   @test hall_subgroup(G,Int64[])==sub(G,[one(G)])
   @test_throws ArgumentError P=hall_subgroup(G,[4])
   @test_throws ArgumentError P=hall_subgroup(symmetric_group(5),[2,3])

   L = sylow_system(G)
   Lo = [order(l[1]) for l in L]
   @test length(Lo)==length(factor(order(G)))
   @test prod(Lo) == order(G)
   @test [isprime(ispower(l)[2]) for l in Lo] == [1 for i in 1:length(L)]
   L = complement_system(G)
   Lo = [index(G,l[1]) for l in L]
   @test length(Lo)==length(factor(order(G)))
   @test prod(Lo) == order(G)
   @test [isprime(ispower(l)[2]) for l in Lo] == [1 for i in 1:length(L)]
   
end

@testset "Some specific subgroups" begin
   G = GL(2,3)
   S = symmetric_group(4)

   @test order(fitting_subgroup(G)[1])==8
   @test fitting_subgroup(S)==sub(S,[S([3,4,1,2]), S([4,3,2,1])])
   @test frattini_subgroup(S)==sub(S,[one(S)])
   @test frattini_subgroup(G)[1]==intersection([H[1] for H in maximal_subgroups(G)])[1]
   @test frattini_subgroup(G)==centre(G)
   @test ischaracteristic_subgroup(G,centre(G)[1])
   @test socle(G)==frattini_subgroup(G)
   @test socle(S)==fitting_subgroup(S)   
   @test radical_subgroup(S)[1]==S
   S = symmetric_group(5)
   @test radical_subgroup(S)==sub(S,[one(S)])
end
