@testset "Tropical Geometry" begin
    mktempdir() do path
        @testset "Tropical Curves" begin
            @testset "Abstract" begin
                Sigma = graph_from_adjacency_matrix(Undirected,[0 1 1; 1 0 1; 1 1 0]);
                multiplicities = Dict(sigma=>one(ZZ) for sigma in edges(Sigma))
                abs_TC = tropical_curve(Sigma,multiplicities)
                test_save_load_roundtrip(path, abs_TC) do loaded
                    @test graph(loaded) == graph(abs_TC)
                end
            end

            @testset "Embedded" begin
                IM = IncidenceMatrix([[1,2],[1,3],[1,4]])
                VR = [0 0; 1 0; -1 0; 0 1]
                PC = polyhedral_complex(QQFieldElem, IM, VR)
                TC = tropical_curve(PC)
                test_save_load_roundtrip(path, TC) do loaded
                    loaded_PC = polyhedral_complex(loaded)
                    @test nrays(PC) == nrays(loaded_PC)
                    @test n_maximal_polyhedra(PC) == n_maximal_polyhedra(loaded_PC)
                    @test dim(PC) == dim(loaded_PC)
                end
            end
        end

        @testset "Tropical Hypersurfaces" begin
            T = tropical_semiring(min)
            Txy,(x,y) = T["x","y"]
            f = x + y^2
            Tf = tropical_hypersurface(f)
            test_save_load_roundtrip(path, Tf) do loaded
                @test f == tropical_polynomial(loaded)
            end
        end
    end
end
