using Oscar
using Test
using Distributed

import Random

numprocs_str = get(ENV, "NUMPROCS", "1")

oldWorkingDirectory = pwd()
cd(joinpath(pkgdir(Oscar), "test"))

if !isempty(ARGS)
  jargs = [arg for arg in ARGS if startswith(arg, "-j")]
  if !isempty(jargs)
    numprocs_str = split(jargs[end], "-j")[end]
  end
end

const numprocs = parse(Int, numprocs_str)

if numprocs >= 2
  println("Adding worker processes")
  addprocs(numprocs)
end

if haskey(ENV, "JULIA_PKGEVAL") ||
  get(ENV, "CI", "") == "true" ||
  haskey(ENV, "OSCAR_RANDOM_SEED")
  seed = parse(UInt32, get(ENV, "OSCAR_RANDOM_SEED", "42"))
  @info string(@__FILE__)*" -- fixed SEED $seed"
else
  seed = rand(UInt32)
  @info string(@__FILE__)*" -- SEED $seed"
end

@everywhere using Test
@everywhere using Oscar
@everywhere Oscar.set_seed!($seed)
@everywhere Oscar.randseed!($seed)
# setting the global julia seed does not work for distributed processes
# the RNG is task-local and each '@everywhere' runs in a separate task...
# to make sure we seed the main process we run this again
Oscar.randseed!(seed)

@everywhere import Oscar.Nemo.AbstractAlgebra
@everywhere include(joinpath(pathof(Oscar.Nemo.AbstractAlgebra), "..", "..", "test", "Rings-conformance-tests.jl"))

# hotfix, otherwise StraightLinePrograms returns something which then leads to an error
module SLPTest
end

# some helpers
@everywhere import PrettyTables


function print_stats(io::IO, stats_dict::Dict; fmt=PrettyTables.tf_unicode, max=50)
  sorted = sort(collect(stats_dict), by=x->x[2].time, rev=true)
  println(io, "### Stats per file")
  println(io)
  table = hcat(first.(sorted), permutedims(reduce(hcat, collect.(values.(last.(sorted))))))
  formatters = nothing
  if haskey(first(values(stats_dict)), :ctime)
    header=[:Filename, Symbol("Runtime in s"), Symbol("+ Compilation"), Symbol("+ Recompilation"), Symbol("Allocations in MB")]
    #formatters = PrettyTables.ft_printf("%.2f%%", [3,4])
  else
    header=[:Filename, Symbol("Time in s"), Symbol("Allocations in MB")]
  end
  PrettyTables.pretty_table(io, table; tf=fmt, max_num_of_rows=max, header=header, formatters=formatters)
end


testlist = Oscar._gather_tests("test")

for exp in [Oscar.exppkgs; Oscar.oldexppkgs]
  path = joinpath(Oscar.oscardir, "experimental", exp, "test")
  if isdir(path)
    append!(testlist, Oscar._gather_tests(path))
  end
end

# make sure we have the same list everywhere
sort!(testlist)
Random.shuffle!(Oscar.get_seeded_rng(), testlist)

@everywhere testlist = $testlist

# this is to check for obsolete include statements in the tests
@everywhere function include(str::String, mod::Module=Main)
  if joinpath(Base.source_dir(), str) in testlist
    @error "invalid include of $str: this file is be included automatically"
  else
    Oscar._timed_include(str, mod)
  end
end

# if many workers, distribute tasks across them
# otherwise, is essentially a serial loop
stats = merge(pmap(x -> Oscar.test_module(x; new=false, timed=true), testlist)...)

# this needs to run here to make sure it runs on the main process
# it is in the ignore list for the other tests
if numprocs == 1
   push!(stats, Oscar._timed_include("Serialization/IPC.jl", Main))
end

if haskey(ENV, "GITHUB_STEP_SUMMARY")
  open(ENV["GITHUB_STEP_SUMMARY"], "a") do io
    print_stats(io, stats; fmt=PrettyTables.tf_markdown)
  end
else
  print_stats(stdout, stats; max=10)
end

cd(oldWorkingDirectory)
