using Oscar
using Test
using Distributed

import Random

import InteractiveUtils

using Printf

if VERSION >= v"1.10.0-DEV"
  jlmax = @ccall jl_gc_get_max_memory()::UInt64
  maxmem = @ccall uv_get_total_memory()::UInt64
  limmem = @ccall uv_get_constrained_memory()::UInt64
  memenv = parse(Float64, get(ENV, "OSCARCI_MAX_MEM_GB", "0")) * 2^30
  if memenv > 0
    println("OscarCI: Limiting memory from ", Base.format_bytes(jlmax), " to ", Base.format_bytes(memenv));
    @ccall jl_gc_set_max_memory(memenv::UInt64)::Cvoid
  end
end

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

if VERSION >= v"1.8.0"
  # Enable GC logging to help track down certain GC related issues.
  # Note that several test files need to temporarily disable and then
  # re-enable this. If we need to disable this globally, those files
  # need to be adjusted as well.
  @everywhere  GC.enable_logging(true)
end

@everywhere import Oscar.Nemo.AbstractAlgebra
@everywhere include(joinpath(pathof(Oscar.Nemo.AbstractAlgebra), "..", "..", "test", "Rings-conformance-tests.jl"))

# hotfix, otherwise StraightLinePrograms returns something which then leads to an error
module SLPTest
end

# some helpers
@everywhere import Printf
@everywhere import PrettyTables

# the current code for extracting the compile times does not work on earlier
# julia version
@everywhere const compiletimes = @static VERSION >= v"1.9.0-DEV" ? true : false

@everywhere const stats_dict = Dict{String,NamedTuple}()

function print_stats(io::IO; fmt=PrettyTables.tf_unicode, max=50)
  sorted = sort(collect(stats_dict), by=x->x[2].time, rev=true)
  println(io, "### Stats per file")
  println(io)
  table = hcat(first.(sorted), permutedims(reduce(hcat, collect.(values.(last.(sorted))))))
  formatters = nothing
  @static if compiletimes
    header=[:Filename, Symbol("Runtime in s"), Symbol("+ Compilation"), Symbol("+ Recompilation"), Symbol("Allocations in MB")]
    #formatters = PrettyTables.ft_printf("%.2f%%", [3,4])
  else
    header=[:Filename, Symbol("Time in s"), Symbol("Allocations in MB")]
  end
  PrettyTables.pretty_table(io, table; tf=fmt, max_num_of_rows=max, header=header, formatters=formatters)
end

@everywhere function meminfo_julia()
  # @printf "GC total:  %9.3f MiB\n" Base.gc_total_bytes(Base.gc_num())/2^20
  # Total bytes (above) usually underreports, thus I suggest using live bytes (below)
  @printf "GC live:   %9.3f MiB\n" Base.gc_live_bytes()/2^20
  @printf "JIT:       %9.3f MiB\n" Base.jit_total_bytes()/2^20
  @printf "Max. RSS:  %9.3f MiB\n" Sys.maxrss()/2^20
  @printf "Free mem:  %9.3f MiB\n" Sys.free_memory()/2^20
  @printf "Free pmem: %9.3f MiB\n" Sys.free_physical_memory()/2^20
end

# we only want to print stats for files that run tests and not those that just
# include other files
@everywhere const innermost = Ref(true)
# redefine include to print and collect some extra stats
@everywhere function include(str::String)
  innermost[] = true
  # we pass the identity to avoid recursing into this function again
  @static if compiletimes
    compile_elapsedtimes = Base.cumulative_compile_time_ns()
  end
  stats = @timed Base.include(identity, Main, str)
  GC.gc(false); GC.gc(true);
  # skip files which just include other files and ignore
  # files outside of the oscar folder
  if innermost[] && !isabspath(str)
    @static if compiletimes
      compile_elapsedtimes = Base.cumulative_compile_time_ns() .- compile_elapsedtimes
      compile_elapsedtimes = compile_elapsedtimes ./ 10^9
    end
    path = Base.source_dir()
    path = joinpath(relpath(path, joinpath(Oscar.oscardir,"test")), str)
    rtime=NaN
    @static if compiletimes
      comptime = first(compile_elapsedtimes)
      rcomptime = last(compile_elapsedtimes)
      stats_dict[path] = (time=stats.time-comptime, ctime=comptime-rcomptime, rctime=rcomptime, alloc=stats.bytes/2^20)
      Printf.@printf "-> Testing %s took: runtime %.3f seconds + compilation %.3f seconds + recompilation %.3f seconds, %.2f MB\n" path stats.time-comptime comptime-rcomptime rcomptime stats.bytes/2^20
    else
      Printf.@printf "-> Testing %s took: %.3f seconds, %.2f MB\n" path stats.time stats.bytes/2^20
      stats_dict[path] = (time=stats.time, alloc=stats.bytes/2^20)
    end
    innermost[] = false
  end
end

@static if compiletimes
  Base.cumulative_compile_timing(true)
end

testlist = [
  "Aqua.jl",
  "printing.jl",

  "PolyhedralGeometry/runtests.jl",
  "Combinatorics/runtests.jl",
  "GAP/runtests.jl",
  "Groups/runtests.jl",
  "Rings/runtests.jl",
  "NumberTheory/runtests.jl",
  "Modules/runtests.jl",
  "InvariantTheory/runtests.jl",

  "AlgebraicGeometry/Schemes/runtests.jl",
  "AlgebraicGeometry/ToricVarieties/runtests.jl",
  "AlgebraicGeometry/Surfaces/runtests.jl",

  "TropicalGeometry/runtests.jl",

  "Serialization/runtests.jl",
  "Serialization/polymake/runtests.jl",
  "Serialization/upgrades/runtests.jl",

  # Automatically include tests of all experimental packages following our
  # guidelines.
  "../experimental/runtests.jl",

  "Data/runtests.jl",
  "StraightLinePrograms/runtests.jl",
]

InteractiveUtils.versioninfo(verbose=true)

# if many workers, distribute tasks across them
# otherwise, is essentially a serial loop
pmap(include, testlist)

InteractiveUtils.versioninfo(verbose=true)

@static if compiletimes
  Base.cumulative_compile_timing(false);
end

#currently, print_stats will fail when running tests with external workers
#TODO: potentially rewrite include as well as print_stats 
#      to comply with parallel decisions
if numprocs == 1
  if haskey(ENV, "GITHUB_STEP_SUMMARY") && compiletimes
    open(ENV["GITHUB_STEP_SUMMARY"], "a") do io
      print_stats(io, fmt=PrettyTables.tf_markdown)
    end
  else
    print_stats(stdout; max=10)
  end
end

cd(oldWorkingDirectory)
