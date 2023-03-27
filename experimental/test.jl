import Glob
for fname in Glob.glob("*/test/runtests.jl")
  include(fname)
end
