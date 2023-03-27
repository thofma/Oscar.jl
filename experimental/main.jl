import Glob
for fname in Glob.glob("*/src/main.jl")
  include(fname)
end
