using Distributed

mutable struct OscarWorkerPool <: AbstractWorkerPool
  channel::Channel
  workers::Set{Int}
  ref::RemoteChannel
end

oscar_worker_pool(c::Channel, workers::Vector{Int},
                  ref::RemoteChannel) = OscarWorkerPool(c, workers, ref)

function set_channels(input::Type{S}, output::Type{T}, params::Type{U};
                      channel_size::Tuple{Int, Int, Int} = (10, 10, 10)) where {S, T, U}
  return (
    Channel{S}(channel_size[1]),
    RemoteChannel(() -> Channel{T}(channel_size[2])),
    RemoteChannel(() -> Channel{U}(channel_size[3]))
  )
end

function put_params(params_channel::RemoteChannel, params::Any)
  for w in workers()
    put!(params_channel, params)
  end

  for w in workers()
    remote_do(w, params_channel) do chnnl
      remote_params = take!(chnnl)
    end
  end
end

function parallel_do(f::Function, v::Vector, in_chnnl::RemoteChannel,
                     out_chnnl::RemoteChannel)
  n = length(v)
  for x in v
    put!(in_chnnl, x)
  end
  
end
