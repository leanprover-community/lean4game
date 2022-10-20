import Lean.Data.JsonRpc

-- The worker implementation roughly follows `Lean/Server/FileWorker.lean`.


#check IO.bindTask

#check Task
#check Task.CancelToken

#check EIO.mapTask

#check maybeTee

#check IO.FS.Stream.writeMessage
