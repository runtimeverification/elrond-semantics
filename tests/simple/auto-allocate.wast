setExitCode 1

(module
   (import "env" "getHash" (func (param i32) (result i32)))
   (import "env" "getArgNum" (func (param i32) (result i32))))

setExitCode 0
