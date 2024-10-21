import Lake
open Lake DSL

package LightData

@[default_target]
lean_lib LightData

require YatimaStdLib from git
  "https://github.com/argumentcomputer/YatimaStdLib.lean" @ "v4.12.0"

require LSpec from git
  "https://github.com/argumentcomputer/lspec/" @ "v4.12.0"

lean_exe Tests.LightData
