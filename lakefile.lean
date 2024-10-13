import Lake
open Lake DSL

package LightData

@[default_target]
lean_lib LightData

require YatimaStdLib from git
  "https://github.com/lurk-lab/YatimaStdLib.lean" @ "v4.12.0"

require LSpec from git
  "https://github.com/yatima-inc/lspec/" @ "v4.12.0-toolchain"

lean_exe Tests.LightData
