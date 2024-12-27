import Lake
open System Lake DSL

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.15.0-rc1"

require tryAtEachStep from git "https://github.com/dwrensha/tryAtEachStep" @ "main"

package time {
}

@[default_target]
lean_lib Time
