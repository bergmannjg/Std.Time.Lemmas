import Lake
open System Lake DSL

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.15.0"

require tryAtEachStep from git "https://github.com/dwrensha/tryAtEachStep" @ "lean-v4.15.0"

package time {
  lintDriver := "batteries/runLinter"
}

@[default_target]
lean_lib Time
