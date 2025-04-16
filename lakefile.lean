import Lake
open Lake DSL

package llm_math_generator {
  version := { major := 0, minor := 1, patch := 0 }
}

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"

lean_lib LLMMathGenerator

@[default_target]
lean_exe llm_math_generator where
  root := `Main
  supportInterpreter := true
