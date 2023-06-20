import Lake
open Lake DSL

package REPL {
  -- add package configuration options here
}

lean_lib REPL {
  -- add library configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "f0dfd500df203fb5a22ed01a4ab0f2dc874e203f"


-- Unfortunately the compiled version doesn't work: `unknown package 'Init'`
@[default_target]
lean_exe repl where
  root := `REPL.Main
  supportInterpreter := true
