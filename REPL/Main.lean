/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import REPL.JSON
import REPL.Frontend
import REPL.InfoTree
import Mathlib

#check algebraInt

-- example : Algebra ℤ ℝ := inferInstance
/-!
# A REPL for Lean.

Communicates via JSON on stdin and stdout. Commands should be separated by blank lines.

Commands may be of the form
```
{ "cmd" : "import Mathlib.Data.List.Basic\ndef f := 2" }
```
or
```
{ "cmd" : "example : f = 2 := rfl", "env" : 3 }
```

The `env` field, if present,
must contain a number received in the `env` field of a previous response,
and causes the command to be run in the existing environment.

If there is no `env` field, a new environment is created.

You can only use `import` commands when you do not specify the `env` field.

You can backtrack simply by using earlier values for `env`.

The results are of the form
```
{"sorries":
 [{"pos": {"line": 1, "column": 18},
   "endPos": {"line": 1, "column": 23},
   "goal": "\n⊢ Nat"}],
 "messages":
 [{"severity": "error",
   "pos": {"line": 1, "column": 23},
   "endPos": {"line": 1, "column": 26},
   "data":
   "type mismatch\n  rfl\nhas type\n  f = f : Prop\nbut is expected to have type\n  f = 2 : Prop"}],
 "env": 6}
 ```
 showing any messages generated, or sorries with their goal states.
 Information is generated for tactic mode sorries, but not for term mode sorries.
-/

open Lean Elab

namespace REPL

/-- The monadic state for the Lean REPL. -/
structure State where
  environments : Array Environment
  lines : Array Nat

/-- The Lean REPL monad. -/
abbrev M (m : Type → Type) := StateT State m

variable [Monad m] [MonadLiftT IO m]

/-- Get the next available id for a new environment. -/
def nextId : M m Nat := do pure (← get).environments.size

/-- Run a command, returning the id of the new environment, and any messages and sorries. -/
unsafe def run (s : Run) : M m Response := do
  let env? := s.env.bind ((← get).environments[·]?)
  let (env, messages, trees) ← IO.processInput s.cmd env? {} ""
  let messages ← messages.mapM fun m => Message.of m
  let sorries ← trees.bind InfoTree.sorries |>.mapM
    fun ⟨ctx, g, pos, endPos⟩ => Sorry.of ctx g pos endPos
  let lines := s.cmd.splitOn "\n" |>.length
  let id ← nextId
  modify fun s => { environments := s.environments.push env, lines := s.lines.push lines }
  pure ⟨id, messages, sorries⟩

end REPL

open REPL

/-- Get lines from stdin until a blank line is entered. -/
unsafe def getLines : IO String := do
  match (← (← IO.getStdin).getLine) with
  | "" => pure ""
  | "\n" => pure "\n"
  | line => pure <| line ++ (← getLines)

/-- Read-eval-print loop for Lean. -/
unsafe def repl : IO Unit :=
  StateT.run' loop ⟨#[], #[]⟩
where loop : M IO Unit := do
  let query ← getLines
  if query = "" then
    return ()
  let json := Json.parse query
  match json with
  | .error e => IO.println <| toString <| toJson (⟨e⟩ : Error)
  | .ok j => match fromJson? j with
    | .error e => IO.println <| toString <| toJson (⟨e⟩ : Error)
    | .ok (r : Run) => IO.println <| toString <| toJson (← run r)
  loop

-- TOJson instance, fine.
-- 1. string for "goal" + "hypotheses" 
-- 2. in the term mode sense, local context + type
-- 3. list of the constants in every expression. 
structure MLInfo where
deriving ToJson

-- MetavarContext : MVar -> MVarDecl
-- MVarDecl: info about each mvar + local-context
-- local-context: a typing context of hypotheses + judgements.
--  this is also used during e.g. locally nameless manipulations,
--  where going under telescopes extends the local-context. 
--  Said differently, it's a map from FVarId to LocalDecl
-- LocalDecl: name, type, value, binder info, etc.

def MLInfo.default : MLInfo := { : MLInfo }  

-- For each TacticInfo node, look at subnodes that are TermInfo and collect
--   constants from their expression. This will be the constants that have been
--   created upon tactic elaboration.
-- For each TermInfo node, 

-- For each TermInfo info, go through their children, and if it's an identifier,
--  check what it elaborates to. If it elaborates to an 
--  (application of a constant) [or a constant],
--  keep it. 
-- le_refl -> ... 
open Meta in 
partial def getInfoFromTree (tree : InfoTree) : IO MLInfo := do 
  tree.foldInfo' (init := pure MLInfo.default) fun ctx tree infoM => do
    match tree with 
    | .node (i := Info.ofTacticInfo i) .. =>
        let mctxBefore := i.mctxBefore
        for g in i.goalsBefore do 
          let decl := mctxBefore.getDecl g
          ctx.runMetaM decl.lctx <| do 
            let fmt ← _root_.Lean.Meta.ppGoal g
            let s := toString fmt
            IO.println s
          if i.goalsAfter.contains g then continue
          ctx.runMetaM decl.lctx <| do
            withMCtx i.mctxAfter <| do 
              let gval ← instantiateMVars (Expr.mvar g)
              let fmt ← _root_.Lean.Meta.ppExpr gval
              let s := toString fmt
              IO.println s!"goal: {s}"
        infoM
        
    -- TODO: this is not what we wanted. For every term, collect these
    -- identifiers in the children.
    | .node (i := Info.ofTermInfo i) .. =>
      match i.stx with 
      | .ident .. => do 
        -- if it's an ident, now we need to check what it elaborates to.
        --  if it's a constant, we keep it.
        -- Recall that `Name` can correspond to names that are both 
        -- pre-and-post resolution, so we cannot use the `Ident.name`.
        -- Rather, we look at the elaborated Expr and grab the head of the
        -- function application (assuming it is an application).
        IO.println s!"identifier {i.stx} with expression {i.expr.getAppFn.constName}" 
      | _ => pure ()
      try
        ctx.runMetaM i.lctx <| do
          -- isBinder?
          let e := i.expr 
          let t ← inferType e   
          let consts := e.foldConsts (init := []) List.cons
          IO.println s!"expr: ({← ppExpr e} : {← ppExpr t}) | {consts}"
      catch _ex => pure () 
      infoM
    | _ => infoM


/-- Main executable function, run as `lake env lean --run Mathlib/Util/REPL.lean`. -/
unsafe def main (_ : List String) : IO Unit := do
  -- TODO: take file path from command line for scripting.
  let contents ← IO.FS.readFile "lake-packages/mathlib/Mathlib/Algebra/Algebra/Basic.lean"
  let (env, messages, trees) ← IO.processInput contents (env? := .none) {} ""
  IO.println s!"num info trees: {trees.length}"  
  for tree in trees do 
    let _ ← getInfoFromTree tree 

