import Lean
import Cli
import GenSeq

open Lean Elab Term Cli Synth

def generate (name : String) (offst : Nat) (source : String) : MetaM String := do
   return TtoLean name offst (← TermElabM.run' <| parse source)

unsafe
def run (p : Parsed) : IO UInt32 := do
  let name := p.positionalArg! "name" |>.as! String
  let offst := p.positionalArg! "offset" |>.as! Nat
  let source := p.positionalArg! "source" |>.as! String

  let modules := #[`GenSeq]
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules (modules.map ({module := ·})) {} (trustLevel := 1024) (loadExts := true)
  let ctx := {fileName := "", fileMap := default}
  let state := {env}
  Prod.fst <$> (Meta.MetaM.toIO · ctx state) do
    IO.println <| (← generate name offst source)
  return 0

unsafe
def cmd : Cmd := `[Cli|
  "genseq" VIA run; ["0.1.0"]
  "Generate a Lean definition from the synthetic DSL."

  ARGS:
      name : String;    "Name for the declaration of the sequence"
      offset : Nat;     "Offset for the sequence"
      source : String;  "Source code from the synthetic DSL"
]

unsafe
def main (args : List String) : IO UInt32 := do
  cmd.validate args
