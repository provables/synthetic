import Lean
import Cli
import GenSeq

open Lean Elab Term Cli Synth
open Std Net
open Qq

structure GenSeqContext where
  env : Environment
  ctx : Core.Context
  state : Core.State

abbrev GenSeqState a := ReaderT GenSeqContext IO a
abbrev GenSeqExcept m := ExceptT String GenSeqState m

def GenSeqState.run {α : Type} (x : GenSeqState α)
    (env : Environment) (ctx : Core.Context) (state : Core.State) : IO α :=
  ReaderT.run x ⟨env, ctx, state⟩

instance : ToString SocketAddress where
  toString
  | .v4 ⟨a, p⟩ => s!"{a}:{p}"
  | .v6 ⟨a, p⟩ => s!"{a}:{p}"

def toLean (name source : String) (offst : Nat) : GenSeqExcept String := do
  let state ← read
  ExceptT.mk <| Prod.fst <$> (Meta.MetaM.toIO · state.ctx state.state) do
    TermElabM.run' (DSLToLean name source offst)

def gen (obj : Json) : GenSeqExcept Json := do
  let name ← obj.getObjValAs? String "name" |>.mapError (s!"missing name: {·}")
  let offst ← obj.getObjValAs? Nat "offset" |>.mapError (s!"missing offset: {·}")
  let source ← obj.getObjValAs? String "source" |>.mapError (s!"missing source: {·}")
  let z ← toLean name source offst
  return Json.mkObj [
    ("lean", z)
  ]

def ready (_obj : Json) : GenSeqExcept Json := do
  return Json.mkObj [
    ("status", "ready")
  ]

def sum (obj : Json) : GenSeqExcept Json := do
  let x ← obj.getObjValAs? Int "x" |>.mapError (s!"missing x: {·}")
  let y ← obj.getObjValAs? Int "y" |>.mapError (s!"missing y: {·}")
  return Json.mkObj [
    ("x + y", x + y)
  ]

-- def eval (..)
--    get "def Af8"
--     String -> Expr (grammar.lean)
--    get values [(1, 32423)]
--    evaluate def for every idx, value
--     Expr -> ℤ (sequencelib/Meta/DeriveTheorems.lean)
--    check
def termStringToExpr (s : String) : TermElabM Lean.Expr := do
  let env ← Lean.getEnv
  let stx ← Lean.ofExcept (Lean.Parser.runParserCategory env `term s)
  Lean.Elab.Term.elabTerm stx none -- `none` for expected type if not known

#check Command.CommandElab
def cmdStringToExpr (s : String) : Command.CommandElabM Unit := do
  let env ← Lean.getEnv
  let stx ← Lean.ofExcept (Lean.Parser.runParserCategory env `command s)
  Lean.Elab.Command.elabCommand stx

run_cmd do
  let x ← cmdStringToExpr r#"def h (n : ℕ ) : ℤ := n"#
  dbg_trace (h 1)

def cmdStringToLean (s : String) : GenSeqExcept Unit := do
  let state ← read
  Prod.fst <$> (Meta.MetaM.toIO · state.ctx state.state) do
    liftCommandElabM (cmdStringToExpr s)

def evalSyntax (values: Array (Int × Int)) (decl: Name) : TermElabM Bool := do
  for (idx, val) in values do
    let value ← instantiateMVars (
      ← Term.elabTerm (← `(term|$(mkIdent decl):ident $(quote idx))) (some (mkConst `Int [])))
    Term.synthesizeSyntheticMVarsNoPostponing
    let z ← unsafe Meta.evalExpr Int (mkConst `Int []) value
    if z != val then
      return false
  return true

def h (n : ℕ) : ℤ := n

run_elab do
  let b ← evalSyntax #[ (1, 1), (2, 2) ] `h
  dbg_trace b

def eval (obj : Json) : GenSeqExcept Json := do
  let src ← obj.getObjValAs? String "src" |>.mapError (s!"missing src: {·}")
  cmdStringToLean src
  let name ← obj.getObjValAs? String "name" |>.mapError (s!"missing name: {·}")
  let decl := Name.mkSimple name
  dbg_trace s!"got decl {decl}"
  let values ← obj.getObjValAs? (Array (Int × Int)) "values" |>.mapError (s!"missing values: {·}")

  dbg_trace s!"got values {values}"
  let state ← read
  let result ←  Prod.fst <$> (Meta.MetaM.toIO · state.ctx state.state) do
    TermElabM.run' (evalSyntax values decl)
  dbg_trace s!"Got result {result}"
  return Json.mkObj [
    ("src", src),
    ("values", values.toJson),
    ("result", result)
  ]

run_elab do
  let x ← termStringToExpr "1 + 1"
  IO.println s! "{x}"

run_meta do
  let j ← Lean.ofExcept (Json.parse r#"{"cmd": "eval", "args": {"src": "def h (n : ℕ ) : ℕ := n", "values": [[1,2], [2, 6]] } }"#)
  let x := GenSeqState.run (ExceptT.run (eval j))

def Commands : Std.HashMap String (Json → GenSeqExcept Json) := .ofList [
  ("ready", ready),
  ("gen", gen),
  ("sum", sum),
  ("eval", eval)
]

def errorToJson (e : String) : Json := Json.mkObj [("status", false), ("error", e)]

def okToJson (r : Json) : Json := Json.mkObj [
  ("status", true),
  ("result", r),
  ("error", Json.null)
]

def process_json (obj : Json) : GenSeqExcept Json := do
  let command ← obj.getObjValAs? String "cmd" |>.mapError (s!"missing cmd: {·}")
  let some commandFun := Commands.get? command |
    ExceptT.mk <| pure (Except.error s!"wrong command: {command}")
  let args ← obj.getObjValAs? Json "args" |>.mapError (s!"missing args: {·}")
  commandFun args

def process_data (input : String) : GenSeqState String := do
  let z := Json.parse input |>.map (process_json ·)
  let w ← match z with
  | .ok j => ExceptT.run j
  | .error e => pure <| .error e
  let u ← match w with
  | .ok s => pure <| okToJson s
  | .error e => pure <| errorToJson e
  return s!"{u.compress}\n"

def process_client (socket : Internal.UV.TCP.Socket) : GenSeqState UInt32 := do
  while true do
    let reader_task := (← socket.recv? 65536).result!
    let e ← reader_task.map (fun t => do
      match t with
      | .ok none =>
        IO.println s!"client disconnected: {← socket.getPeerName}"
        return (some 0)
      | .ok (some u) =>
        match String.fromUTF8? u with
        | some text =>
          IO.println s!"got data: {text.trimRight}"
          let output ← process_data text
          match (← socket.send <| String.toUTF8 output).result!.get with
          | .ok _ => return none
          | .error e =>
            IO.println s!"got error while writing: {e}"
            return (some 1)
        | none =>
          IO.println "got data but not utf8"
          return (some 1)
      | .error v =>
        IO.println s!"got error while reading: {v}"
        return (some 1)
    ) |>.get
    if let some x := e then
      return x
  return 0

def run_server (port : Nat) : GenSeqState UInt32 := do
  let socket ← Internal.UV.TCP.Socket.new
  let addr := IPv4Addr.ofString "0.0.0.0" |>.getD default
  let endpoint := SocketAddress.v4 {addr := addr, port := port}
  socket.bind endpoint
  socket.listen 1
  IO.println s!"Ready on port {port}"
  while true do
    let conn ← socket.accept
    let result := conn.result!
    let _ ← Task.get <| result.map (fun t => do
      match t with
      | .ok s =>
        IO.println s!"client connected: {← s.getPeerName}"
        let state ← read
        let _u ← IO.asTask (
          GenSeqState.run (process_client s) state.env state.ctx state.state
        )
      | .error e =>
        IO.println s!"client connection error: {e}"
    )
  return 0

unsafe
def run (p : Parsed) : IO UInt32 := do
  let modules := #[`GenSeq]
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules (modules.map ({module := ·})) {} (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := {fileName := "", fileMap := default}
  let state : Core.State := {env}
  let port := p.flag? "port" |>.map (·.as! Nat) |>.getD 8000
  GenSeqState.run (run_server port) env ctx state

unsafe
def cmd : Cmd := `[Cli|
  "genseq" VIA run; ["0.1.0"]
  "Generate a Lean definition from the synthetic DSL.

  Requests: {\"name\": String, \"offset\": Nat, \"source\": String}
  Responses:
    - {\"status\": true, \"lean\": String}
    - {\"status\": false, \"error\": String}
  "

  FLAGS:
    p, port : Nat;      "Listen at port <port> (default: 8000)"
]

unsafe
def main (args : List String) : IO UInt32 := do
  cmd.validate args
