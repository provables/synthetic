import Lean
import Cli
import GenSeq

open Lean Elab Term Cli Synth
open Std Net

def runExcept {e a : Type} {m : Type → Type} [Monad m] (x : Except e (m (Except e a))) :
    m (Except e a) := do
  match x with
  | .error err => pure (Except.error err)
  | .ok result => pure (← result)

def process_json (obj : Json) : TermElabM (Except String Json) := do
  let data := do
    let name ← obj.getObjValAs? String "name"
    let offst ← obj.getObjValAs? Nat "offset"
    let source ← obj.getObjValAs? String "source"
    let x := DSLToLean name source offst >>= (fun o =>
      let u := o.map (fun v =>
        let j := Json.mkObj [
          ("status", Json.bool true),
          ("lean", v),
          ("error", Json.null)
        ]
        j)
      pure u)
    return x
  return (← runExcept data)

def process_data (input : String) : TermElabM String := do
  let x ← runExcept <| Lean.Json.parse input >>= (fun r => pure <| process_json r)
  let y := match x with
  | .ok s => s
  | .error s =>
    Json.mkObj [
      ("status", Json.bool false),
      ("error", s)
    ]
  return s!"{y}"

run_elab do
  let x ← process_data r#"{"name": "foo", "offset": 2, "source": "x"}"#
  dbg_trace s!"{x}"
  -- let y ← f
  -- dbg_trace s!"{y}"
  -- dbg_trace "after"

def process_client (socket : Internal.UV.TCP.Socket) : TermElabM UInt32 := do
  while true do
    let d ← socket.recv? 65536
    let reader_task := d.result!
    let e ← reader_task.map (fun t => do
      match t with
      | .ok none =>
        IO.println "end of connection"
        return (some 0)
      | .ok (some u) =>
        match String.fromUTF8? u with
        | some text =>
          IO.println s!"got data: {text}"

          match process_data text with
          | .error s =>
            IO.println s!"error while processing: {s}"
            return (some 1)
          | .ok s =>
            match (← socket.send <| String.toUTF8 s).result!.get with
            | .ok _ => return none
            | .error e =>
              IO.println s!"got error while writing: {e}"
              return (some 1)

          -- let parsed ← parse text
          -- match parsed with
          -- | .error s =>
          --   IO.println s!"got parser error: {s}"
          --   return (some 1)
          -- | .ok s =>
          --   let response := String.toUTF8 <| TtoLean "foo" 0 s
          --   let o := (← socket.send response).result!
          --   match o.get with
          --   | .ok _ => return none
          --   | .error e =>
          --     IO.println s!"got error while writing: {e}"
          --     return (some 1)
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

def run_server : TermElabM UInt32 := do
  let socket ← Internal.UV.TCP.Socket.new
  let addr := IPv4Addr.ofString "0.0.0.0" |>.getD default
  let endpoint := SocketAddress.v4 {addr := addr, port := 1234}
  socket.bind endpoint
  socket.listen 1
  IO.println "Ready"
  while true do
    let conn ← socket.accept
    let result := conn.result!
    let y ← Task.get <| result.map (fun t => do
      match t with
      | .ok s =>
        IO.println "got connection"
        let x ← process_client s
        IO.println "client finished"
        return x
      | .error e =>
        IO.println s!"client connection error: {e}"
        return 1
    )
    if y ≠ 0 then
      return y
  return 0

unsafe
def run (p : Parsed) : IO UInt32 := do
  let name := p.positionalArg! "name" |>.as! String
  let offst := p.positionalArg! "offset" |>.as! Nat
  let source := p.positionalArg! "source" |>.as! String

  let modules := #[`GenSeq]
  enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules (modules.map ({module := ·})) {} (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := {fileName := "", fileMap := default}
  let state : Core.State := {env}

  let z ← Prod.fst <$> (Meta.MetaM.toIO · ctx state) do
    TermElabM.run' run_server
  return z

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
