import Lean
import Qq
import Sequencelib.Meta.Synthetic
import Sequencelib.Meta.Codomain

open Synth
open Lean Expr Elab Term Tactic Meta Qq Syntax Command
open Lean.Parser.Command
open System

def hashSetEq {α : Type} [BEq α] [Hashable α] (s t : Std.HashSet α) : Bool :=
  s.all (t.contains ·) && t.all (s.contains ·)

structure SeqInfo where
  cod : Codomain
  deriving Repr

instance : Inhabited SeqInfo where
  default := ⟨.Int⟩

structure ProcessState where
  freeVars : Array (Std.HashSet Name)
  safeCtx : Bool
  seqInfo : Std.HashMap Name SeqInfo
  doValidation : Bool

instance : Inhabited ProcessState where
  default := ⟨#[∅], default, default, true⟩

abbrev ProcessM (α : Type) := StateT ProcessState TermElabM α

def ProcessM.run {α : Type} (x : ProcessM α) (s : ProcessState := default) : TermElabM α :=
  StateT.run' x s

def newFreeVars : ProcessM Unit := do
  let state ← get
  let new_state := {state with freeVars := state.freeVars.push ∅}
  StateT.set new_state

def closeFreeVars : ProcessM Unit := do
  let state ← get
  let new_state := {state with freeVars := state.freeVars.pop}
  StateT.set new_state

def pushFreeVar (v : Name) : ProcessM Unit := do
  let state ← get
  let curCtx := state.freeVars.back!
  let new_state := {state with freeVars := state.freeVars.pop.push <| curCtx.insert v}
  StateT.set new_state

def popFreeVars : ProcessM (Std.HashSet Name) := do
  let state ← get
  return state.freeVars.back!

def setSafe : ProcessM Unit := do
  StateT.set {(← get) with safeCtx := true}

def setUnsafe : ProcessM Unit := do
  StateT.set {(← get) with safeCtx := false}

def clearFreeVars : ProcessM Unit := do
  StateT.set {(← get) with freeVars := ∅}

partial def processTerm (term : TSyntax `term) : ProcessM (TSyntax `term) := do
  --dbg_trace s!"term: {term}"
  match term with
  | `(term|($n:num)) =>
    --dbg_trace s!"--- (num): {n}"
    setSafe
    `(term|$n)
  | tz@`(term|$_:num) =>
    --dbg_trace s!"--- num: {n}"
    pure tz
  | `(term|($ti:ident)) =>
    --dbg_trace s!"--- (ident) := {ti}"
    let t ← processTerm ti
    setSafe
    `(term|$t)
  | `(term|($t:term)) =>
    --dbg_trace s!"--- (term)"
    let p := (← get).safeCtx
    let t2 ← processTerm t
    if p then
      `(term|$t2)
    else
      if (← get).safeCtx then
        `(term|$t2)
      else
        setSafe
        `(term|($t2))
  | `(term|$n:num + $m:num) =>
    --dbg_trace s!"--- sum_num := {n} + {m}"
    setSafe
    `(term|$(mkNatLit (n.getNat + m.getNat)))
  | `(term|$a + $b) =>
    --dbg_trace s!"--- sum"
    setUnsafe
    let t1 ← processTerm a
    let t2 ← processTerm b
    setUnsafe
    if a == (← `(term|0)) then
      `(term|$t2)
    else if b == (← `(term|0)) then
      `(term|$t1)
    else
      `(term|$t1 + $t2)
  | `(term|$a - $b) =>
    --dbg_trace s!"--- sub"
    setUnsafe
    let t1 ← processTerm a
    let t2 ← processTerm b
    setUnsafe
    if a == (← `(term|0)) then
      `(term|(-$t2))
    else if b == (← `(term|0)) then
      `(term|$t1)
    else
      `(term|$t1 - $t2)
  | `(term|$a * $b) =>
    --dbg_trace s!"--- mul"
    setUnsafe
    let t1 ← processTerm a
    let t2 ← processTerm b
    setUnsafe
    if a == (← `(term|0)) || b == (← `(term|0)) then
      `(term|0)
    else if a == (← `(term|1)) then
      `(term|$t2)
    else if b == (← `(term|1)) then
      `(term|$t1)
    else
      `(term|$t1 * $t2)
  | `(term|$a / $b) =>
    --dbg_trace s!"--- div"
    setUnsafe
    let t1 ← processTerm a
    let t2 ← processTerm b
    setUnsafe
    if b == (← `(term|1)) then
      `(term|$t1)
    else
      `(term|$t1 / $t2)
  | `(term|$a % $b) =>
    --dbg_trace s!"--- mod"
    setUnsafe
    let t1 ← processTerm a
    let t2 ← processTerm b
    setUnsafe
    `(term|$t1 % $t2)
  | `(term|if $t:term ≤ 0 then $a:term else $b:term) =>
    --dbg_trace s!"--- if"
    setUnsafe
    let t1 ← processTerm t
    setSafe
    let ta ← processTerm a
    setSafe
    let tb ← processTerm b
    `(term|if $t1 ≤ 0 then $ta else $tb)
  | `(term|λ(x y : $_:term) ↦ $t:term) =>
    --dbg_trace "--- fun"
    setSafe
    newFreeVars
    let t1 ← processTerm t
    let f1 ← popFreeVars
    closeFreeVars
    if hashSetEq f1 {`x} then
      `(term|λ($(mkIdent `x) $(mkIdent `_y)) ↦ $t1)
    else if hashSetEq f1 {`y} then
      `(term|λ($(mkIdent `_x) $(mkIdent `y)) ↦ $t1)
    else if hashSetEq f1 {`x, `y} then
      `(term|λ($(mkIdent `x) $(mkIdent `y)) ↦ $t1)
    else
      `(term|λ($(mkIdent `_x) $(mkIdent `_y)) ↦ $t1)
  | `(term|λ(x : $_:term) ↦ $t:term) =>
    setSafe
    newFreeVars
    let t1 ← processTerm t
    let f ← popFreeVars
    closeFreeVars
    if hashSetEq f {`x} then
      `(term|λ($(mkIdent `x)) ↦ $t1)
    else
      `(term|λ($(mkIdent `_x)) ↦ $t1)
  | `(term|loop $f $a $b) =>
    --dbg_trace s!"--- loop"
    setUnsafe
    let tf ← processTerm f
    setUnsafe
    let ta ← processTerm a
    setUnsafe
    let tb ← processTerm b
    `(term|$(mkIdent `loop) $tf $ta $tb)
  | `(term|loop2 $f1 $f2 $a $b $c) =>
    --dbg_trace s!"--- loop2"
    setUnsafe
    let tf1 ← processTerm f1
    setUnsafe
    let tf2 ← processTerm f2
    setUnsafe
    let ta ← processTerm a
    setUnsafe
    let tb ← processTerm b
    setUnsafe
    let tc ← processTerm c
    `(term|$(mkIdent `loop2) $tf1 $tf2 $ta $tb $tc)
  | `(term|comprN $f $t) =>
    setUnsafe
    let tf ← processTerm f
    setUnsafe
    let t1 ← processTerm t
    `(term|$(mkIdent `comprN) $tf $t1)
  | `(term|x) =>
    --dbg_trace s!"--- x := x"
    pushFreeVar `x
    `(term|$(mkIdent `x))
  | `(term|y) =>
    --dbg_trace s!"--- y := y"
    pushFreeVar `y
    `(term|$(mkIdent `y))
  | _ =>
    --dbg_trace s!"--- default := {s}"
    pure term

def processCodomain (c : Codomain) (_cod: TSyntax `term) (body : TSyntax `term)
    : ProcessM <| TSyntax `term × TSyntax `term:= do
  match c with
  | .Nat => do
    match body with
    | `(term|Int.toNat <| $_:term) =>
      return (← `(term|ℕ), body)
    | _ =>
      return (← `(term|ℕ), ← `(term|$(mkIdent `Int.toNat) <| $body))
  | .Int => do return (← `(term|ℤ), body)

def processLet (let_t : TSyntax `term) (body : TSyntax `term) :
    ProcessM <| (TSyntax `ident) × (TSyntax `term) := do
  match let_t with
  | `(term|n - $m:num) =>
    if m.getNat == 0 then
      return (← `(ident|$(mkIdent `x)), body)
    else
      return (← `(ident|$(mkIdent `n)), ← `(term|let $(mkIdent `x) := $let_t
        $body
      ))
  | _ =>
  return (← `(ident|$(mkIdent `n)), body)

def processDef (definition : TSyntax `Lean.Parser.Command.definition) :
    ProcessM <| TSyntax `Lean.Parser.Command.definition := do
  let x ← match definition with
  | `(definition|def $a:ident ($_e:ident : $b:term) : $t:term :=
        let $_ti:ident := $tt:term
        $rr:term) =>
      let info := (← get).seqInfo[a.getId]?.getD default
      let new_rr ← processTerm rr
      let (new_t, new_body) ← processCodomain info.cod t new_rr
      let (new_ident, new_body') ← processLet tt new_body
      `(definition|def $a:declId ($new_ident:ident : $b:term) : $new_t:term :=
        $new_body':term)
  | `(definition|def $a:ident ($e:ident : $b:term) : $t:term :=
        $tt:term) =>
      let info := (← get).seqInfo[a.getId]?.getD default
      let new_tt ← processTerm tt
      let (new_t, new_body) ← processCodomain info.cod t new_tt
      `(definition|def $a:declId ($e:ident : $b:term) : $new_t:term :=
        $new_body:term)
  | s => pure s
  return x

def fixFormatting (s : String) : String :=
  let y := (s.splitOn "\n").flatMap (fun line =>
    if line.startsWith "/-!" then
      ["/-!", line.drop 3]
    else if line.startsWith "@[OEIS" then
      [", ".intercalate
        (line.splitOn "," |>.map (fun word => " := ".intercalate (word.splitOn ":=")))]
    else
      [line]
  )
  "\n".intercalate y

def renameDef (orig : TSyntax `Lean.Parser.Command.declaration) (name : Name)
    : TermElabM <| TSyntax `Lean.Parser.Command.declaration := do
  let cursor := Syntax.Traverser.fromSyntax orig
  let c := cursor.down 1 |>.down 1
  let u := c.setCur (← `(declId|$(mkIdent name)))
  return ⟨u.up.up.cur⟩

def clearModifiers (decl : TSyntax `Lean.Parser.Command.declaration) :
    TermElabM <| TSyntax `Lean.Parser.Command.declaration := do
  let cursor := Syntax.Traverser.fromSyntax decl
  let cursor := cursor.down 0 |>.setCur (← `(declModifiersT|))
  return ⟨cursor.up.cur⟩

def progressPath (fpath : FilePath) : FilePath :=
  let fpath := fpath.normalize
  fpath.parent.getD "/" |>.join "progress" |>.join <| fpath.fileStem.getD default

def backupPath (fpath : FilePath) : FilePath :=
  let fpath := fpath.normalize.addExtension "bak"
  fpath.parent.getD "/" |>.join "backup" |>.join <| fpath.fileName.getD default

def processStateFromJson (fpath : FilePath) : IO ProcessState := do
  let f ← IO.FS.readFile fpath
  let .ok j := Json.parse f | throw <| IO.Error.mkInvalidArgument 1 "json parse failed"
  let m : RBMap String Json _ ← IO.ofExcept <| RBMap.fromJson? j (cmp := compare)
  let mut seqInfo : Std.HashMap Name SeqInfo := ∅
  for (k, v) in m do
    let w ← IO.ofExcept <| v.getObjValAs? (Array String) "keywords"
    seqInfo := seqInfo.insert k.toName (if "sign" ∈ w then ⟨.Int⟩ else ⟨.Nat⟩)
  return {(default : ProcessState) with seqInfo := seqInfo}
