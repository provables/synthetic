import Mathlib
import Lean.Syntax
import Qq

open Lean Elab Term Syntax Qq

inductive Atom
  | Zero
  | One
  | Two
  | X
  | Y
  deriving Repr

instance : ToString Atom where
  toString
  | .Zero => "0"
  | .One => "1"
  | .Two => "2"
  | .X => "x"
  | .Y => "y"

mutual
inductive F
  -- λ(x, y).a
  | Lam (t : T)
  deriving Repr

inductive T
  | Atom (a : Atom)
  -- t1 + t2
  | Add (t1 t2 : T)
  -- t1 - t2
  | Sub (t1 t2 : T)
  -- t1 × t2
  | Mul (t1 t2 : T)
  -- t1 / t2
  | Div (t1 t2 : T)
  -- t1 % t2
  | Mod (t1 t2 : T)
  -- if t1 ≤ 0 then t2 else t3
  | Cond (t1 t2 t3 : T)
  -- loop(f, t1, t2)
  | Loop (f : F) (t1 t2 : T)
  -- loop2(f, g, t1, t2, t3)
  | Loop2 (f g : F) (t1 t2 t3 : T)
  -- compr(f, t1)
  | Compr (f : F) (t1 : T)
  deriving Repr
end

declare_syntax_cat oeis_synth (behavior := symbol)

syntax func := "\\(x,y)." oeis_synth
syntax num : oeis_synth
syntax "x" : oeis_synth
syntax "y" : oeis_synth
syntax oeis_synth ("+" <|> "-" <|> "*" <|> "div" <|> "mod") oeis_synth : oeis_synth
syntax "if" oeis_synth "≤" num &"then" oeis_synth &"else" oeis_synth : oeis_synth
syntax "loop" "(" func "," oeis_synth "," oeis_synth ")" : oeis_synth
syntax "loop2" "(" func "," func "," oeis_synth "," oeis_synth "," oeis_synth ")" : oeis_synth
syntax "compr" "(" func "," oeis_synth ")" : oeis_synth
syntax "(" oeis_synth ")" : oeis_synth

syntax "OEIS% " oeis_synth : term

partial def toT : TSyntax `oeis_synth → Except String T
  | `(oeis_synth| $n:num) =>
    match n.getNat with
    | 0 => .ok <| T.Atom .Zero
    | 1 => .ok <| T.Atom .One
    | 2 => .ok <| T.Atom .Two
    | n => .error s!"number {n} not supported (needs to be 0, 1, or 2)"
  | `(oeis_synth| x) => .ok <| T.Atom .X
  | `(oeis_synth| y) => .ok <| T.Atom .Y
  | `(oeis_synth| $a + $b) => do .ok <| T.Add (← toT a) (← toT b)
  | `(oeis_synth| $a - $b) => do .ok <| T.Sub (← toT a) (← toT b)
  | `(oeis_synth| $a * $b) => do .ok <| T.Mul (← toT a) (← toT b)
  | `(oeis_synth| $a div $b) => do .ok <| T.Div (← toT a) (← toT b)
  | `(oeis_synth| $a mod $b) => do .ok <| T.Mod (← toT a) (← toT b)
  | `(oeis_synth| if $a ≤ $n then $b else $c) =>
    match n.getNat with
    | 0 => do .ok <| T.Cond (← toT a) (← toT b) (← toT c)
    | _ => .error "only `if T ≤ 0 then T else T` is supported"
  | `(oeis_synth| loop(\(x,y).$f,$a,$b)) => do .ok <| T.Loop (.Lam (← toT f)) (← toT a) (← toT b)
  | `(oeis_synth| loop2(\(x,y).$f1,\(x,y).$f2,$a,$b,$c)) =>
    do .ok <| T.Loop2 (.Lam (← toT f1)) (.Lam (← toT f2)) (← toT a) (← toT b) (← toT c)
  | `(oeis_synth| compr(\(x,y).$f,$a)) => do .ok <| T.Compr (.Lam (← toT f)) (← toT a)
  | `(oeis_synth| ($a)) => toT a
  | r => .error s!"unsupported syntax {r}"

def parse (s : String) : Elab.TermElabM T := do
  let env ← getEnv
  let t : Syntax ← Lean.ofExcept (Lean.Parser.runParserCategory env `oeis_synth s)
  let ts := match t with
    | `(oeis_synth| $k) => k
  match toT ts with
  | .ok result => return result
  | .error msg => throwError m!"parse error: {msg}"

mutual
partial def binOp (indent : ℕ) (t1 t2 : T) (op : String) : String :=
  let s1 := TtoLeanAux indent t1
  let s2 := TtoLeanAux indent t2
  s!"({s1} {op} {s2})"

partial def TtoLeanAux (indent: ℕ) (t : T) : String :=
  match t with
  | .Atom x => s!"{x}"
  | .Add t1 t2 => binOp indent t1 t2 "+"
  | .Sub t1 t2 => binOp indent t1 t2 "-"
  | .Mul t1 t2 => binOp indent t1 t2 "*"
  | .Div t1 t2 => binOp indent t1 t2 "/"
  | .Mod t1 t2 => binOp indent t1 t2 "%"
  | .Cond t1 t2 t3 =>
    let s1 := TtoLeanAux indent t1
    let s2 := TtoLeanAux indent t2
    let s3 := TtoLeanAux indent t3
    s!"if ({s1}) ≤ 0 then ({s2}) else ({s3})"
  | .Loop (.Lam f) t1 t2 =>
    let sf := TtoLeanAux indent f
    let s1 := TtoLeanAux indent t1
    let s2 := TtoLeanAux indent t2
    s!"loop (λ(x y : ℤ) ↦ {sf}) ({s1}) ({s2})"
  | .Loop2 (.Lam f) (.Lam g) t1 t2 t3 =>
    let sf := TtoLeanAux indent f
    let sg := TtoLeanAux indent g
    let s1 := TtoLeanAux indent t1
    let s2 := TtoLeanAux indent t2
    let s3 := TtoLeanAux indent t3
    s!"loop2 (λ(x y : ℤ) ↦ {sf}) (λ(x y : ℤ) ↦ {sg}) ({s1}) ({s2}) ({s3})"
  | .Compr (.Lam f) t1 =>
    let sf := TtoLeanAux indent f
    let s1 := TtoLeanAux indent t1
    s!"comprN (λ(x : ℕ) ↦ {sf}) ({s1})"
end

def TtoLean (name : String) (offst : ℕ) (t : T) : String :=
  s!"def {name} (n : ℕ) : ℤ :=\n  let x := n - {offst}\n  {TtoLeanAux 0 t}"
