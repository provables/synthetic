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

mutual
inductive F
  -- λ(x, y).a
  | Lam (t : T)
  deriving Repr

inductive T
  | Atom (a : Atom)
  | Fun (f : T)
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

partial def toT : TSyntax `oeis_synth → Option T
  | `(oeis_synth| $n:num) =>
    match n.getNat with
    | 0 => T.Atom .Zero
    | 1 => T.Atom .One
    | 2 => T.Atom .Two
    | _ => none
  | `(oeis_synth| x) => T.Atom .X
  | `(oeis_synth| y) => T.Atom .Y
  | `(oeis_synth| $a + $b) => do T.Add (← toT a) (← toT b)
  | `(oeis_synth| $a - $b) => do T.Sub (← toT a) (← toT b)
  | `(oeis_synth| $a * $b) => do T.Mul (← toT a) (← toT b)
  | `(oeis_synth| $a div $b) => do T.Div (← toT a) (← toT b)
  | `(oeis_synth| $a mod $b) => do T.Mod (← toT a) (← toT b)
  | `(oeis_synth| if $a ≤ $n then $b else $c) =>
    match n.getNat with
    | 0 => do T.Cond (← toT a) (← toT b) (← toT c)
    | _ => none
  | `(oeis_synth| loop(\(x,y).$f,$a,$b)) => do T.Loop (.Lam (← toT f)) (← toT a) (← toT b)
  | `(oeis_synth| loop2(\(x,y).$f1,\(x,y).$f2,$a,$b,$c)) =>
    do T.Loop2 (.Lam (← toT f1)) (.Lam (← toT f2)) (← toT a) (← toT b) (← toT c)
  | `(oeis_synth| compr(\(x,y).$f,$a)) => do T.Compr (.Lam (← toT f)) (← toT a)
  | `(oeis_synth| ($a)) => toT a
  | _ => none

unsafe def parse (s : String) : Elab.TermElabM T := do
  let env ← getEnv
  let t : Syntax ← Lean.ofExcept (Lean.Parser.runParserCategory env `oeis_synth s)
  let ts := match t with
    | `(oeis_synth| $k) => k
  match toT ts with
  | some result => return result
  | _ => throwError m!"parse error: {s}"

-- #eval do
--   --let stx ← `(OEIS% if (1 + 2) ≤ 0 then (x + y) else 0)
--   --let stx ← `(OEIS% loop(\(x,y).x, (x + y), 1))
--   let s := "x"
--   let z ← parse s
--   dbg_trace (repr z)
