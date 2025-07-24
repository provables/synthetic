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
syntax oeis_synth ("+" <|> "-" <|> "*" <|> "/" <|> "mod") oeis_synth : oeis_synth
syntax "if" oeis_synth "≤" num &"then" oeis_synth &"else" oeis_synth : oeis_synth
syntax "loop" "(" func "," oeis_synth "," oeis_synth ")" : oeis_synth
syntax "loop2" "(" func "," func "," oeis_synth "," oeis_synth "," oeis_synth ")" : oeis_synth
syntax "compr" "(" func "," oeis_synth ")" : oeis_synth
syntax "(" oeis_synth ")" : oeis_synth

syntax "OEIS% " oeis_synth : term

 macro_rules
  | `(OEIS% $n:num) =>
    match n.getNat with
    | 0 => `(T.Atom .Zero)
    | 1 => `(T.Atom .One)
    | 2 => `(T.Atom .Two)
    | _ => Macro.throwUnsupported
  | `(OEIS% x) => `(T.Atom .X)
  | `(OEIS% y) => `(T.Atom .Y)
  | `(OEIS% $a + $b) => `(T.Add (OEIS% $a) (OEIS% $b))
  | `(OEIS% $a - $b) => `(T.Sub (OEIS% $a) (OEIS% $b))
  | `(OEIS% $a * $b) => `(T.Mul (OEIS% $a) (OEIS% $b))
  | `(OEIS% $a / $b) => `(T.Div (OEIS% $a) (OEIS% $b))
  | `(OEIS% $a mod $b) => `(T.Mod (OEIS% $a) (OEIS% $b))
  | `(OEIS% if $a ≤ $n then $b else $c) =>
    match n.getNat with
    | 0 => `(T.Cond (OEIS% $a) (OEIS% $b) (OEIS% $c))
    | _ => Macro.throwUnsupported
  | `(OEIS% loop(\(x,y).$f,$a,$b)) => `(T.Loop (.Lam (OEIS% $f)) (OEIS% $a) (OEIS% $b))
  | `(OEIS% loop2(\(x,y).$f1,\(x,y).$f2,$a,$b,$c)) =>
    `(T.Loop2 (.Lam (OEIS% $f1)) (.Lam (OEIS% $f2) (OEIS% $a) (OEIS% $b) (OEIS% $c)))
  | `(OEIS% compr(\(x,y).$f,$a)) => `(T.Compr (.Lam (OEIS% $f) (OEIS% $a)))
  | `(OEIS% ($a)) => `(OEIS% $a)

#eval do
  --let stx ← `(OEIS% if (1 + 2) ≤ 0 then (x + y) else 0)
  let stx ← `(OEIS% loop(\(x,y).x, (x + y), 1))
  let u : Q(T) ← elabTerm stx q(T)
  let v : T ← Meta.evalExpr T q(T) u
  dbg_trace (repr v)
