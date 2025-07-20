import Mathlib
import Lean.Syntax

open Lean

inductive Atom
  | Zero
  | One
  | Two
  | X
  | Y

mutual
inductive F
  -- λ(x, y).a
  | Lam (t : T)

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
end

declare_syntax_cat oeis_synth (behavior := symbol)

syntax func := "fun" "x" "y" "=>" oeis_synth
syntax num : oeis_synth
syntax "x" : oeis_synth
syntax "y" : oeis_synth
syntax oeis_synth ("+" <|> "-" <|> "*" <|> "/" <|> "mod") oeis_synth : oeis_synth
syntax "if" oeis_synth "≤" num "then" oeis_synth "else" oeis_synth : oeis_synth
syntax "loop1" "(" func ")" oeis_synth oeis_synth : oeis_synth
syntax "loop2" "(" func ")" "(" func ")" oeis_synth oeis_synth oeis_synth : oeis_synth
syntax "compr" "(" func ")" oeis_synth : oeis_synth
syntax "(" oeis_synth ")" : oeis_synth

syntax "OEIS% " oeis_synth : term

macro_rules
  | `(OEIS% $stx) => `(logInfo m!"{OEIS% $stx}")

def loop1 (f : ℤ → ℤ → ℤ) (a : ℤ) (b : ℤ) : ℤ := 0

#eval do
  let stx ← `(OEIS% x)
  dbg_trace (repr stx)
