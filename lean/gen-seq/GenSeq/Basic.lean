import Mathlib
open Lean

def hello := "world"

declare_syntax_cat arith

syntax num : arith
syntax arith "-" arith : arith
syntax arith "+" arith : arith
syntax "(" arith ")" : arith

partial def denoteArith : TSyntax `arith → Nat
  | `(arith| $x:num) => x.getNat
  | `(arith| $x:arith + $y:arith) => denoteArith x + denoteArith y
  | `(arith| $x:arith - $y:arith) => denoteArith x - denoteArith y
  | `(arith| ($x:arith)) => denoteArith x
  | _ => 0

#check Lean.Parser.runParserCategory
-- You can ignore Elab.TermElabM, what is important for us is that it allows
-- us to use the ``(arith| (12 + 3) - 4)` notation to construct `Syntax`
-- instead of only being able to match on it like this.
def test : Elab.TermElabM Nat := do
  let stx ← `(arith| (12 + 3) - 4)
  let x := "12 + 1"
  let env ← getEnv
  let t : Except String Syntax := Lean.Parser.runParserCategory env `arith x
  let u : Syntax ← Lean.ofExcept t
  let z := match u with
    | `(arith| $x) => x
  pure (denoteArith z)

#eval test -- 11
