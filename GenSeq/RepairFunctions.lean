import Std
import Lean

open Std Lean Elab Command Syntax

def WrongIdentifiers := HashMap.ofList [
  (`Nat.length, `Nat.card),
  (`Nat.primes, `Nat.Primes),
  (`Nat.prime, `Nat.Primes),
  (`Nat.Prime, `Nat.Primes),
  (`Nat.factors, `Nat.divisors),
  (`Nat.primeSeq, `Nat.divisors),
  (`Nat.Factors, `Nat.divisors),
  (`Nat.primes.stream, `Nat.Primes)
]

def Regexes : HashMap String String := ∅

def _repairIdentifiers (dictionary : HashMap Name Name) (orig : Syntax) :
    CommandElabM (Syntax × Nat) := do
  StateT.run (replaceM (λ s ↦ do
    match s with
    | `(term|$n:ident) =>
      let some hit := dictionary.get? n.getId | return none
      modify (· + 1)
      `(term|$(mkIdent hit):ident)
    | _ => return none
  ) orig) 0

def repairIdentifiers : Syntax → CommandElabM (Syntax × Nat) := _repairIdentifiers WrongIdentifiers
