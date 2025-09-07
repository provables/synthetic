import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Testing.Plausible.Sampleable
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Synth
open Function

@[simp]
def add (a b : ℤ) : ℤ := a + b

@[simp]
def sub (a b : ℤ) : ℤ := a - b

@[simp]
def mul (a b : ℤ) : ℤ := a * b

@[simp]
def div (a b : ℤ) : ℤ := a / b

@[simp]
def mod (a : ℤ) (b : ℤ) : ℤ := a % b

@[simp]
def cond (a b c : ℤ) : ℤ := if a ≤ 0 then b else c

/--
Original semantics from the paper. It uses recursion and it's inefficient.
Use `loop` instead (see theorem about equivalence).
-/
@[simp,reducible]
def loop' (f : ℤ → ℤ → ℤ) (a : ℤ) (b : ℤ) : ℤ :=
  match a with
  | .ofNat 0 => b
  | .ofNat (n + 1) => f (loop' f n b) (n + 1)
  | .negSucc _ => b
termination_by Int.natAbs a

/--
Efficient implementation of `loop`.
-/
@[simp,reducible]
def loop (f : ℤ → ℤ → ℤ) (n : ℤ) (b : ℤ) : ℤ :=
  match n with
  | .ofNat m => List.range' 1 m |>.foldl f b
  | .negSucc _ => b

theorem loop'_eq_loop : loop' = loop := by
  ext h n b
  simp only [loop]
  cases n with
  | ofNat m =>
    induction m with
    | zero =>
      reduce; rfl
    | succ k ih =>
      rw [loop']
      push_cast
      conv at ih =>
        rhs
        reduce
      rw [show Int.ofNat k = ↑k by rfl] at ih
      rw [ih]
      simp
      have : List.range' 1 (k + 1) = List.range' 1 k ++ [k + 1] := by
        nth_rw 2 [show k + 1 = 1 + k by omega]
        apply List.range'_1_concat
      aesop
  | negSucc m =>
    reduce; rfl

@[simp,reducible]
def loop2 (f g : ℤ → ℤ → ℤ) (a : ℤ) (b c : ℤ) : ℤ :=
  match a with
  | .ofNat 0 => b
  | .ofNat (n + 1) => loop2 f g n (f b c) (g b c)
  | .negSucc _ => b
termination_by Int.natAbs a

@[simp,reducible]
def loop2' (f g : ℤ × ℤ → ℤ) (a : ℤ) (b : ℤ × ℤ) : ℤ × ℤ :=
  match a with
  | .ofNat 0 => b
  | .ofNat (n + 1) => loop2' f g n (f b, g b)
  | .negSucc _ => b
termination_by Int.natAbs a

theorem loop2_eq_loop2' (f g : ℤ → ℤ → ℤ) (a : ℤ) (b c : ℤ) :
    loop2 f g a b c = (loop2' (uncurry f) (uncurry g) a (b, c)).1 := by
  match a with
  | .negSucc _ => reduce; rfl
  | .ofNat a =>
    simp
    induction a generalizing b c with
    | zero => reduce; rfl
    | succ _ ih =>
      simp
      unfold loop2 loop2'
      exact ih _ _

theorem loop2'_rec (f g : ℤ × ℤ → ℤ) (n : ℕ) (b : ℤ × ℤ) :
    loop2' f g (n + 1) b = (f (loop2' f g n b), g (loop2' f g n b)) := by
  induction n generalizing b with
  | zero => reduce; rfl
  | succ m ih => unfold loop2'; exact ih _

example (n : ℕ) : Int.ofNat (n + 1) = n + 1 := rfl

@[simp]
theorem loop2_out (f g : ℤ → ℤ → ℤ) (a : ℤ) (b c : ℤ) :
    loop2 f g a b c = b ∨ ∃ b' c', loop2 f g a b c = f b' c' := by
  match a with
  | .negSucc _ => reduce; left; rfl
  | .ofNat 0 => reduce; left; rfl
  | .ofNat (n + 1) =>
    rw [loop2_eq_loop2', show Int.ofNat (n + 1) = n + 1 by rfl, loop2'_rec]
    let (u, v) := loop2' (uncurry f) (uncurry g) n (b, c)
    right
    use u, v
    simp

def N : ℕ := 1000

@[reducible]
def comprN (f : ℤ → ℤ) (a : ℤ) : ℤ :=
  match a with
  | .negSucc _ => 0
  | .ofNat 0 => List.range N |>.find? (f · ≤ 0) |>.getD N
  | .ofNat (n + 1) =>
    let x := comprN f n
    List.range N |>.find? (fun (i : ℕ) => x < i ∧ f i ≤ 0) |>.getD N
termination_by Int.natAbs a

@[reducible]
def comprP (f : ℤ → ℤ) (b : ℤ → ℕ) (hb : ∀ n : ℕ, n < b n ∧ f (b n) ≤ 0) (a : ℤ) : ℤ :=
  match a with
  | .negSucc _ => 0
  | .ofNat 0 => List.range (b 0) |>.find? (f · ≤ 0) |>.getD (b 0)
  | .ofNat (n + 1) =>
    let x := comprP f b hb n
    let N := b x
    List.range N |>.find? (fun (i : ℕ) => x < i ∧ f i ≤ 0) |>.getD N
termination_by Int.natAbs a

end Synth
