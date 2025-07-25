import Mathlib

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

@[simp]
def loop (f : ℤ → ℤ → ℤ) (a : ℕ) (b : ℤ) : ℤ :=
  match a with
  | 0 => b
  | n + 1 => f (loop f n b) (n + 1)

@[simp]
def loop2 (f g : ℤ → ℤ → ℤ) (a : ℕ) (b c : ℤ) : ℤ :=
  match a with
  | 0 => b
  | n + 1 =>
    loop2 f g n (f b c) (g b c)

@[simp]
def loop2' (f g : ℤ × ℤ → ℤ) (a : ℕ) (b : ℤ × ℤ) : ℤ × ℤ :=
  match a with
  | 0 => b
  | n + 1 =>
    loop2' f g n (f b, g b)

theorem loop2_eq_loop2' (f g : ℤ → ℤ → ℤ) (a : ℕ) (b c : ℤ) :
    loop2 f g a b c = (loop2' (uncurry f) (uncurry g) a (b, c)).1 := by
  induction a generalizing b c with
  | zero => simp
  | succ _ ih => simp; exact ih _ _

theorem loop2'_rec (f g : ℤ × ℤ → ℤ) (n : ℕ) (b : ℤ × ℤ) :
    loop2' f g (n + 1) b = (f (loop2' f g n b), g (loop2' f g n b)) := by
  induction n generalizing b with
  | zero => simp
  | succ m ih => unfold loop2'; exact ih _

@[simp]
theorem loop2_out (f g : ℤ → ℤ → ℤ) (a : ℕ) (b c : ℤ) :
    loop2 f g a b c = b ∨ ∃ b' c', loop2 f g a b c = f b' c' := by
  match a with
  | 0 => left; simp
  | n + 1 =>
    right
    rw [loop2_eq_loop2', loop2'_rec]
    let (u, v) := loop2' (uncurry f) (uncurry g) n (b, c)
    use u, v
    simp

def N : ℕ := 1000

def comprN (f : ℤ → ℤ) (a : ℕ) : ℤ :=
  match a with
  | 0 => List.range N |>.find? (f · ≤ 0) |>.getD N
  | n + 1 => List.range N |>.find? (fun (i : ℕ) => comprN f n < i ∧ f i ≤ 0) |>.getD N

def comprP (f : ℤ → ℤ) (b : ℤ → ℕ) (hb : ∀ n : ℕ, n < b n ∧ f (b n) ≤ 0) (a : ℕ) : ℤ :=
  match a with
  | 0 => List.range (b 0) |>.find? (f · ≤ 0) |>.getD (b 0)
  | n + 1 =>
    let N := b (comprP f b hb n)
    List.range N |>.find? (fun (i : ℕ) => comprP f b hb n < i ∧ f i ≤ 0) |>.getD N

end Synth
