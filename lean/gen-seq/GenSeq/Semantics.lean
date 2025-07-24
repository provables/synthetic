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

def comprN (f : ℕ → ℤ → ℤ) (a : ℕ) : ℤ :=
  match a with
  | 0 => List.range N |>.find? (f · 0 ≤ 0) |>.getD N
  | n + 1 => List.range N |>.find? (fun (i : ℕ) => comprN f n < i ∧ f i 0 ≤ 0) |>.getD N

def comprP (f : ℕ → ℤ) (b : ℤ → ℕ) (hb : ∀ n : ℕ, n < b n ∧ f (b n) ≤ 0) (a : ℕ) : ℤ :=
  match a with
  | 0 => List.range (b 0) |>.find? (f · ≤ 0) |>.getD (b 0)
  | n + 1 =>
    let N := b (comprP f b hb n)
    List.range N |>.find? (fun (i : ℕ) => comprP f b hb n < i ∧ f i ≤ 0) |>.getD N

def p (x : ℕ) : ℤ :=
  loop2
    (fun x y => add (mod (mul (div y 2) y) 2) x)
    (fun _ y => div y 2)
    x 0 x

theorem p_eq_zero_of_pow (n : ℕ) : p (2 ^ n) = 0 := by
  simp [p]
  have : ∀ u, loop2
      (fun x y ↦ add (mod (mul (div y 2) y) 2) x)
      (fun x y ↦ div y 2)
      u 0 0 = 0 := by
    intro u
    induction u with
    | zero => simp
    | succ n ih =>
      simp
      exact ih
  have : ∀ m u, loop2
      (fun x y ↦ add (mod (mul (div y 2) y) 2) x)
      (fun x y ↦ div y 2)
      u 0 (2 ^ m) = 0 := by
    intro m u
    induction u generalizing m with
    | zero => simp
    | succ m' ih =>
      simp
      have t1 : (2 : ℤ) ^ m / 2 * 2 ^ m % 2 = 0 := by
        cases m with
        | zero => simp
        | succ u =>
          simp
          exact Dvd.dvd.mul_left (by exact dvd_pow_self (2 : ℤ) (by linarith)) _
      by_cases hhm : m = 0
      · simp [hhm, div, add, mod, mul]
        exact this m'
      · have t2 : ((2 : ℤ) ^ m) / 2 = 2 ^ (m - 1) := by
          norm_cast
          nth_rw 2 [show 2 = 2 ^ 1 by rfl]
          refine Nat.pow_div (by omega) (by linarith)
        rw [t1, t2]
        exact ih _
  exact this _ _

def bound (n : ℤ) : ℕ :=
  if n < 0 then
    0
  else
    2 ^ n.toNat

theorem bound_spec (n : ℕ) : n < bound n ∧ p (bound n) ≤ 0 := by
  constructor
  · unfold bound
    split_ifs
    trivial
    simp
    exact Nat.lt_two_pow_self
  · unfold bound
    split_ifs
    decide
    simp
    have : p (2 ^ n) = 0 := p_eq_zero_of_pow n
    linarith

-- https://github.com/Anon52MI4/oeis-alien
-- A3714: compr (loop2 ((((y div 2) * y) mod 2) + x) (y div 2) x 0 x) x
def g (x : ℕ) : ℤ :=
  comprN (fun x _ =>
    loop2
      (fun x y => add (mod (mul (div y 2) y) 2) x)
      (fun _ y => div y 2)
      x 0 x
  ) x

def g2 (x : ℕ) : ℤ :=
  comprP (fun x =>
    loop2
      (fun x y => add (mod (mul (div y 2) y) 2) x)
      (fun _ y => div y 2)
      x 0 x
  ) bound bound_spec x

theorem fooA : g2 0 = 0 := by
  decide

theorem fooB : g2 3 = 4 := by
  decide

theorem foo : g 0 = 0 := by
  decide +kernel

theorem foo2 : g 3 = 4 := by
  decide +kernel

end Synth
