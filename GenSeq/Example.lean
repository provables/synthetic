import GenSeq

open Synth

def p (x : ℤ) : ℤ :=
  loop2
    (fun x y => (((y / 2) * y) % 2) + x)
    (fun _ y => y / 2)
    x 0 x

theorem p_eq_zero_of_pow (n : ℕ) : p (2 ^ n) = 0 := by
  simp [p]
  have : ∀ u, loop2
      (fun x y ↦ (((y / 2) * y) % 2) + x)
      (fun x y ↦ y / 2)
      u 0 0 = 0 := by
    intro u
    match u with
    | .negSucc _ => reduce; rfl
    | .ofNat u =>
      induction u with
      | zero => reduce; rfl
      | succ n ih =>
        simp
        unfold loop2
        exact ih

  have : ∀ m u, loop2
      (fun x y ↦ (((y / 2) * y) % 2) + x)
      (fun x y ↦ y / 2)
      u 0 (2 ^ m) = 0 := by
    intro m u
    match u with
    | .negSucc _ => reduce; rfl
    | .ofNat u =>
      induction u generalizing m with
      | zero => reduce; rfl
      | succ m' ih =>
        simp
        unfold loop2
        have t1 : (2 : ℤ) ^ m / 2 * 2 ^ m % 2 = 0 := by
          cases m with
          | zero => simp
          | succ u =>
            simp
            exact Dvd.dvd.mul_left (by exact dvd_pow_self (2 : ℤ) (by linarith)) _
        by_cases hhm : m = 0
        · simp [hhm]
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
  comprN (fun x =>
    loop2
      (fun x y => (((y / 2) * y) % 2) + x)
      (fun _ y => y / 2)
      x 0 x
  ) x

def g2 (x : ℕ) : ℤ :=
  comprP (fun x =>
    loop2
      (fun x y => (((y / 2) * y) % 2) + x)
      (fun _ y => y / 2)
      x 0 x
  ) bound bound_spec x

theorem g2_zero : g2 0 = 0 := by
  decide

theorem g2_three : g2 3 = 4 := by
  decide

theorem g_zero : g 0 = 0 := by
  decide +kernel

theorem g_three : g 3 = 4 := by
  decide +kernel
