import Mathlib

namespace Synth

def add (a b : ℤ) : ℤ := a + b

def sub (a b : ℤ) : ℤ := a - b

def mul (a b : ℤ) : ℤ := a * b

def div (a b : ℤ) : ℤ := a / b

def mod (a : ℤ) (b : ℤ) : ℤ := a % b

def cond (a b c : ℤ) : ℤ := if a ≤ 0 then b else c

def loop (f : ℤ → ℤ → ℤ) (a : ℕ) (b : ℤ) : ℤ :=
  match a with
  | 0 => b
  | n + 1 => f (loop f n b) (n + 1)

def loop2 (f g : ℤ → ℤ → ℤ) (a : ℕ) (b c : ℤ) : ℤ :=
  match a with
  | 0 => b
  | n + 1 =>
    loop2 f g n (f b c) (g b c)

theorem loop2_out (f g : ℤ → ℤ → ℤ) (a : ℕ) (b c : ℤ) :
    loop2 f g a b c = b ∨ ∃ b' c', loop2 f g a b c = f b' c' := by
  match a with
  | 0 =>
    left
    simp [loop2]
  | n + 1 =>
    right
    induction n generalizing (b : ℤ) (c : ℤ) with
    | zero =>
      use b, c
      simp [loop2]
    | succ n ih =>
      have := ih (f b c) (g b c)
      obtain ⟨u, hu⟩ := this
      obtain ⟨v, hv⟩ := hu
      unfold loop2
      use u, v

def N : ℕ := 1000

def compr (f : ℕ → ℤ → ℤ) (a : ℕ) : ℤ :=
  match a with
  | 0 => List.range N |>.find? (f · 0 ≤ 0) |>.getD N
  | n + 1 => List.range N |>.find? (fun (i : ℕ) => compr f n < i ∧ f i 0 ≤ 0) |>.getD N

def compr4 (f : ℕ → ℤ) (b : ℤ → ℕ) (hb : ∀ n : ℕ, n < b n ∧ f (b n) ≤ 0) (a : ℕ) : ℤ :=
  match a with
  | 0 => List.range (b 0) |>.find? (f · ≤ 0) |>.getD (b 0)
  | n + 1 =>
    let N := b (compr4 f b hb n)
    List.range N |>.find? (fun (i : ℕ) => compr4 f b hb n < i ∧ f i ≤ 0) |>.getD N

def p (x : ℕ) : ℤ :=
  loop2
    (fun x y => add (mod (mul (div y 2) y) 2) x)
    (fun _ y => div y 2)
    x 0 x

theorem spam1 (n : ℕ) : p (2 ^ n) = 0 := by
  simp [p]
  have : ∀ u, loop2
      (fun x y ↦ add (mod (mul (div y 2) y) 2) x)
      (fun x y ↦ div y 2)
      u 0 0 = 0 := by
    intro u
    induction u with
    | zero => simp [loop2]
    | succ n ih =>
      simp [loop2, add, mod, mul, div]
      exact ih
  have : ∀ m u, loop2
      (fun x y ↦ add (mod (mul (div y 2) y) 2) x)
      (fun x y ↦ div y 2)
      u 0 (2 ^ m) = 0 := by
    intro m u
    induction u generalizing m with
    | zero => simp [loop2]
    | succ m' ih =>
      simp [loop2]
      have t1 : add (mod (mul (div (2 ^ m) 2) (2 ^ m)) 2) 0 = 0 := by
        simp [add, mod, mul, div]
        by_cases hm : m = 0
        · rw [hm]
          simp
        · exact Dvd.dvd.mul_left (by exact dvd_pow_self (2 : ℤ) hm) _
      by_cases hhm : m = 0
      · simp [hhm, div, add, mod, mul]
        exact this m'
      · have t2 : div (2 ^ m) 2 = 2 ^ (m - 1) := by
          simp [div]
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
    have : p (2 ^ n) = 0 := spam1 n
    linarith

-- https://github.com/Anon52MI4/oeis-alien
-- A3714: compr (loop2 ((((y div 2) * y) mod 2) + x) (y div 2) x 0 x) x
def g (x : ℕ) : ℤ :=
  compr (fun x _ =>
    loop2
      (fun x y => add (mod (mul (div y 2) y) 2) x)
      (fun _ y => div y 2)
      x 0 x
  ) x

def g2 (x : ℕ) : ℤ :=
  compr4 (fun x =>
    loop2
      (fun x y => add (mod (mul (div y 2) y) 2) x)
      (fun _ y => div y 2)
      x 0 x
  ) bound bound_spec x

theorem fooA : g2 0 = 0 := by
  decide

theorem foo : g 0 = 0 := by
  decide +kernel

theorem foo2 : g 3 = 4 := by
  decide +kernel

#find_syntax "↑"
#print foo
macro "foo" : command =>
  `(#print $(Lean.mkCIdent (.num `GenSeq.Semantics._auxLemma 2)))
foo
#explode Semigroup.mul_assoc
#explode iff_of_true
#eval g 0
#eval g 1
#eval g 2
#eval g 3
#eval g 4
#eval g 5

end Synth
