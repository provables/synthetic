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

def N : ℕ := 100000

def compr (f : ℕ → ℤ → ℤ) (a : ℕ) : ℤ :=
  match a with
  | 0 => List.range N |>.find? (f · 0 ≤ 0) |>.getD N
  | n + 1 => List.range N |>.find? (fun (i : ℕ) => compr f n < i ∧ f i 0 ≤ 0) |>.getD N

-- compr (loop2 ((((y div 2) * y) mod 2) + x) (y div 2) x 0 x) x
def g (x : ℕ) : ℤ :=
  compr (fun x _ =>
    loop2
      (fun x y => add (mod (mul (div y 2) y) 2) x)
      (fun _ y => div y 2)
      x 0 x
  ) x

#eval g 0
#eval g 1
#eval g 2
#eval g 3
#eval g 4
#eval g 5

end Synth
