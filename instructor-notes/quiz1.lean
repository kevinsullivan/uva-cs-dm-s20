def s1 := "Hello, "
def s2 := "Lean!"
def s3 := "Hello, Lean!"

theorem t1 : s1 ++ s2 = s3 := eq.refl "Hello, Lean!"

theorem t2 : 4 * 4 = 16 := eq.refl 16

def square : ℕ → ℕ 
| n := n^2

theorem t3 : s1 ++ s2 = s3 ∧ square 5 = 25 := 
and.intro t1 (eq.refl 25)

theorem t4 : (s1 ++ s2 = s3 ∧ square 5 = 25) → (square 5 = 25)  :=
λ h, h.right