def s1 := "Hello, "
def s2 := "Nifty!"
def s3 := s1 ++ s2

theorem t1 : s1 ++ s2 = s3 := _

theorem t2 : 4^2 = 16 := _

theorem t3 : s1 ++ s2 = s3 ∧ 5^2 = 25 := _

theorem t4 : 
    ∀ (P Q R : Prop), (P ∧ Q) ∧ (Q ∧ R) → (P ∧ R) := 
    λ (P Q R : Prop),
        and.intro _ _