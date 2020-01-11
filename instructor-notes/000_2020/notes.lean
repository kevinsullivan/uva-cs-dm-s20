axiom Swan : Type
axiom White : Swan → Prop
#check ∀ (s : Swan), White s


axiom Object : Type
axiom isSwan : Object → Prop
axiom isWhite : Object → Prop
#check ∀ s, isSwan s → isWhite s

 