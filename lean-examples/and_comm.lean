theorem and_comm_custom (a b : Prop) : a ∧ b ↔ b ∧ a :=
  iff.intro (and.swap) (and.swap)
  
