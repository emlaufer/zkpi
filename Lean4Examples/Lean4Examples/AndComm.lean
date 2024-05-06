theorem and_comm_custom (a b : Prop) : a ∧ b ↔ b ∧ a :=
  Iff.intro (And.symm) (And.symm)
