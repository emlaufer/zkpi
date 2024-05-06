axiom em_eff : ∀ (p : Prop), p ∨ ¬p

def demorganAndForward {p q: Prop} : ¬(p ∧ q) → (¬p ∨ ¬q) :=
by
  intros h
  apply Or.elim (em_eff p)
  intro hp
  let nq := λ hq => h (And.intro hp hq)
  exact Or.intro_right _ nq
  intro hnp
  exact Or.intro_left _ hnp

def demorganAndBackward {p q : Prop} : (¬p ∨ ¬q) → ¬(p ∧ q) :=
by
  intro h
  apply Or.elim h
  intro np
  exact (λ hpq => np (And.left hpq))
  intro nq
  exact (λ hpq => nq (And.right hpq))

def demorganAnd {p q : Prop} : ¬(p ∧ q) ↔ (¬p ∨ ¬q) :=
  Iff.intro demorganAndForward demorganAndBackward

def demorganOrForward {p q : Prop} : ¬(p ∨ q) → (¬p ∧ ¬q) :=
by
  intros h
  apply Or.elim (em_eff p)
  intro hp
  exact absurd (Or.intro_left _ hp) h
  intro np
  apply Or.elim (em_eff q)
  intro hq
  exact absurd (Or.intro_right _ hq) h
  intro nq
  exact And.intro np nq

def demorganOrBackward {p q : Prop} : (¬p ∧ ¬q) → ¬(p ∨ q)  :=
by
  intro h
  let np := And.left h
  let nq := And.right h
  exact (λ porq => Or.elim porq (λ hp => absurd hp np) (λ hq => absurd hq nq))

def demorganOr {p q : Prop} : ¬(p ∨ q) ↔ (¬p ∧ ¬q) :=
  Iff.intro demorganOrForward demorganOrBackward

def demorgan {p q : Prop} : (¬(p ∨ q) ↔ (¬p ∧ ¬q)) ∧  (¬(p ∧ q) ↔ (¬p ∨ ¬q)) :=
  And.intro demorganOr demorganAnd
