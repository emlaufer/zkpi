axiom em_eff : ∀ (p : Prop), p ∨ ¬p

def demorganAndForward {p q: Prop} : ¬(p ∧ q) → (¬p ∨ ¬q) :=
begin
  intros h,
  apply or.elim (em_eff p),
  intro hp,
  let nq := λ hq, h (and.intro hp hq),
  exact or.intro_right _ nq,
  intro hnp,
  exact or.intro_left _ hnp,
end

def demorganAndBackward {p q : Prop} : (¬p ∨ ¬q) → ¬(p ∧ q) :=
begin
  intro h,
  apply or.elim h,
  intro np,
  exact (λ hpq, np (and.elim_left hpq)),
  intro nq,
  exact (λ hpq, nq (and.elim_right hpq)),
end

def demorganAnd {p q : Prop} : ¬(p ∧ q) ↔ (¬p ∨ ¬q) :=
  iff.intro demorganAndForward demorganAndBackward

def demorganOrForward {p q : Prop} : ¬(p ∨ q) → (¬p ∧ ¬q) :=
begin
  intros h,
  apply or.elim (em_eff p),
  intro hp,
  exact absurd (or.intro_left _ hp) h,
  intro np,
  apply or.elim (em_eff q),
  intro hq,
  exact absurd (or.intro_right _ hq) h,
  intro nq,
  exact and.intro np nq,
end

def demorganOrBackward {p q : Prop} : (¬p ∧ ¬q) → ¬(p ∨ q)  :=
begin
  intro h,
  let np := and.elim_left h,
  let nq := and.elim_right h,
  exact (λ porq, or.elim porq (λ hp, absurd hp np) (λ hq, absurd hq nq)),
end

def demorganOr {p q : Prop} : ¬(p ∨ q) ↔ (¬p ∧ ¬q) :=
  iff.intro demorganOrForward demorganOrBackward

def demorgan {p q : Prop} : (¬(p ∨ q) ↔ (¬p ∧ ¬q)) ∧  (¬(p ∧ q) ↔ (¬p ∨ ¬q)) :=
  and.intro demorganOr demorganAnd