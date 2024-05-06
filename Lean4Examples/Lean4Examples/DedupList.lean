noncomputable def add_eff : Nat → Nat → Nat :=
  λ n m => @Nat.rec (λ _ => Nat) n (λ mp prev => Nat.succ prev) m

noncomputable def sub_eff : Nat → Nat → Nat := 
  λ n m => @Nat.rec (λ _ => Nat) n (λ mp prev => @Nat.rec (λ _=> Nat) Nat.zero (λ pprev _ => pprev) prev) m

noncomputable def is_zero : Nat -> Bool :=
  λ n => @Nat.rec (λ _ => Bool) Bool.true (λ np prev => Bool.false) n

noncomputable def is_eq : Nat → Nat → Bool :=
  λ n m => is_zero (sub_eff n m) && is_zero (sub_eff m n)

axiom is_eq_refl (x : Nat) : is_eq x x = Bool.true

noncomputable def mem : Nat -> List Nat -> Bool :=
  λ x l => List.recOn l Bool.false (λ hd tl prev => prev || (is_eq hd x))

def bor_eq_split_ineff {a b : Bool} (h: a || b = Bool.true): a = Bool.true ∨ b = Bool.true :=
by
  simp at h
  exact h

def bor_eq_split {a b : Bool} (h: a || b = Bool.true): a = Bool.true ∨ b = Bool.true :=
by
  cases a
  cases b
  trivial
  exact Or.intro_right _ (Eq.refl Bool.true)
  exact Or.intro_left _ (Eq.refl Bool.true)

def bor_eq_left {a b : Bool} (h: b = Bool.true) : (a || b) = Bool.true :=
by
  cases b
  trivial
  cases a
  trivial
  trivial

def bor_eq_right {a b : Bool} (h: a = Bool.true ) : (a || b) = Bool.true :=
by
  cases a
  trivial
  cases b
  trivial
  trivial

def mem_head : ∀ (hd : Nat) (tl : List Nat), (mem hd (hd :: tl)) = Bool.true :=
  fun hd tl => @bor_eq_left (mem hd tl) (is_eq hd hd) (is_eq_refl hd)

def mem_cons : ∀ {x : Nat} (hd : Nat) {tl : List Nat} (h : mem x tl = Bool.true ), mem x (hd :: tl) = Bool.true :=
  fun {x} hd {tl} h => @bor_eq_right (mem x tl) (is_eq hd x) h

def subset : List Nat -> List Nat -> Prop :=
  λ s l => List.recOn s True (λ hd tl prev => (mem hd l) ∧ prev)

def subset_nil : ∀ (l : List Nat), subset [] l :=
  λ l => trivial

def subset_cons : ∀ (s l : List Nat) (hd : Nat) (p : mem hd l = Bool.true) (h: subset s l), subset (hd :: s) l := 
  λ s l hd p h => And.intro p h

def subset_cons_list : ∀ (s l : List Nat) (hd : Nat), subset s l → subset s (hd :: l) :=
  λ (s l : List Nat) (hd : Nat) (h : subset s l) =>
    List.rec
      (λ h =>
         id (λ h => trivial)
           h)
      (λ s_hd s_tl s_ih h =>
         id ⟨mem_cons hd (And.left h), s_ih (And.right h)⟩)
      s
      h

def subset_cons_cons : ∀ (s l : List Nat) (hd : Nat) (h: subset s l), subset (hd :: s) (hd :: l) :=
by
  intros s l hd h
  let h2 := subset_cons_list s l hd h
  let h3 := subset_cons s (hd :: l) hd (mem_head hd l) h2
  exact h3

def nodup (l: List Nat) : Prop :=
  List.rec true (λ hd tl prev => (mem hd tl = Bool.false) ∧ prev) l

def nodup_nil : nodup [] := by trivial

def nodup_cons (hd : Nat) (tl : List Nat) (p: mem hd tl = Bool.false) (prior: nodup tl) : nodup (hd :: tl) :=
  And.intro p prior

structure deduped_list (ol : List Nat) := (l : List Nat) (p : nodup l) (sub : subset l ol) (sub2: subset ol l)

def deduped_nil : deduped_list [] := ⟨ [], nodup_nil, subset_nil [], subset_nil [] ⟩

noncomputable instance decidable_bool_eq (b : Bool) : Decidable (b = Bool.false) :=
by
  induction b
  apply isTrue
  apply Eq.refl
  apply isFalse
  intro h
  contradiction

def not_eq_ff_eq_Bool.true {x : Bool} : (¬ x = Bool.false) -> (x = Bool.true) :=
by
  intro h
  induction x
  trivial
  trivial

noncomputable def deduped_cons (hd : Nat) (tl : List Nat) (prev: deduped_list tl) : deduped_list (hd :: tl) :=
  Decidable.recOn (decidable_bool_eq (mem hd prev.l))
    (λ np => deduped_list.mk prev.l prev.p (subset_cons_list prev.l tl hd prev.sub) (subset_cons tl prev.l hd (not_eq_ff_eq_Bool.true np) prev.sub2)) 
    (λ p => deduped_list.mk (hd :: prev.l) (nodup_cons hd prev.l p prev.p) (subset_cons_cons prev.l tl hd prev.sub) (subset_cons_cons tl prev.l hd prev.sub2))

noncomputable def dedup_list : ∀ (l : List Nat), deduped_list l :=
  λ l => List.recOn l deduped_nil (λ hd tl prev => deduped_cons hd tl prev)
