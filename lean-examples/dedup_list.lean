def sub_eff : ℕ → ℕ → ℕ := 
  λ n m, @nat.rec (λ _, ℕ) n (λ mp prev, @nat.rec (λ _, ℕ) nat.zero (λ mpp _, mpp) prev) m

def is_zero : ℕ -> bool :=
  λ n, @nat.rec (λ _, bool) true (λ np prev, false) n

def is_eq : ℕ → ℕ → bool :=
  λ n m, is_zero (sub_eff n m) && is_zero (sub_eff m n)

axiom is_eq_refl (x : ℕ) : is_eq x x = tt

def mem : ℕ -> list ℕ -> bool :=
  λ x l, list.rec_on l ff (λ hd tl prev, prev || (is_eq hd x))

def bor_eq_split_ineff {a b : bool} (h: a || b = tt): a = tt ∨ b = tt :=
begin
  simp at h,
  exact h,
end

def bor_eq_split {a b : bool} (h: a || b = tt): a = tt ∨ b = tt :=
begin
  cases a,
  cases b,
  trivial,
  exact or.intro_right _ (eq.refl tt),
  exact or.intro_left _ (eq.refl tt),
end

def bor_eq_left {a b : bool} (h: b = tt) : a || b = tt :=
begin
  cases b,
  trivial,
  cases a,
  trivial,
  trivial,
end

def bor_eq_right {a b : bool} (h: a = tt) : a || b = tt :=
begin
  cases a,
  trivial,
  cases b,
  trivial,
  trivial,
end

def mem_head : ∀ (hd : ℕ) (tl : list ℕ), mem hd (hd :: tl) = tt:=
  λ hd tl, bor_eq_left (is_eq_refl hd)

def mem_cons : ∀ {x : ℕ } (hd : ℕ) {tl : list ℕ} (h : mem x tl = tt), mem x (hd :: tl) = tt :=
  λ x hd tl h, (bor_eq_right h)

def mem_cons_ineff : ∀ {x : ℕ } (hd : ℕ) {tl : list ℕ} (h : mem x tl = tt), mem x (hd :: tl) = tt :=
begin
  intros,
  dunfold mem,
  simp,
  dunfold mem at h,
  simp at h,
  exact or.intro_left _ h,
end

def dedup_list : list ℕ -> list ℕ :=
  λ l, list.rec_on l [] (λ hd tl prev, bool.rec_on (mem hd prev) (prev) (hd :: prev))

def subset : list ℕ -> list ℕ -> Prop :=
  λ s l, list.rec_on s true (λ hd tl prev, (mem hd l) ∧ prev)

def subset_nil : ∀ (l : list ℕ), subset [] l :=
  λ l, trivial

def subset_cons : ∀ (s l : list ℕ) (hd : ℕ) (p : mem hd l = tt) (h: subset s l), subset (hd :: s) l := 
  λ s l hd p h, and.intro p h

def subset_cons_list : ∀ (s l : list ℕ) (hd : ℕ), subset s l → subset s (hd :: l) :=
  λ (s l : list ℕ) (hd : ℕ) (h : subset s l),
    list.rec
      (λ h,
         id (λ h, trivial)
           h)
      (λ s_hd s_tl s_ih h,
         id ⟨mem_cons hd (and.elim_left h) , s_ih (and.elim_right h)⟩)
      s
      h

def subset_cons_cons : ∀ (s l : list ℕ) (hd : ℕ) (h: subset s l), subset (hd :: s) (hd :: l) :=
begin
  intros,
  let h2 := subset_cons_list s l hd h,
  let h3 := subset_cons s (hd :: l) hd (mem_head hd l) h2,
  exact h3
end

def nodup (l: list ℕ) : Prop :=
  list.rec true (λ hd tl prev, (mem hd tl = ff) ∧ prev) l

def nodup_nil : nodup [] := trivial

def nodup_cons (hd : ℕ) (tl : list ℕ) (p: mem hd tl = ff) (prior: nodup tl) : nodup (hd :: tl) :=
  and.intro p prior

structure deduped_list (ol : list ℕ) := (l : list ℕ) (p : nodup l) (sub : subset l ol) (sub2: subset ol l)

def deduped_nil : deduped_list [] := ⟨ [], nodup_nil, subset_nil [], subset_nil [] ⟩

instance decidable_bool_eq (b : bool) : decidable (b = ff) :=
begin
  induction b,
  apply is_true,
  apply eq.refl,
  apply is_false,
  intro h,
  apply tt_eq_ff_eq_false h,
end

def not_eq_ff_eq_tt {x : bool} : (¬ x = ff) -> (x = tt) :=
begin
  intro h,
  induction x,
  trivial,
  trivial
end

def deduped_cons (hd : ℕ) (tl : list ℕ) (prev: deduped_list tl) : deduped_list (hd :: tl) :=
  decidable.rec_on (decidable_bool_eq (mem hd prev.l))
    (λ np, deduped_list.mk prev.l prev.p (subset_cons_list prev.l tl hd prev.sub) (subset_cons tl prev.l hd (not_eq_ff_eq_tt np) prev.sub2)) 
    (λ p, deduped_list.mk (hd :: prev.l) (nodup_cons hd prev.l p prev.p) (subset_cons_cons prev.l tl hd prev.sub) (subset_cons_cons tl prev.l hd prev.sub2))

def deduped_list_new : Π (l : list ℕ), deduped_list l :=
  λ l, list.rec_on l deduped_nil (λ hd tl prev, deduped_cons hd tl prev)
