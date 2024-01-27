open classical

#check forall_not_of_not_exists

variables (A B: Prop)
lemma contrapositive (h : ¬ B → ¬ A) : A → B :=
assume h1 : A,
show B, from
  by_contradiction
    (assume h2 : ¬ B,
      have h3 : ¬ A, from h h2,
      show false, from h3 h1)

--λ hne x hp, hne ⟨x, hp⟩

#print Exists

lemma exists_push {p : ℕ -> ℕ -> Prop} : (¬ (∃ i j : ℕ, p i j)) -> (∀ i j : ℕ, ¬ p i j) :=
begin
  intros hne i j hp,
  exact hne (Exists.intro i (Exists.intro j hp)),
end
--assume : A,
--show B, from
--  by_contradiction
--    (assume : ¬ B,
--      have A ∧ ¬ B, from and.intro ‹A› this,
--      show false, from h this)

lemma implies_to_disjunct {A B: Prop}: (A -> B) ↔ (¬ A ∨ B) :=
begin
  apply iff.intro,
  intro h,
  let h := or.elim (em A) (
    begin
      intro a,
      exact or.intro_right (¬ A) (h a),
    end
  ) (
    begin
      intro not_a,
      exact or.intro_left (B) not_a,
    end
  ),
  exact h,
  intro h,
  intro a,
  let test := (em A),
  apply or.elim h (
    begin
    intro not_a,
    exact (@absurd A B a not_a),
    end
  )
  (
    begin
      intro b,
      exact b,
    end
  )
end

theorem demorgan_or {P Q : Prop} : (¬ (P ∨ Q)) ↔ ¬ P ∧ ¬ Q :=
begin
  apply iff.intro,
  intro h,
  apply or.elim (em P) (
    begin
      intro p,
      let p_or_q := or.intro_left Q p,
      let answer: ¬ P ∧ ¬ Q := absurd (p_or_q) h,
      exact answer,
    end
  )
  (
    begin
      intro p,
      apply and.intro,
      exact p,
      intro q,
      let p_or_q := or.intro_right P q,
      exact (h p_or_q),
    end
  ),
  intro h,
  intro p_or_q,
  cases p_or_q,
  apply and.elim_left h,
  exact p_or_q,
  apply and.elim_right h,
  exact p_or_q,
end

-- could be simpliefied probably...
theorem demorgan_and {P Q : Prop} : (¬ (P ∧ Q)) ↔ ¬ P ∨ ¬ Q :=
begin
  apply iff.intro,
  intro h,
  apply or.elim (em P),
  intro p,
  apply or.elim (em Q),
  intro q,
  apply absurd (and.intro p q) h,
  intro nq,
  apply or.intro_right (¬ P) nq,
  intro np,
  apply or.intro_left (¬ Q) np,
  intro h,
  intro hp,
  apply or.elim h,
  intro np,
  let p := and.elim hp (λ p q, p),
  exact absurd p np,
  intro nq,
  let q := and.elim hp (λ p q, q),
  exact absurd q nq,
end

theorem not_not_iff {P : Prop} : ¬ ¬ P ↔ P :=
begin
  apply iff.intro,
  intro nnp,
  by_contra,
  exact nnp h,
  intro p,
  intro np,
  exact absurd p np,
end

set_option trace.simp_lemmas true


--theorem pigeon_BAD (n : ℕ) (f : ℕ → ℕ) :
--  (∀i : ℕ,  (i < n+1) → (f i < n))
--  → ∃ i j : ℕ, (i < j ∧ j < n + 1) → (f i = f j) :=
--begin
--  apply contrapositive,
--  intro h,
--  intro not_h,
--  simp [implies_to_disjunct] at not_h,
--  simp [implies_to_disjunct] at h,
--  let ht := exists_push h,
--  simp at ht,
--  simp [demorgan_or] at ht,
--  simp [not_not_iff] at ht,
--  let test := ht 1 0,
--  simp [and.assoc] at test,
--  let test2 :=  and.elim_left test,
--  let test3 := nat.not_lt_zero 1 test2,
--  exact test3,
--end
--
--#check Exists.intro
--
--theorem pidgeon1 (n : ℕ) (i j : ℕ) (f : ℕ → ℕ) :
--  (∀i : ℕ,  (i < n+1) → (f i < n))
--  → (i < j ∧ j < n ∧ f i = f j)
--  → (∃ k l : ℕ, (k < l ∧ l < n + 1 ∧ f k = f l)) :=
--begin
--  intro h1,
--  intro h2,
--  let h3 := and.right h2,
--  let h3' := and.left h2,
--  let h4 := and.left h3,
--  let h5 := nat.lt.step h4,
--  let h6 := and.right h3,
--  let h7 := (and.intro h3' (and.intro h5 h6)),
--  apply exists.intro i,
--  apply exists.intro j,
--  exact h7,
--end
--
--theorem pidgeon2 (n : ℕ) (i j : ℕ) (f : ℕ → ℕ) :
--  (∀i : ℕ,  (i < n+1) → (f i < n))
--  → (i < j ∧ j < n ∧ f i = f j)
--  → (∃ k l : ℕ, (k < l ∧ l < n + 1 ∧ f k = f l)) :=
--
--
--#check em

--theorem pigeon (n : ℕ) (f : ℕ → ℕ) :
--  (∀i : ℕ,  (i < n+1) → (f i < n))
--  → ∃ i j : ℕ, (i < n+1 ∧ j < n + 1 ∧ f i = f j) :=
--begin
--  intro h,
--  let i : ℕ,
--  exact n,
--  let hi := h i,
--  let i : ℕ,
--  exact n,
--  let j : ℕ,
--  exact n,
--  apply exists.intro i,
--  apply exists.intro j,
--  by_contradiction,
--
--  --let test := forall_not_of_not_exists h,
--  --let v : ℕ,
--  --exact n,
--  --let test2 := test v,
--  --simp at test2,
--  --let test := forall_not_of_not_exists test2,
--  --simp at test,
--  --let w : ℕ,
--  --exact n,
--  --let statement := test w,
--  --cases (iff.elim_left demorgan_and) statement,
--  --revert h_1,
--
--
--  --by_cases statement_demorgan,
--  --let em_v := (em (v < n + 1)),
--
--
--  --induction n,
--  --intro h,
--  --let t := (h 0),
--  --let t2 := t (nat.zero_lt_succ 0),
--  --exact absurd t2 (nat.not_lt_zero (f 0)),
--  --intro h,
--  -- TODO: idea:
--  -- Can we split into cases?
--  -- Case 1: two or more f i = f j = n + 1 -> done trivially
--  -- Case 2: 1 value f i = n + 1 (e.g. forall i /= j, f i < n + 1) -> then prove by creating g where we swap i with last value of n+1, then prove by induction
--  -- Case 3: no value = n+1, easy by induction done.
--
--end

-- TODO
--begin
--  intro h,
--  intro h2,
--
--
--end

#print list.rec
#print list.length
--def list_len : list ℕ -> ℕ :=
--  λ l, @list.rec ℕ (λ _, ℕ) 0 (λ hd tl p, 1 + p) l
--
def add_eff : ℕ → ℕ → ℕ :=
  λ n m, @nat.rec (λ _, ℕ) n (λ mp prev, prev.succ) m

lemma eq_succ {a b : ℕ} : (a = b) -> (a.succ = b.succ) :=
  λ h, eq.subst h rfl

lemma add_eff_zero {a : ℕ} : (add_eff 0 a) = a :=
  nat.rec_on a (eq.refl 0) (λ np prev, eq_succ prev)

def sub_eff : ℕ → ℕ → ℕ := 
  λ n m, @nat.rec (λ _, ℕ) n (λ mp prev, @nat.rec (λ _, ℕ) nat.zero (λ pprev _, pprev) prev) m

def is_zero : ℕ -> Prop :=
  λ n, @nat.rec (λ _, Prop) true (λ np prev, false) n

theorem is_zero_succ {n : ℕ} : (is_zero n.succ) -> false :=
  λ h, h

theorem is_zero_eq_zero {n : ℕ}: (is_zero n) -> n = 0 :=
  nat.rec_on n (λ hp, eq.refl 0) (λ np hp prev, false.rec_on (np.succ = 0) (is_zero_succ prev))

theorem is_zero_zero : (is_zero 0) :=
  trivial

lemma add_eff_is_zero : (is_zero (add_eff 0 0)) :=
  trivial

def sub_eff_is_zero_succ {n m: ℕ} : (is_zero (sub_eff n m)) -> (is_zero (sub_eff n m.succ)) :=
  λ h, @eq.subst ℕ 
    (λ a, is_zero (nat.rec 0 (λ (pprev : ℕ) (_x : (λ (_x : ℕ), ℕ) pprev), pprev) a))
     (0) (sub_eff n m) (eq.symm (is_zero_eq_zero h)) (trivial)

--def sub_eff_is_zero_succ2 {n m: ℕ} : () -> (is_zero (sub_eff n m)) :=

def sub_eff_is_zero_pred {n m: ℕ} : (¬ is_zero (sub_eff n m.succ)) -> (¬ is_zero (sub_eff n m)) :=
  λ h h2, absurd (sub_eff_is_zero_succ h2) h

def lt_eff : ℕ → ℕ → Prop := 
  λ m n, is_zero (sub_eff m.succ n)

inductive nat_list : Type
| nil : nat_list
| cons : ℕ → nat_list -> nat_list

def list_len : nat_list -> ℕ :=
  λ l, @nat_list.rec (λ _, ℕ) nat.zero (λ hd tl prev, prev.succ) l

def sum_list : nat_list → ℕ := 
  λ l, @nat_list.rec (λ _, ℕ) nat.zero (λ hd tl prev, add_eff hd prev) l

def double_pigeon : nat_list → Prop :=
  λ l, @nat_list.rec (λ _, Prop) false (λ hd tl prev, (lt_eff nat.zero.succ hd) ∨ prev) l

lemma sub_eff_zero_zero : (is_zero (sub_eff nat.zero.succ nat.zero)) → false :=
  λ h, h

-- law of excluded middle
axiom em_eff : ∀ (p : Prop), p ∨ ¬p

-- n >= m , m >= k , n >= k
axiom gt_eff_trans {n m k : ℕ} : (¬lt_eff n m) -> (¬lt_eff m k) -> (¬ lt_eff n k)

axiom gt_add_left {n m : ℕ} (h: ¬lt_eff n m) (k : ℕ) : (¬lt_eff (add_eff k n) (add_eff m k))

axiom gt_add_right {n m : ℕ} (h: ¬lt_eff n m) (k : ℕ) : (¬lt_eff (add_eff n k) (add_eff m k))

theorem add_gt {a b c d : ℕ} : (¬ lt_eff a b) -> (¬lt_eff c d) -> (¬ lt_eff (add_eff a c) (add_eff d b)) :=
  λ h1 h2, gt_eff_trans (gt_add_right h1 c) (gt_add_left h2 b)

-- if a + 1 < c + d and a >= d, then 1 < c
theorem lt_eff_succ_gt {a c d : ℕ} : (lt_eff (add_eff a 1) (add_eff c d)) → (¬ (lt_eff a d)) → (lt_eff 1 c) :=
  λ h1 h2, or.rec_on (em_eff (lt_eff 1 c)) (λ p, p) (λ np, absurd h1 (add_gt h2 np))

theorem pigeon_termed (l : nat_list) : (lt_eff (list_len l) (sum_list l)) → (double_pigeon l) :=
  nat_list.rec (sub_eff_zero_zero)
    (λ (l_hd : ℕ) (l_tl : nat_list) (l_ih : lt_eff (list_len l_tl) (sum_list l_tl) → double_pigeon l_tl)
     (h : lt_eff (list_len (nat_list.cons l_hd l_tl)) (sum_list (nat_list.cons l_hd l_tl))),
       (em_eff (lt_eff (list_len l_tl) (sum_list l_tl))).cases_on
         (λ (h_1 : lt_eff (list_len l_tl) (sum_list l_tl)),
            (or.intro_right (lt_eff nat.zero.succ l_hd) (l_ih h_1)))
         (λ (h_1 : ¬lt_eff (list_len l_tl) (sum_list l_tl)), 
            (or.intro_left
              (double_pigeon l_tl)
              (lt_eff_succ_gt h h_1))))
    l

theorem test_pigeon (l : nat_list) : (lt_eff (list_len l) (sum_list l)) → (double_pigeon l) :=
begin 
  induction l with l_hd l_tl,
  dunfold list_len,
  dunfold sum_list,
  dunfold double_pigeon,
  dunfold lt_eff,
  simp,
  apply sub_eff_zero_zero,
  intro h,
  cases (em_eff (lt_eff (list_len (l_tl)) (sum_list (l_tl)))),
  let tl_less := l_ih h_1,
  dunfold double_pigeon,
  apply or.intro_right,
  exact tl_less,
  let hi := lt_eff_succ_gt h h_1,
  dunfold double_pigeon,
  apply or.intro_left,
  exact hi,
end
#print pigeon_termed

def sum_list_ineff : list ℕ → ℕ := 
  λ l, @list.rec ℕ (λ _, ℕ) nat.zero (λ hd tl prev, hd + prev) l

def double_pigeon_ineff : list ℕ → Prop :=
  λ l, @list.rec ℕ (λ _, Prop) false (λ hd tl prev, (1 < hd) ∨ prev) l

lemma le_cancel {a b c d: ℕ} : a + b ≤ c + d -> b = d -> a ≤ c :=
begin
  intro h1,
  intro h2,
  rw ←h2 at h1,
  rw (nat.add_le_add_iff_le_right b a c) at h1,
  exact h1,
end

lemma le_lt_or_eq {a b : ℕ} : a ≤ b -> a < b ∨ a = b :=
begin
  intro h,
  induction h,
  simp,
  cases h_ih,
  let test := nat.lt_succ_of_lt h_ih,
  exact (or.intro_left (a = h_b.succ) test),
  rw h_ih,
  exact (or.intro_left (h_b = h_b.succ) (nat.lt_succ_self h_b)),
end

lemma le_pigeon_lemma {a c d : ℕ} : ((1 + a) < (c + d)) → (¬ (a < d)) → (1 < c) :=
begin
  intro h1,
  intro h2,
  rw not_lt at h2,
  cases le_lt_or_eq h2,
  let full := nat.add_lt_add h1 h,
  rw nat.add_assoc at full,
  rw nat.add_assoc at full,
  let comm := nat.add_comm a d,
  rw comm at full,
  exact nat.lt_of_add_lt_add_right full,
  rw h at h1,
  exact nat.lt_of_add_lt_add_right h1,
end

#print has_lt.lt
theorem pigeon_inefficient (l : list ℕ) : ((list.length l) < (sum_list_ineff l)) → (double_pigeon_ineff l) :=
begin 
  induction l with l_hd l_tl,
  dunfold list.length,
  dunfold sum_list_ineff,
  dunfold double_pigeon_ineff,
  simp,
  apply nat.not_lt_zero 0,
  intro h,
  cases (em ((list.length (l_tl)) < (sum_list_ineff (l_tl)))),
  let tl_less := l_ih h_1,
  dunfold double_pigeon_ineff,
  apply or.intro_right,
  exact tl_less,
  unfold list.length at h,
  unfold sum_list_ineff at h,
  rw nat.add_comm at h,
  let hi :=  le_pigeon_lemma h h_1,
  dunfold double_pigeon_ineff,
  apply or.intro_left,
  exact hi,
end

--#print test_pigeon
--
--def list_len_no_eff : list ℕ -> ℕ :=
--  λ l, @list.rec ℕ (λ _, ℕ) nat.zero (λ hd tl prev, 1 + prev) l
--
--def sum_list_no_eff: list ℕ → ℕ := 
--  λ l, @list.rec ℕ (λ _, ℕ) nat.zero (λ hd tl prev, hd + prev) l
--
--def double_pigeon_no_eff : list ℕ → Prop :=
--  λ l, @list.rec ℕ (λ _, Prop) false (λ hd tl prev, (1 < hd) ∨ prev) l
----
----axiom hithere (l_hd: ℕ) (l_tl: list ℕ) (l_ih: list_len l_tl < sum_list l_tl → double_pigeon l_tl) (h: list_len (l_hd :: l_tl) < sum_list (l_hd :: l_tl)) : double_pigeon (l_hd :: l_tl)
----
--axiom assumeitall (l : nat_list) (p: lt_eff (list_len l) (sum_list l)) : (double_pigeon l)
--
--axiom inductive_case (l_hd : ℕ) (l_tl : nat_list)  (l_ih : lt_eff (list_len l_tl) (sum_list l_tl) → double_pigeon l_tl) : lt_eff (list_len (nat_list.cons l_hd l_tl)) (sum_list (nat_list.cons l_hd l_tl)) → double_pigeon (nat_list.cons l_hd l_tl)
--
--theorem pigeon_axiomed (l : nat_list) : (lt_eff (list_len l) (sum_list l)) → (double_pigeon l) := λ p, assumeitall l p