open classical

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

theorem pigeonhole (l : nat_list) : (lt_eff (list_len l) (sum_list l)) → (double_pigeon l) :=
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