def sub_eff : ℕ → ℕ → ℕ := 
  λ n m, @nat.rec (λ _, ℕ) n (λ mp prev, @nat.rec (λ _, ℕ) nat.zero (λ mpp _, mpp) prev) m
--
def is_zero : ℕ -> bool :=
  λ n, @nat.rec (λ _, bool) true (λ np prev, false) n

def is_eq : ℕ → ℕ → bool :=
  λ n m, is_zero (sub_eff n m) && is_zero (sub_eff m n)

def le_eff : ℕ → ℕ → bool := 
  λ m n, is_zero (sub_eff m n)

axiom is_eq_refl (x : ℕ) : is_eq x x = tt

def mem : ℕ -> list ℕ -> Prop :=
  λ x l, list.rec_on l false (λ hd tl prev, prev ∨ (is_eq hd x = tt))

def bor_eq_split {a b : bool} (h: a || b = tt): a = tt ∨ b = tt :=
begin
  cases a,
  cases b,
  trivial,
  exact or.intro_right _ (eq.refl tt),
  exact or.intro_left _ (eq.refl tt),
end

#print bor._main
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

def ff_ne_tt : ff = tt -> false :=
begin
  intro h,
  trivial,
end

def bor_eq_combine {a b c: bool} (h : a = tt ∨ b = tt ∨ c = tt): a || b || c = tt :=
begin
  cases a,
  cases b,
  exact (or.elim h (λ p, absurd p ff_ne_tt) (λ p, or.elim p (λ p, absurd p ff_ne_tt) (bor_eq_left))),
  exact bor_eq_right (eq.refl tt),
  exact bor_eq_right (eq.refl tt),
end

def bor_eq_combine2 {a b: bool} (h : a = tt ∨ b = tt): a || b = tt :=
begin
  cases a,
  exact (or.elim h (λ p, absurd p ff_ne_tt) (λ p, bor_eq_left p)),
  exact bor_eq_right (eq.refl tt),
end

def mem_head : ∀ (hd : ℕ) (tl : list ℕ), mem hd (hd :: tl) :=
  λ hd tl, or.intro_right _ (is_eq_refl hd)

def mem_cons : ∀ {x : ℕ } (hd : ℕ) {tl : list ℕ} (h : mem x tl), mem x (hd :: tl) :=
  λ x hd tl h, or.intro_left _ h

theorem or_comm_ : ∀ {a b: Prop}, a ∨ b -> b ∨ a :=
  λ a b, or.swap

def or_comm_helper : ∀ {p q r : Prop} (h : p ∨ q ∨ r), (p ∨ r ∨ q) :=
begin
  intros,
  exact or.elim h (or.intro_left (r ∨ q)) (λ qr, or.intro_right p (or_comm_ qr)),
end

theorem or_assoc_forward : ∀ {a b c : Prop}, (a ∨ b) ∨ c -> a ∨ b ∨ c :=
begin
  intros a b c h,
  induction h,
  apply or.elim h,
  intro ha,
  exact or.intro_left _ ha,
  intro hb,
  exact or.intro_right _ (or.intro_left _ hb),
  exact or.intro_right _ (or.intro_right _ h),
end

theorem or_assoc_backward : ∀ {a b c : Prop}, a ∨ b ∨ c -> (a ∨ b) ∨ c :=
begin
  intros a b c h,
  induction h,
  exact or.intro_left _ (or.intro_left _ h),
  induction h,
  exact or.intro_left _ (or.intro_right _ h),
  exact or.intro_right _ h, 
end

def mem_reorder : ∀ {x y z: ℕ} {tl : list ℕ} (h : mem x (y :: z :: tl)), mem x (z :: y :: tl) :=
begin
  intros,
  let h1 := h,
  let h2 := or.elim h1 (λ p, or.intro_left (is_eq y x = tt) ( p)) (λ p, or.intro_right _ p),
  let h3 := or_assoc_forward h2,
  let h4 := or_comm_helper h3,
  let h5 := or_assoc_backward h4,
  exact h5,
end

def subset : list ℕ -> list ℕ -> Prop :=
  λ s l, list.rec_on s true (λ hd tl prev, (mem hd l) ∧ prev)

def subset_nil : ∀ (l : list ℕ), subset [] l :=
  λ l, trivial

def subset_cons : ∀ {s l : list ℕ} {hd : ℕ} (p : mem hd l) (h: subset s l), subset (hd :: s) l := 
  λ s l hd p h, and.intro p h

def subset_cons_list : ∀ {s l : list ℕ} (hd : ℕ) (h: subset s l), subset s (hd :: l) :=
begin
  intros,
  induction s,
  dunfold subset at h,
  trivial,
  let mem1 := and.elim_left h,
  let h2 := s_ih (and.elim_right h),
  dunfold subset,
  let h3 := mem_cons hd mem1,
  exact and.intro h3 h2,
end

def subset_cons_cons : ∀ (s l : list ℕ) (hd : ℕ) (h: subset s l), subset (hd :: s) (hd :: l) :=
begin
  intros,
  let h2 := subset_cons_list  hd h,
  let h3 := subset_cons (mem_head hd l) h2,
  exact h3
end

def subset_tail : ∀ {l tl : list ℕ} {hd : ℕ} (h : subset (hd :: tl) l), subset tl l :=
begin
  intros, 
  exact and.elim_right h,
end

theorem and_assoc_forward : ∀ {a b c : Prop}, (a ∧ b) ∧ c -> a ∧ b ∧ c :=
begin
  intros a b c h,
  induction h,
  induction h_left,
  exact and.intro h_left_left (and.intro h_left_right h_right)
end

theorem and_assoc_backward : ∀ {a b c : Prop}, a ∧ b ∧ c ->  (a ∧ b) ∧ c  :=
begin
  intros a b c h,
  induction h,
  induction h_right,
  exact and.intro (and.intro h_left h_right_left) h_right_right
end

theorem and_comm_ : ∀ {a b: Prop}, a ∧ b -> b ∧ a :=
  λ a b, and.swap 

def subset_reorder_s : ∀ {tl l : list ℕ} {x y : ℕ} (h : subset (x :: y :: tl) l), subset (y :: x :: tl) l :=
begin
  intros,
  let h1 := and.elim_left (and_assoc_backward h),
  let h2 := and.elim_right (and_assoc_backward h),
  exact and_assoc_forward (and.intro (and_comm_ h1) h2),
end

def subset_eq : ∀ (l : list ℕ), subset l l :=
begin
  intro,
  induction l,
  trivial,
  exact subset_cons_cons l_tl l_tl l_hd l_ih,
end

def subset_reorder : ∀ {s tl : list ℕ} {x y : ℕ} (h: subset s (x :: y :: tl)), subset s (y :: x :: tl) :=
begin
  intros,
  induction s,
  trivial,
  let h1 := s_ih (and.elim_right h),
  let h2 := and.elim_left h,
  let h3 := mem_reorder h2,
  exact and.intro h3 h1,
end

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

def flip_eq {a b : bool} (p: a = b) : (b = a) :=
begin
  exact @eq.subst bool (λ x, x = a) a b p (eq.refl a),
end

def sorted : list ℕ -> Prop :=
  λ l, list.rec_on l true (λ hd tl prev, list.rec_on tl true (λ hd_tl tl_tl prev_tl, le_eff hd hd_tl = tt ∧ prev) )
def sorted_nil : sorted [] := trivial
def sorted_singleton (x : ℕ) : sorted [x] := trivial
def sorted_cons_le (x : ℕ) (hd : ℕ) (tl: list ℕ) (h: sorted (hd :: tl)) (h2: le_eff x hd = tt) : sorted (x :: hd :: tl) :=
  and.intro h2 h
def sorted_tail (hd : ℕ) (tl : list ℕ) (h: sorted (hd :: tl)) : sorted tl :=
begin
  induction tl,
  trivial,
  exact and.elim_right h,
end

axiom le_eff_of_not_le {a b : ℕ}: (le_eff a b = ff) -> (le_eff b a)

def insert_sorted (x : ℕ) (l : list ℕ) : list ℕ :=
  list.rec_on l [x] (λ hd tl prev, bool.rec_on (le_eff x hd) (hd :: prev) (x :: hd :: tl))

def insert_sorted_subset (x : ℕ) (s l : list ℕ) (h: subset s l) : subset (insert_sorted x s) (x :: l) :=
begin
  induction s,
  dunfold insert_sorted,
  dunfold subset,
  exact (and.intro (mem_head x l) true.intro),
  dunfold insert_sorted,
  cases (decidable_bool_eq (le_eff x s_hd)),
  let h1 := not_eq_ff_eq_tt h_1,
  exact @eq.subst bool (λb, subset (bool.rec (s_hd :: list.rec [x] (λ (hd : ℕ) (tl prev : list ℕ), bool.rec (hd :: prev) (x :: hd :: tl) (le_eff x hd)) s_tl) (x :: s_hd :: s_tl) b) (x :: l)) tt (le_eff x s_hd) (flip_eq h1) (subset_cons_cons (s_hd :: s_tl) l x h),
  apply @eq.subst bool (λb, subset (bool.rec (s_hd :: list.rec [x] (λ (hd : ℕ) (tl prev : list ℕ), bool.rec (hd :: prev) (x :: hd :: tl) (le_eff x hd)) s_tl) (x :: s_hd :: s_tl) b) (x :: l)) ff (le_eff x s_hd) (flip_eq h_1),
  let h1 := s_ih (subset_tail h),
  let h2 := mem_cons x (and.elim_left h),
  exact and.intro h2 h1,
end

#print or.elim
def mem_insert_sorted {x : ℕ} {l : list ℕ} (y : ℕ ) (h : mem x l) : mem x (insert_sorted y l) :=
begin
  induction l,
  dunfold mem at h,
  exact false.elim (h),
  dunfold insert_sorted,
  cases (decidable_bool_eq (le_eff y l_hd)),
  let h_1 := not_eq_ff_eq_tt h_1,
  let h2 := (mem_cons y h),
  exact @eq.subst bool (λ b, mem x (bool.rec (l_hd :: list.rec [y] (λ (hd : ℕ) (tl prev : list ℕ), bool.rec (hd :: prev) (y :: hd :: tl) (le_eff y hd)) l_tl) (y :: l_hd :: l_tl) b)) tt (le_eff y l_hd) (flip_eq h_1) h2,
  cases (decidable_bool_eq (is_eq l_hd x)),
  apply @eq.subst bool (λ b, mem x (bool.rec (l_hd :: list.rec [y] (λ (hd : ℕ) (tl prev : list ℕ), bool.rec (hd :: prev) (y :: hd :: tl) (le_eff y hd)) l_tl) (y :: l_hd :: l_tl) b)) ff (le_eff y l_hd) (flip_eq h_1),
  dunfold mem,
  let h_2 := not_eq_ff_eq_tt h_2,
  exact (or.intro_right _ h_2),
  apply @eq.subst bool (λ b, mem x (bool.rec (l_hd :: list.rec [y] (λ (hd : ℕ) (tl prev : list ℕ), bool.rec (hd :: prev) (y :: hd :: tl) (le_eff y hd)) l_tl) (y :: l_hd :: l_tl) b)) ff (le_eff y l_hd) (flip_eq h_1),
  dunfold mem,
  dunfold mem at h,
  let h := or.elim (h) (λp, p) (λ p, false.elim (ff_ne_tt (eq.trans (flip_eq h_2) p))),
  let h1 := or.intro_left (is_eq l_hd x = tt) (l_ih h),
  let h2 := h1,
  exact h2,
end
#print mem_insert_sorted

def and_true_intro (p : Prop): p -> p ∧ true :=
begin
  intro h,
  exact and.intro h true.intro,
end

def and_true_elim (p : Prop) : p ∧ true -> p :=
begin
  apply and.elim_left,
end

def subset_insert_sorted (x : ℕ) (s l : list ℕ) (h : subset s l) : subset (x :: s) (insert_sorted x l)  :=
begin
  induction s,
  dunfold insert_sorted,
  dunfold subset,
  induction l,
  exact (and.intro (mem_head x []) (true.intro)),
  cases (decidable_bool_eq (le_eff x l_hd)),
  let h_1 := not_eq_ff_eq_tt h_1,
  apply (and_true_intro (mem x (list.rec_on (l_hd :: l_tl) [x] (λ (hd : ℕ) (tl prev : list ℕ), bool.rec_on (le_eff x hd) (hd :: prev) (x :: hd :: tl))))),
  apply @eq.subst bool (λ b, mem x (bool.rec (l_hd :: list.rec [x] (λ (hd : ℕ) (tl prev : list ℕ), bool.rec (hd :: prev) (x :: hd :: tl) (le_eff x hd)) l_tl) (x :: l_hd :: l_tl) b)) tt (le_eff x l_hd) (flip_eq h_1),
  exact (mem_head x (l_hd :: l_tl)),
  apply (and_true_intro (mem x (list.rec_on (l_hd :: l_tl) [x] (λ (hd : ℕ) (tl prev : list ℕ), bool.rec_on (le_eff x hd) (hd :: prev) (x :: hd :: tl))))),
  apply @eq.subst bool (λ b, mem x (bool.rec (l_hd :: list.rec [x] (λ (hd : ℕ) (tl prev : list ℕ), bool.rec (hd :: prev) (x :: hd :: tl) (le_eff x hd)) l_tl) (x :: l_hd :: l_tl) b)) ff (le_eff x l_hd) (flip_eq h_1),
  let h1 := l_ih (subset_nil l_tl),
  let h1 := (and_true_elim (mem x (list.rec_on l_tl [x] (λ (hd : ℕ) (tl prev : list ℕ), bool.rec_on (le_eff x hd) (hd :: prev) (x :: hd :: tl))))) h1,
  exact (mem_cons l_hd h1),
  let h2 := s_ih (subset_tail h),
  let h3 := and.elim_left h,
  let h4 := mem_insert_sorted x h3,
  let h5 := subset_cons h4 h2,
  exact subset_reorder_s h5,
end

def insert_sorted_correct (x : ℕ) (l : list ℕ) (h: sorted l) : sorted (insert_sorted x l) :=
  list.rec_on l 
    (λ h: sorted [], trivial)
    (λ hd tl prev, 
      (λ h: sorted (hd :: tl), decidable.rec_on (decidable_bool_eq (le_eff x hd))
        (λ h_1, @eq.subst bool (λb, sorted (bool.rec (hd :: list.rec [x] (λ (hd : ℕ) (tl prev : list ℕ), bool.rec (hd :: prev) (x :: hd :: tl) (le_eff x hd)) tl) (x :: hd :: tl) b)) tt (le_eff x hd) (flip_eq (not_eq_ff_eq_tt h_1)) (sorted_cons_le x hd tl h (not_eq_ff_eq_tt h_1)))
        (λ h_1, 
          @eq.subst bool (λ b, sorted (bool.rec (hd :: list.rec [x] (λ (hd : ℕ) (tl prev : list ℕ), bool.rec (hd :: prev) (x :: hd :: tl) (le_eff x hd)) tl) (x :: hd :: tl) b)) ff (le_eff x hd) (flip_eq h_1)
            (list.rec_on tl 
              (λ h, λ l_ih, sorted_cons_le hd x [] (sorted_singleton x) (le_eff_of_not_le h_1))
              (λ l_tl_hd l_tl_tl prev_tl, 
                (λ h : sorted (hd :: l_tl_hd :: l_tl_tl),
                 λ l_ih : sorted (l_tl_hd :: l_tl_tl) → sorted (insert_sorted x (l_tl_hd :: l_tl_tl)),
                  decidable.rec_on (decidable_bool_eq (le_eff x l_tl_hd))
                    (λ np, let 
                      h1 := (not_eq_ff_eq_tt np),
                      h2 := sorted_tail hd (l_tl_hd :: l_tl_tl) h,
                      h3 := sorted_cons_le (x) l_tl_hd l_tl_tl h2 h1,
                      h4 := (le_eff_of_not_le h_1),
                      h5 := (sorted_cons_le (hd) (x) (l_tl_hd :: l_tl_tl) h3 h4),
                      h6 := @eq.subst bool (λ b1, sorted (hd :: bool.rec (l_tl_hd :: list.rec [x] (λ (hd : ℕ) (tl prev : list ℕ), bool.rec (hd :: prev) (x :: hd :: tl) (le_eff x hd)) l_tl_tl) (x :: l_tl_hd :: l_tl_tl) b1)) tt (le_eff x l_tl_hd) (flip_eq h1) h5 in
                        h6
                    )
                    (λ pp, 
                        @eq.subst bool (λ b1, sorted (hd :: bool.rec (l_tl_hd :: list.rec [x] (λ (hd : ℕ) (tl prev : list ℕ), bool.rec (hd :: prev) (x :: hd :: tl) (le_eff x hd)) l_tl_tl) (x :: l_tl_hd :: l_tl_tl) b1)) ff (le_eff x l_tl_hd) (flip_eq pp)
                          (
                            let h3 := sorted_tail hd (l_tl_hd :: l_tl_tl) h,
                                h4 := l_ih h3,
                                h5 := and.elim_left h,
                                h6 := @eq.subst bool (λ b1, sorted (bool.rec (l_tl_hd :: list.rec [x] (λ (hd : ℕ) (tl prev : list ℕ), bool.rec (hd :: prev) (x :: hd :: tl) (le_eff x hd)) l_tl_tl) (x :: l_tl_hd :: l_tl_tl) b1)) (le_eff x l_tl_hd) ff (pp) h4
                                in sorted_cons_le (hd) (l_tl_hd) (insert_sorted x l_tl_tl) h6 h5
                          )
                    )
               )
            )
            h
            prev 
          )
        )
      )
    )
    h

def sort : list ℕ -> list ℕ :=
  λ l, list.rec_on l [] (λ hd tl prev, insert_sorted hd prev) 

def sort_sorted (l : list ℕ) : sorted (sort l) :=
    (list.rec_on l (sorted_nil) (λ hd tl ih, insert_sorted_correct hd (sort tl) ih))

def subset_sort (l : list ℕ) :  subset (l) (sort l)  :=
      (list.rec_on l (trivial) (λ hd tl ih, 
        subset_insert_sorted hd tl (sort tl) ih
      ))

def sort_subset (l : list ℕ) : subset (sort l) (l) :=
      (list.rec_on l (trivial) (λ hd tl ih, insert_sorted_subset hd (sort tl) tl ih))

def sort_correct (l : list ℕ) : sorted (sort l) ∧ subset (l) (sort l) ∧ subset (sort l) (l) :=
  and.intro (sort_sorted l) (and.intro (subset_sort l) (sort_subset l))