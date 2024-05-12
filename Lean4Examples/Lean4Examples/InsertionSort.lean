
namespace InsertionSort 

noncomputable def add_eff : Nat → Nat → Nat :=
  λ n m => @Nat.rec (λ _ => Nat) n (λ mp prev => Nat.succ prev) m

noncomputable def sub_eff : Nat → Nat → Nat := 
  λ n m => @Nat.rec (λ _ => Nat) n (λ mp prev => @Nat.rec (λ _=> Nat) Nat.zero (λ pprev _ => pprev) prev) m

noncomputable def is_zero : Nat -> Bool :=
  λ n => @Nat.rec (λ _ => Bool) Bool.true (λ np prev => Bool.false) n

noncomputable def is_eq : Nat → Nat → Bool :=
  λ n m => is_zero (sub_eff n m) && is_zero (sub_eff m n)

noncomputable def le_eff : Nat → Nat → Bool := 
  λ m n => is_zero (sub_eff m n)

axiom is_eq_refl (x : Nat) : is_eq x x = Bool.true

def mem : Nat -> List Nat -> Prop :=
  λ x l => List.recOn l False (λ hd tl prev => prev ∨ (is_eq hd x = Bool.true))

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

def ff_ne_tt : Bool.false = Bool.true -> False :=
by
  intro h
  trivial

def bor_eq_combine {a b c: Bool} (h : a = Bool.true ∨ b = Bool.true ∨ c = Bool.true): (a || b || c) = Bool.true :=
by
  cases a
  cases b
  exact (Or.elim h (λ p => absurd p ff_ne_tt) (λ p => Or.elim p (λ p => absurd p ff_ne_tt) (bor_eq_left)))
  exact bor_eq_right (Eq.refl Bool.true)
  exact bor_eq_right (Eq.refl Bool.true)

def bor_eq_combine2 {a b: Bool} (h : a = Bool.true ∨ b = Bool.true): (a || b) = Bool.true :=
by
  cases a
  exact (Or.elim h (λ p => absurd p ff_ne_tt) (λ p => bor_eq_left p))
  exact bor_eq_right (Eq.refl Bool.true)

def mem_head : ∀ (hd : Nat) (tl : List Nat), mem hd (hd :: tl) :=
  λ hd tl => Or.intro_right _ (is_eq_refl hd)

def mem_cons : ∀ {x : Nat } (hd : Nat) {tl : List Nat} (h : mem x tl), mem x (hd :: tl) :=
  λ {x} hd {tl} h => Or.intro_left _ h

theorem or_comm_ : ∀ {a b: Prop}, a ∨ b -> b ∨ a :=
  Or.symm

def or_comm_helper : ∀ {p q r : Prop} (h : p ∨ q ∨ r), (p ∨ r ∨ q) :=
by
  intros p q r h
  exact Or.elim h (Or.intro_left (r ∨ q)) (λ qr => Or.intro_right p (or_comm_ qr))

theorem or_assoc_forward : ∀ {a b c : Prop}, (a ∨ b) ∨ c -> a ∨ b ∨ c :=
by
  intros a b c h
  induction h with
  | inl h => apply Or.elim h
             intro ha
             exact Or.intro_left _ ha
             intro hb
             exact Or.intro_right _ (Or.intro_left _ hb)
  | inr h => exact Or.intro_right _ (Or.intro_right _ h)

theorem or_assoc_backward : ∀ {a b c : Prop}, a ∨ b ∨ c -> (a ∨ b) ∨ c :=
by
  intros a b c h
  induction h with
  | inl h => exact Or.intro_left _ (Or.intro_left _ h)
  | inr h => induction h with
             | inl h => exact Or.intro_left _ (Or.intro_right _ h)
             | inr h => exact Or.intro_right _ h

def mem_reorder : ∀ {x y z: Nat} {tl : List Nat} (h : mem x (y :: z :: tl)), mem x (z :: y :: tl) :=
by
  intros x y z tl h
  let h1 := h
  let h2 := Or.elim h1 (λ p => Or.intro_left (is_eq y x = Bool.true) ( p)) (λ p => Or.intro_right _ p)
  let h3 := or_assoc_forward h2
  let h4 := or_comm_helper h3
  let h5 := or_assoc_backward h4
  exact h5

def subset : List Nat -> List Nat -> Prop :=
  λ s l => List.recOn s True (λ hd tl prev => (mem hd l) ∧ prev)

def subset_nil : ∀ (l : List Nat), subset [] l :=
  λ l => trivial

def subset_cons : ∀ {s l : List Nat} {hd : Nat} (p : mem hd l) (h: subset s l), subset (hd :: s) l := 
  λ {s l} {hd} p h => And.intro p h

def subset_cons_list : ∀ {s l : List Nat} (hd : Nat) (h: subset s l), subset s (hd :: l) :=
by
  intros s l hd h
  induction s with
  | nil => trivial
  | cons _ _ s_ih => let mem1 := And.left h
                     let h2 := s_ih (And.right h)
                     let h3 := mem_cons hd mem1
                     exact And.intro h3 h2

def subset_cons_cons : ∀ (s l : List Nat) (hd : Nat) (h: subset s l), subset (hd :: s) (hd :: l) :=
by
  intros s l hd h
  let h2 := subset_cons_list  hd h
  let h3 := subset_cons (mem_head hd l) h2
  exact h3

def subset_tail : ∀ {l tl : List Nat} {hd : Nat} (h : subset (hd :: tl) l), subset tl l :=
by
  intros l tl hd h
  exact And.right h

theorem and_assoc_forward : ∀ {a b c : Prop}, (a ∧ b) ∧ c -> a ∧ b ∧ c :=
by
  intros a b c h
  exact And.intro h.left.left (And.intro h.left.right h.right)

theorem and_assoc_backward : ∀ {a b c : Prop}, a ∧ b ∧ c ->  (a ∧ b) ∧ c  :=
by
  intros a b c h
  exact And.intro (And.intro h.left h.right.left) h.right.right

theorem and_comm_ : ∀ {a b: Prop}, a ∧ b -> b ∧ a :=
  And.symm

def subset_reorder_s : ∀ {tl l : List Nat} {x y : Nat} (h : subset (x :: y :: tl) l), subset (y :: x :: tl) l :=
by
  intros tl l x y h
  let h1 := And.left (and_assoc_backward h)
  let h2 := And.right (and_assoc_backward h)
  exact and_assoc_forward (And.intro (and_comm_ h1) h2)

def subset_eq : ∀ (l : List Nat), subset l l :=
by
  intro l
  induction l with
  | nil => trivial
  | cons l_hd l_tl l_ih => exact subset_cons_cons l_tl l_tl l_hd l_ih

def subset_reorder : ∀ {s tl : List Nat} {x y : Nat} (h: subset s (x :: y :: tl)), subset s (y :: x :: tl) :=
by
  intros s tl x y h
  induction s with
  | nil => trivial
  | cons _ _ s_ih => let h1 := s_ih (And.right h)
                     let h2 := And.left h
                     let h3 := mem_reorder h2
                     exact And.intro h3 h1

noncomputable instance decidable_bool_eq (b : Bool) : Decidable (b = Bool.false) :=
by
  induction b
  apply isTrue
  apply Eq.refl
  apply isFalse
  intro h
  contradiction

def not_eq_ff_eq_tt {x : Bool} : (¬ x = Bool.false) -> (x = Bool.true) :=
by
  intro h
  induction x with
  | false => trivial
  | true => trivial

def flip_eq {a b : Bool} (p: a = b) : (b = a) :=
by
  exact @Eq.subst Bool (λ x => x = a) a b p (Eq.refl a)

def sorted : List Nat -> Prop :=
  λ l => List.recOn l True (λ hd tl prev => List.recOn tl True (λ hd_tl tl_tl prev_tl => le_eff hd hd_tl = Bool.true ∧ prev) )

def sorted_nil : sorted [] := trivial
def sorted_singleton (x : Nat) : sorted [x] := trivial
def sorted_cons_le (x : Nat) (hd : Nat) (tl: List Nat) (h: sorted (hd :: tl)) (h2: le_eff x hd = Bool.true) : sorted (x :: hd :: tl) :=
  And.intro h2 h
def sorted_tail (hd : Nat) (tl : List Nat) (h: sorted (hd :: tl)) : sorted tl :=
by
  induction tl
  trivial
  exact And.right h

axiom le_eff_of_not_le {a b : Nat}: (le_eff a b = Bool.false) -> (le_eff b a = Bool.true)

noncomputable def insert_sorted (x : Nat) (l : List Nat) : List Nat :=
  List.recOn l [x] (λ hd tl prev => Bool.recOn (le_eff x hd) (hd :: prev) (x :: hd :: tl))

def insert_sorted_subset (x : Nat) (s l : List Nat) (h: subset s l) : subset (insert_sorted x s) (x :: l) :=
by
  induction s with
  | nil => exact (And.intro (mem_head x l) True.intro)
  | cons s_hd s_tl s_ih => cases (decidable_bool_eq (le_eff x s_hd)) with
                           | isFalse h_1 => let h1 := not_eq_ff_eq_tt h_1
                                            exact @Eq.subst Bool (λb => subset (Bool.rec (s_hd :: List.rec [x] (λ (hd : Nat) (tl prev : List Nat) => Bool.rec (hd :: prev) (x :: hd :: tl) (le_eff x hd)) s_tl) (x :: s_hd :: s_tl) b) (x :: l)) Bool.true (le_eff x s_hd) (flip_eq h1) (subset_cons_cons (s_hd :: s_tl) l x h)
                           | isTrue h_1 => apply @Eq.subst Bool (λb => subset (Bool.rec (s_hd :: List.rec [x] (λ (hd : Nat) (tl prev : List Nat) => Bool.rec (hd :: prev) (x :: hd :: tl) (le_eff x hd)) s_tl) (x :: s_hd :: s_tl) b) (x :: l)) Bool.false (le_eff x s_hd) (flip_eq h_1)
                                           let h1 := s_ih (subset_tail h)
                                           let h2 := mem_cons x (And.left h)
                                           exact And.intro h2 h1

def mem_insert_sorted {x : Nat} {l : List Nat} (y : Nat ) (h : mem x l) : mem x (insert_sorted y l) :=
by
  induction l
  exact False.elim (h)
  case cons l_hd l_tl l_ih => cases (decidable_bool_eq (le_eff y l_hd)) with
  | isFalse h_1 => let h_1 := not_eq_ff_eq_tt h_1
                   let h2 := (mem_cons y h)
                   exact @Eq.subst Bool (λ b => mem x (Bool.rec (l_hd :: List.rec [y] (λ (hd : Nat) (tl prev : List Nat) => Bool.rec (hd :: prev) (y :: hd :: tl) (le_eff y hd)) l_tl) (y :: l_hd :: l_tl) b)) Bool.true (le_eff y l_hd) (flip_eq h_1) h2
  | isTrue h_1 => cases (decidable_bool_eq (is_eq l_hd x)) with
                  | isFalse h_2 => apply @Eq.subst Bool (λ b => mem x (Bool.rec (l_hd :: List.rec [y] (λ (hd : Nat) (tl prev : List Nat) => Bool.rec (hd :: prev) (y :: hd :: tl) (le_eff y hd)) l_tl) (y :: l_hd :: l_tl) b)) Bool.false (le_eff y l_hd) (flip_eq h_1)
                                   let h_2 := not_eq_ff_eq_tt h_2
                                   exact (Or.intro_right _ h_2)
                  | isTrue h_2 => apply @Eq.subst Bool (λ b => mem x (Bool.rec (l_hd :: List.rec [y] (λ (hd : Nat) (tl prev : List Nat) => Bool.rec (hd :: prev) (y :: hd :: tl) (le_eff y hd)) l_tl) (y :: l_hd :: l_tl) b)) Bool.false (le_eff y l_hd) (flip_eq h_1)
                                  let h := Or.elim (h) (λp => p) (λ p => False.elim (ff_ne_tt (Eq.trans (flip_eq h_2) p)))
                                  let h1 := Or.intro_left (is_eq l_hd x = Bool.true) (l_ih h)
                                  let h2 := h1
                                  exact h2

def and_true_intro (p : Prop): p -> p ∧ True :=
by
  intro h
  exact And.intro h True.intro

def and_true_elim {p : Prop} : p ∧ True -> p :=
by
  apply And.left

def subset_insert_sorted (x : Nat) (s l : List Nat) (h : subset s l) : subset (x :: s) (insert_sorted x l)  :=
by
  induction s
  case nil => induction l with
              | nil => exact (And.intro (mem_head x []) (True.intro))
              | cons l_hd l_tl l_ih => cases (decidable_bool_eq (le_eff x l_hd)) with
                                       | isFalse  h_1 => let h_1 := not_eq_ff_eq_tt h_1
                                                         apply (and_true_intro (mem x (List.recOn (l_hd :: l_tl) [x] (λ (hd : Nat) (tl prev : List Nat) => Bool.recOn (le_eff x hd) (hd :: prev) (x :: hd :: tl)))))
                                                         apply @Eq.subst Bool (λ b => mem x (Bool.rec (l_hd :: List.rec [x] (λ (hd : Nat) (tl prev : List Nat) => Bool.rec (hd :: prev) (x :: hd :: tl) (le_eff x hd)) l_tl) (x :: l_hd :: l_tl) b)) Bool.true (le_eff x l_hd) (flip_eq h_1)
                                                         exact (mem_head x (l_hd :: l_tl))
                                       | isTrue h_1 => apply (and_true_intro (mem x (List.recOn (l_hd :: l_tl) [x] (λ (hd : Nat) (tl prev : List Nat) => Bool.recOn (le_eff x hd) (hd :: prev) (x :: hd :: tl)))))
                                                       apply @Eq.subst Bool (λ b => mem x (Bool.rec (l_hd :: List.rec [x] (λ (hd : Nat) (tl prev : List Nat) => Bool.rec (hd :: prev) (x :: hd :: tl) (le_eff x hd)) l_tl) (x :: l_hd :: l_tl) b)) Bool.false (le_eff x l_hd) (flip_eq h_1)
                                                       let h1 := l_ih (subset_nil l_tl)
                                                       let h1 := (and_true_elim h1)
                                                       exact (mem_cons l_hd h1)
  case cons s_hd s_tl s_ih => let h2 := s_ih (subset_tail h)
                              let h3 := And.left h
                              let h4 := mem_insert_sorted x h3
                              let h5 := subset_cons h4 h2
                              exact subset_reorder_s h5

def insert_sorted_correct (x : Nat) (l : List Nat) (h: sorted l) : sorted (insert_sorted x l) :=
  @List.recOn Nat (fun l => (∀ (h: sorted l), sorted (insert_sorted x l))) l 
    (λ h: sorted [] => trivial)
    (λ hd tl prev => 
      (λ h: sorted (hd :: tl) => Decidable.recOn (decidable_bool_eq (le_eff x hd))
        (λ h_1 => @Eq.subst Bool (λb => sorted (Bool.rec (hd :: List.rec [x] (λ (hd : Nat) (tl prev : List Nat) => Bool.rec (hd :: prev) (x :: hd :: tl) (le_eff x hd)) tl) (x :: hd :: tl) b)) Bool.true (le_eff x hd) (flip_eq (not_eq_ff_eq_tt h_1)) (sorted_cons_le x hd tl h (not_eq_ff_eq_tt h_1)))
        (λ h_1 => by apply @Eq.subst Bool (λ b => sorted (Bool.rec (hd :: List.rec [x] (λ (hd : Nat) (tl prev : List Nat) => Bool.rec (hd :: prev) (x :: hd :: tl) (le_eff x hd)) tl) (x :: hd :: tl) b)) Bool.false (le_eff x hd) (flip_eq h_1)
                     simp at prev
                     exact (@List.rec Nat (λ l => sorted (hd :: l) -> (sorted l → sorted (insert_sorted x l)) -> (λ (b : Bool) => sorted (Bool.rec (hd :: List.rec [x] (λ (hd : Nat) (tl prev : List Nat) => Bool.rec (hd :: prev) (x :: hd :: tl) (le_eff x hd)) l) [x, hd] b)) Bool.false)       
                      (λ h => λ l_ih => sorted_cons_le hd x [] (sorted_singleton x) (le_eff_of_not_le h_1))

                      (λ l_tl_hd l_tl_tl prev_tl =>
                        (λ h : sorted (hd :: l_tl_hd :: l_tl_tl) =>
                         λ l_ih : sorted (l_tl_hd :: l_tl_tl) → sorted (insert_sorted x (l_tl_hd :: l_tl_tl)) =>
                  Decidable.recOn (decidable_bool_eq (le_eff x l_tl_hd))
                    (λ np => let 
                      h1 := (not_eq_ff_eq_tt np)
                      let h2 := sorted_tail hd (l_tl_hd :: l_tl_tl) h
                      let h3 := sorted_cons_le (x) l_tl_hd l_tl_tl h2 h1
                      let h4 := (le_eff_of_not_le h_1)
                      let h5 := (sorted_cons_le (hd) (x) (l_tl_hd :: l_tl_tl) h3 h4)
                      let h6 := @Eq.subst Bool (λ b1 => sorted (hd :: Bool.rec (l_tl_hd :: List.rec [x] (λ (hd : Nat) (tl prev : List Nat) => Bool.rec (hd :: prev) (x :: hd :: tl) (le_eff x hd)) l_tl_tl) (x :: l_tl_hd :: l_tl_tl) b1)) Bool.true (le_eff x l_tl_hd) (flip_eq h1) h5
                      h6
                    )
                    (λ pp =>
                        @Eq.subst Bool (λ b1 => sorted (hd :: Bool.rec (l_tl_hd :: List.rec [x] (λ (hd : Nat) (tl prev : List Nat) => Bool.rec (hd :: prev) (x :: hd :: tl) (le_eff x hd)) l_tl_tl) (x :: l_tl_hd :: l_tl_tl) b1)) Bool.false (le_eff x l_tl_hd) (flip_eq pp)
                          (
                            let h3 := sorted_tail hd (l_tl_hd :: l_tl_tl) h
                            let h4 := l_ih h3
                            let h5 := And.left h
                            let h6 := @Eq.subst Bool (λ b1 => sorted (Bool.rec (l_tl_hd :: List.rec [x] (λ (hd : Nat) (tl prev : List Nat) => Bool.rec (hd :: prev) (x :: hd :: tl) (le_eff x hd)) l_tl_tl) (x :: l_tl_hd :: l_tl_tl) b1)) (le_eff x l_tl_hd) Bool.false (pp) h4
                            sorted_cons_le (hd) (l_tl_hd) (insert_sorted x l_tl_tl) h6 h5
                          )
                    )
                         ))
                      tl
                     h) prev
          )
        )
      )
      h 

noncomputable def sort : List Nat -> List Nat :=
  λ l => List.recOn l [] (λ hd tl prev => insert_sorted hd prev) 

noncomputable def sort_sorted (l : List Nat) : sorted (sort l) :=
    (List.recOn l (sorted_nil) (λ hd tl ih => insert_sorted_correct hd (sort tl) ih))

noncomputable def subset_sort (l : List Nat) :  subset (l) (sort l)  :=
      (List.recOn l (trivial) (λ hd tl ih => 
        subset_insert_sorted hd tl (sort tl) ih
      ))

noncomputable def sort_subset (l : List Nat) : subset (sort l) (l) :=
      (List.recOn l (trivial) (λ hd tl ih => insert_sorted_subset hd (sort tl) tl ih))

noncomputable def sort_correct (l : List Nat) : sorted (sort l) ∧ subset (l) (sort l) ∧ subset (sort l) (l) :=
  And.intro (sort_sorted l) (And.intro (subset_sort l) (sort_subset l))

end InsertionSort
