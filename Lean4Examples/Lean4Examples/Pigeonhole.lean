open Classical

namespace Pigeonhole

noncomputable def add_eff : Nat → Nat → Nat :=
  λ n m => @Nat.rec (λ _ => Nat) n (λ mp prev => Nat.succ prev) m


noncomputable def sub_eff : Nat → Nat → Nat := 
  λ n m => @Nat.rec (λ _ => Nat) n (λ mp prev => @Nat.rec (λ _=> Nat) Nat.zero (λ pprev _ => pprev) prev) m

noncomputable def is_zero : Nat -> Prop :=
  λ n => @Nat.rec (λ _ => Prop) True (λ np prev => False) n

theorem is_zero_succ {n : Nat} : (is_zero n.succ) -> False :=
  λ h => h

theorem is_zero_eq_zero {n : Nat}: (is_zero n) -> n = 0 :=
  Nat.recOn n (λ hp => Eq.refl 0) (λ np hp prev => False.recOn (is_zero_succ prev))

theorem is_zero_zero : (is_zero 0) := by
  trivial

theorem add_eff_is_zero : (is_zero (add_eff 0 0)) := by
  trivial

def sub_eff_is_zero_succ {n m: Nat} : (is_zero (sub_eff n m)) -> (is_zero (sub_eff n m.succ)) :=
  λ h => @Eq.subst Nat 
    (λ a => is_zero (Nat.rec 0 (λ (pprev : Nat) (_x : (λ (_x : Nat) => Nat) pprev) => pprev) a))
     (0) (sub_eff n m) (Eq.symm (is_zero_eq_zero h)) (by trivial)

def sub_eff_is_zero_pred {n m: Nat} : (¬ is_zero (sub_eff n m.succ)) -> (¬ is_zero (sub_eff n m)) :=
  λ h h2 => absurd (sub_eff_is_zero_succ h2) h

def lt_eff : Nat → Nat → Prop := 
  λ m n => is_zero (sub_eff m.succ n)

inductive Nat_list : Type
| nil : Nat_list
| cons : Nat → Nat_list -> Nat_list

noncomputable def list_len : Nat_list -> Nat :=
  λ l => @Nat_list.rec (λ _ => Nat) Nat.zero (λ hd tl prev => prev.succ) l

noncomputable def sum_list : Nat_list → Nat := 
  λ l => @Nat_list.rec (λ _ => Nat) Nat.zero (λ hd tl prev => add_eff hd prev) l

def double_pigeon : Nat_list → Prop :=
  λ l => @Nat_list.rec (λ _ => Prop) False (λ hd tl prev => (lt_eff Nat.zero.succ hd) ∨ prev) l

theorem sub_eff_zero_zero : (is_zero (sub_eff Nat.zero.succ Nat.zero)) → False :=
  λ h => h

-- law of excluded middle
axiom em_eff : ∀ (p : Prop), p ∨ ¬p

-- n >= m , m >= k , n >= k
axiom gt_eff_trans {n m k : Nat} : (¬lt_eff n m) -> (¬lt_eff m k) -> (¬ lt_eff n k)

axiom gt_add_left {n m : Nat} (h: ¬lt_eff n m) (k : Nat) : (¬lt_eff (add_eff k n) (add_eff m k))

axiom gt_add_right {n m : Nat} (h: ¬lt_eff n m) (k : Nat) : (¬lt_eff (add_eff n k) (add_eff m k))

theorem add_gt {a b c d : Nat} : (¬ lt_eff a b) -> (¬lt_eff c d) -> (¬ lt_eff (add_eff a c) (add_eff d b)) :=
  λ h1 h2 => gt_eff_trans (gt_add_right h1 c) (gt_add_left h2 b)

-- if a + 1 < c + d and a >= d, then 1 < c
theorem lt_eff_succ_gt {a c d : Nat} : (lt_eff (add_eff a 1) (add_eff c d)) → (¬ (lt_eff a d)) → (lt_eff 1 c) :=
  λ h1 h2 => Or.recOn (em_eff (lt_eff 1 c)) (λ p => p) (λ np => absurd h1 (add_gt h2 np))

theorem pigeonhole (l : Nat_list) : (lt_eff (list_len l) (sum_list l)) → (double_pigeon l) :=
  Nat_list.rec (sub_eff_zero_zero)
    (λ (l_hd : Nat) (l_tl : Nat_list) (l_ih : lt_eff (list_len l_tl) (sum_list l_tl) → double_pigeon l_tl)
     (h : lt_eff (list_len (Nat_list.cons l_hd l_tl)) (sum_list (Nat_list.cons l_hd l_tl))) =>
       (em_eff (lt_eff (list_len l_tl) (sum_list l_tl))).casesOn
         (λ (h_1 : lt_eff (list_len l_tl) (sum_list l_tl)) =>
            (Or.intro_right (lt_eff Nat.zero.succ l_hd) (l_ih h_1)))
         (λ (h_1 : ¬lt_eff (list_len l_tl) (sum_list l_tl)) =>
            (Or.intro_left
              (double_pigeon l_tl)
              (lt_eff_succ_gt h h_1))))
    l

end Pigeonhole
