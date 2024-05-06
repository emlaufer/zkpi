universe u

def even : Nat -> Prop :=
  λ n => @Nat.rec (λ _ => Prop) true (λ np prev => ¬ prev) n

inductive graph {V : Type u} : Type u
| empty : graph
| vertex : forall (v: V) (g: graph), graph
| edge : forall (e: (V × V)), graph -> graph

noncomputable def degree {V: Type u} (g: @graph V) : Nat :=
  graph.recOn g 0 (λ v g p => p) (λ e g p => p + 2)

theorem degree_is_even (V: Type u) (g: @graph V) : even (degree g) :=
by
  induction g with
  | empty => trivial
  | vertex v g g_ih => exact g_ih
  | edge e g g_ih => exact not_not_intro g_ih
