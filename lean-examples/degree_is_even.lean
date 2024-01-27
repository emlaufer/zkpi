universe u

def even : ℕ -> Prop :=
  λ n, @nat.rec (λ _, Prop) true (λ np prev, ¬ prev) n

inductive graph {V : Type u} : Type u
| empty : graph
| vertex : forall (v: V) (g: graph), graph
| edge : forall (e: (V × V)), graph -> graph

def degree {V: Type u} (g: @graph V) : ℕ :=
  graph.rec_on g 0 (λ v g p, p) (λ e g p, p + 2)

theorem degree_is_even (V: Type u) (g: @graph V) : even (degree g) :=
begin
  induction g,
  trivial,
  exact g_ih,
  exact not_not_intro g_ih,
end
