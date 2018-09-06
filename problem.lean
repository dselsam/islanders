/-
 Description : Tools to construct islanders assumptions for varying numbers of people.
 Copyright   : (c) Daniel Selsam, 2018
 License     : GPL-3
-/

import .util .knows

constant is_marked : person → Prop

@[reducible] def everyone_sees_def : Prop :=
∀ (d₁ d₂ : day) (p₁ p₂ : person), p₂ ≠ p₁ → common_knowledge (is_marked p₂ → knows d₂ p₁ (is_marked p₂)) d₁
                                          ∧ common_knowledge (¬ is_marked p₂ → knows d₂ p₁ (¬ is_marked p₂)) d₁

@[reducible] def oracle_def (n_people : ℕ) : Prop :=
∀ (d : day) (p : person) (k : ℕ), common_knowledge (knows (d+1) p (reduce_or (list.map is_marked (list.range n_people)))) (d+1+k)

@[reducible] def nobody_leaves_def (n_people : ℕ) : Prop :=
∀ (d : day) (p : person), d+1 < n_people → common_knowledge (¬ knows (d+1) p (is_marked p)) (d+1+1)

@[reducible] def with_islanders_assumptions (n_people : ℕ) (prop : Prop) : Prop :=
everyone_sees_def → oracle_def n_people → nobody_leaves_def n_people → prop

@[reducible] def islanders (n_people : ℕ) : Prop :=
with_islanders_assumptions n_people (knows n_people (n_people-1) (is_marked (n_people-1)))
