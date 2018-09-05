/-
 Description : Tools to construct islanders assumptions for varying numbers of people.
 Copyright   : (c) Daniel Selsam, 2018
 License     : GPL-3
-/

import .util .knows

constant is_marked : person → Prop

@[reducible] def mk_everyone_sees₁ (n_people : ℕ) : Prop :=
∀ (d₁ d₂ : day) (p₁ p₂ : person), p₂ ≠ p₁ → common_knowledge (is_marked p₂ → knows d₂ p₁ (is_marked p₂)) d₁

@[reducible] def mk_everyone_sees₂ (n_people : ℕ) : Prop :=
∀ (d₁ d₂ : day) (p₁ p₂ : person), p₂ ≠ p₁ → common_knowledge (¬ is_marked p₂ → knows d₂ p₁ (¬ is_marked p₂)) d₁

@[reducible] def mk_nobody_leaves (n_people : ℕ) : Prop :=
∀ (d : day) (p : person), d+1 < n_people → common_knowledge (¬ knows (d+1) p (is_marked p)) (d+2)

@[reducible] def mk_oracle (n_people : ℕ) : Prop :=
∀ (d : day) (p : person) (k : ℕ), common_knowledge (knows (d+1) p (reduce_or (list.map is_marked (list.range n_people)))) (d+1+k)
