/-
 Description : Formalization of islanders problem for two people.
 Copyright   : (c) Daniel Selsam, 2018
 License     : GPL-3
-/

import .util .knows .problem

theorem islanders_n2 : islanders 2 :=

assume everyone_sees₁ :
  ∀ (d₁ d₂ : day) (p₁ p₂ : person), p₂ ≠ p₁ → common_knowledge (is_marked p₂ → knows d₂ p₁ (is_marked p₂)) d₁,

assume everyone_sees₂ :
  ∀ (d₁ d₂ : day) (p₁ p₂ : person), p₂ ≠ p₁ → common_knowledge (¬ is_marked p₂ → knows d₂ p₁ (¬ is_marked p₂)) d₁,

assume oracle :
  ∀ (d : day) (p : person) (k : ℕ), common_knowledge (knows (d+1) p (reduce_or (list.map is_marked (list.range 2)))) (d+1+k),

assume nobody_leaves :
  ∀ (d : day) (p : person), d+1 < 2 → common_knowledge (¬ knows (d+1) p (is_marked p)) (d+2),

have H1 : knows 1 1 (¬ is_marked 1 → knows 1 0 (is_marked 0 ∨ is_marked 1)), from
  knows_lam 1 1 1 [] (λ _, oracle 0 0 0 [1]),

have H2 : knows 1 1 (¬ is_marked 1 → knows 1 0 (¬ is_marked 1)), from
  everyone_sees₂ 1 1 0 1 (ne.symm nat.zero_ne_one) [1],

have H3 : knows 1 1 (¬ is_marked 1) → knows 1 1 (knows 1 0 (is_marked 0)), from
  assume h1 : knows 1 1 (¬ is_marked 1),
  show knows 1 1 (knows 1 0 (is_marked 0)), from
  have h2 : knows 1 1 (knows 1 0 (is_marked 0 ∨ is_marked 1)), from knows_mp 0 1 1 1 [] [] H1 h1,
  have h3 : knows 1 1 (knows 1 0 (¬ is_marked 1)), from knows_mp 0 1 1 1 [] [] H2 h1,
  knows_cancel_or 0 _ _ _ [1] [] h2 h3,

have H4 : knows 2 1 (¬ is_marked 1 → knows 1 0 (is_marked 0)), from
  knows_persists 0 1 1 [] (knows_lam 0 1 1 [] H3),

have H5 : knows 2 1 (¬ knows 1 0 (is_marked 0)), from
  nobody_leaves 0 0 (nat.lt_succ_self 1) [1],

show knows 2 1 (is_marked 1), from
  knows_dneg 0 _ _ [] (knows_cancel_imp 0 0 _ _ [] [] H4 H5)
