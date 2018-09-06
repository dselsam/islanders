/-
 Description : Draft sketch of proof for general case, using n=3 as an example.
 Copyright   : (c) Daniel Selsam, 2018
 License     : GPL-3
-/

import .util .knows .problem .helpers
open nat

@[reducible] def n_people : ℕ := succ (succ (succ zero))

-- Thanks to @tinarwhite for suggesting we first prove this inductive invariant
lemma islanders_puzzle_core :
  with_islanders_assumptions n_people (∀ (d : day), d < n_people → day_conclusion n_people d) :=
assume everyone_sees oracle nobody_leaves,

have H_base : day_conclusion n_people 0, from
  show knows 2 2 (¬is_marked 2 → knows 2 1 (¬is_marked 1 → knows 1 0 (is_marked 0))), from
  have h1 : knows 2 2 (knows 2 1 (¬ is_marked 1 → knows 1 0 (¬ is_marked 1))), from sorry,
  have h2 : knows 2 2 (¬ is_marked 2 → knows 2 1 (knows 1 0 (¬ is_marked 2))), from sorry,
  have h3 : knows 2 2 (¬ is_marked 2 → knows 2 1 (¬ is_marked 1 → knows 1 0 (¬ is_marked 1 ∧ ¬ is_marked 2))), from sorry,
  sorry,

have H_step : ∀ (d : day), (d < n_people → day_conclusion n_people d) → d + 1 < n_people → day_conclusion n_people (d + 1), from
  assume d : day,
  assume IH : d < n_people → day_conclusion n_people d,
  assume d_small : d + 1 < n_people,
  show day_conclusion n_people (d + 1), from
  sorry,

λ d, nat.rec (λ _, H_base) H_step d

theorem islanders_puzzle : islanders n_people :=
assume everyone_sees oracle nobody_leaves,

show day_conclusion n_people (n_people - 1), from

suffices H_suffices : ∀ (d : day), d < n_people → day_conclusion n_people d, from
  H_suffices (n_people - 1) (nat.lt_succ_self _),

islanders_puzzle_core everyone_sees oracle nobody_leaves
