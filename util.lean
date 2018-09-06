/-
 Description : Basic utilities for islanders formalization.
 Copyright   : (c) Daniel Selsam, 2018
 License     : GPL-3
-/

def reduce_or : list Prop → Prop
| [] := false
| [p] := p
| (p::ps) := p ∨ reduce_or ps

lemma sub_one_lt {n : ℕ} (h : n ≥ 1) : n - 1 < n := sorry
lemma one_add_one_eq_2 : (1 : ℕ) + 1 = 2 := rfl
