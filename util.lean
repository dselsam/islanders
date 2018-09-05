/-
 Description : Basic utilities for islanders formalization.
 Copyright   : (c) Daniel Selsam, 2018
 License     : GPL-3
-/

def reduce_or : list Prop → Prop
| [] := false
| [p] := p
| (p::ps) := p ∨ reduce_or ps
