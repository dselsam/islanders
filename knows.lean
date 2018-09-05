/-
 Description : Axiomization of dynamic knowledge among set of agents.
 Copyright   : (c) Daniel Selsam, 2018
 License     : GPL-3
-/

import .util
open list

@[reducible] def person := nat
@[reducible] def day := nat

constant knows (d : day) (p : person) (f : Prop) : Prop

@[reducible] def knows_chain (f : Prop) (d : day) : list person → Prop
| []      := f
| (p::ps) := knows d p (knows_chain ps)

@[reducible] def common_knowledge (f : Prop) (d : day) : Prop :=
  ∀ (ps : list person), knows_chain f d ps

namespace knows_axioms

variables {f f₁ f₂ : Prop} (fp : person → Prop) (d d₁ d₂ : day) (p p₁ p₂ : person) (ps : list person) (k : ℕ)

axiom knows_persists : common_knowledge (knows d₂ p f → knows (d₂+1) p f) d₁
axiom knows_lam      : common_knowledge ((knows d₂ p f₁ → knows d₂ p f₂) → knows d₂ p (f₁ → f₂)) d₁
axiom knows_mp       : common_knowledge (knows_chain (knows d₂ p (f₁ → f₂)) d₁ ps
                                         → knows_chain (knows d₂ p f₁) d₁ ps → knows_chain (knows d₂ p f₂) d₁ ps) d

axiom knows_cancel_imp   : common_knowledge (knows_chain (knows d₂ p (f₁ → f₂)) d₁ ps
                                           → knows_chain (knows d₂ p (¬ f₂)) d₁ ps → knows_chain (knows d₂ p (¬ f₁)) d₁ ps) d

axiom knows_cancel_or      : common_knowledge (knows_chain (knows d₂ p (f₁ ∨ f₂)) d₁ ps
                                       → knows_chain (knows d₂ p (¬ f₂)) d₁ ps → knows_chain (knows d₂ p f₁) d₁ ps) d

axiom knows_dneg     : common_knowledge (knows d₂ p (¬ ¬ f) → knows d₂ p f) d₁

end knows_axioms
export knows_axioms
