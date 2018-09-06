import .knows .problem

@[reducible] def chain_nobody_leaves_core (d : day) : Π (n : ℕ), Prop
| 0     := ¬ knows (d+1) d (is_marked d)
| (n+1) := knows (d+2) (n+d+1) (chain_nobody_leaves_core n)

@[reducible] def chain_nobody_leaves (n_people : ℕ) (d : day) : Prop :=
chain_nobody_leaves_core d (n_people - 1 - d)

@[reducible] def day_conclusion_core (d : day) : Π (n : ℕ), Prop
| 0     := knows (d+1) d (is_marked d)
| (n+1) := knows (d+2) (n+d+1) (¬ is_marked (n+d+1) → day_conclusion_core n)

@[reducible] def day_conclusion (n_people : ℕ) (d : day) : Prop :=
day_conclusion_core d (n_people - 1 - d)
