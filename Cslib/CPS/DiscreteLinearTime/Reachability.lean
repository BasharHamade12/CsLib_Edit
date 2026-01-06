import Cslib.CPS.DiscreteLinearTime.Basic

universe u v

variable {σ : Type u} {ι : Type v}
variable [TopologicalSpace σ] [NormedAddCommGroup σ] [NormedSpace ℂ σ]
variable [TopologicalSpace ι] [NormedAddCommGroup ι] [NormedSpace ℂ ι]
variable {sys : DiscreteLinearSystemState σ ι}


/-- Reachability: For any target state x_f ∈ σ, there exists a positive integer k_f
    and an input sequence U = (u[0], u[1], ..., u[k_f-1]) such that starting from
    x[0] = 0, the system reaches x[k_f] = x_f -/
def DiscreteLinearSystemState.IsReachable : Prop :=
  ∀ x_f : σ, ∃ (k_f : ℕ) (u : ℕ → ι) , k_f > 0 ∧
  DiscreteLinearSystemState.evolve_from_zero u sys k_f = x_f

/-- The set of states reachable in exactly k steps -/
def DiscreteLinearSystemState.reachableSetInKSteps (sys : DiscreteLinearSystemState σ ι) (k : ℕ) : Set σ :=
  {x : σ | ∃ u : ℕ → ι, DiscreteLinearSystemState.evolve_from_zero u sys k = x}


def DiscreteLinearSystemState.totalReachableSet  (sys : DiscreteLinearSystemState σ ι) : Set σ :=
  ⋃ k : ℕ, reachableSetInKSteps sys k
