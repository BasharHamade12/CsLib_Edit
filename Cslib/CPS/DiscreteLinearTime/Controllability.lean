import Cslib.CPS.DiscreteLinearTime.Basic
import Cslib.CPS.DiscreteLinearTime.Reachability
import Cslib.CPS.DiscreteLinearTime.Cayley

universe u v

-- 1. FIX: Add these variables so Lean knows σ and ι are normed spaces
variable {σ : Type u} {ι : Type v}
variable [TopologicalSpace σ] [NormedAddCommGroup σ] [NormedSpace ℂ σ]
variable [TopologicalSpace ι] [NormedAddCommGroup ι] [NormedSpace ℂ ι]
variable {sys : DiscreteLinearSystemState σ ι}

open BigOperators Finset

/-- The i-th column block of the controllability matrix: Aⁱ B -/
noncomputable def controllabilityColumn (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (i : ℕ) : ι →L[ℂ] σ :=
  (a ^ i).comp B

def controllabilityMatrix (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (n : ℕ) : Fin n → (ι →L[ℂ] σ) :=
  fun i => (a ^ (i : ℕ)).comp B

theorem evolve_from_zero_eq_sum (k : ℕ) :
   DiscreteLinearSystemState.evolve_from_zero sys k =
     ∑ j ∈ Finset.range k, (sys.a ^ (k - 1 - j)) (sys.B (sys.u j)) := by

    induction k with
    | zero =>
      -- Base case: x[0] = 0 = empty sum
      simp [DiscreteLinearSystemState.evolve_from_zero]

    | succ k ih =>
      simp [DiscreteLinearSystemState.evolve_from_zero]
      rw [ih]
      simp
      rw [Finset.sum_range_succ]
      simp


      --simp only [Nat.add_sub_cancel]
      apply Finset.sum_congr rfl
      intro x hx

      have : sys.a.comp (sys.a ^ (k - 1 - x)) = sys.a ^ (k -  x ) := by
        rw [← system_power_multiplication_flopped]
        congr
        have : x < k := Finset.mem_range.mp hx
        omega

      rw [<-ContinuousLinearMap.comp_apply]
      rw [this]
