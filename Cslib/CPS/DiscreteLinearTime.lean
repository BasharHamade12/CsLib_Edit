import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Complex.Exponential

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real

import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Order.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Cslib.CPS.Cayley



--set_option diagnostics true
open scoped ComplexOrder

-- Trace instance synthesis to debug
--set_option trace.Meta.synthInstance true

-- Test if we can check the instance
#check (by infer_instance : NormedField ℂ)
set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.deprecated.module false

variable {σ ι : Type*}
variable [TopologicalSpace σ] [NormedAddCommGroup σ] [NormedSpace ℂ σ]
variable [TopologicalSpace ι] [NormedAddCommGroup ι] [NormedSpace ℂ ι]
variable [Inhabited ι]

variable (σ ι) in
structure DiscreteLinearSystemState where
  /-- State transition matrix (n×n) -/
  a : σ →L[ℂ] σ
  /-- Input matrix (n×p) -/
  B : ι →L[ℂ] σ
  /-- Initial state -/
  x₀ : σ
  /-- State sequence -/
  x : ℕ → σ
  /-- Input sequence -/
  u : ℕ → ι

-- System evolution function
noncomputable def DiscreteLinearSystemState.system_evolution
(sys : DiscreteLinearSystemState σ ι) : ℕ → σ
  | 0 => sys.x₀
  | k + 1 => sys.a (system_evolution sys k) + sys.B (sys.u k)

-- Discrete State space representatio
def DiscreteLinearSystemState.state_system_equation (sys : DiscreteLinearSystemState σ ι) : Prop :=
  ∀ k : ℕ, sys.x (k + 1) = sys.a (sys.x k) + sys.B (sys.u k)

-- Zero input sequence
def zero_input : ℕ → ι := fun _ => 0






 -- State evolution starting from zero initial state with a given input sequence
noncomputable def evolve_from_zero (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (u : ℕ → ι) : ℕ → σ
  | 0 => 0
  | k + 1 => a (evolve_from_zero a B u k) + B (u k)

/-- Reachability: For any target state x_f ∈ σ, there exists a positive integer k_f
    and an input sequence U = (u[0], u[1], ..., u[k_f-1]) such that starting from
    x[0] = 0, the system reaches x[k_f] = x_f -/
def IsReachable (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) : Prop :=
  ∀ x_f : σ, ∃ (k_f : ℕ) (u : ℕ → ι), k_f > 0 ∧ evolve_from_zero a B u k_f = x_f

/-- A discrete linear system is reachable if its (A, B) matrices satisfy reachability -/
def SystemReachable (sys : DiscreteLinearSystemState σ ι) : Prop :=
  IsReachable sys.a sys.B




open BigOperators

/-- The i-th column block of the controllability matrix: Aⁱ B -/
noncomputable def controllabilityColumn (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (i : ℕ) : ι →L[ℂ] σ :=
  (a ^ i).comp B

def controllabilityMatrix (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (n : ℕ) : Fin n → (ι →L[ℂ] σ) :=
  fun i => (a ^ (i : ℕ)).comp B

open Finset

theorem evolve_from_zero_eq_sum (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (u : ℕ → ι) (k : ℕ) :
    evolve_from_zero a B u k = ∑ j ∈ Finset.range k, (a ^ (k - 1 - j)) (B (u j)) := by

  induction k with
  | zero =>
    -- Base case: x[0] = 0 = empty sum
    simp [evolve_from_zero]
  | succ k ih =>
    simp [evolve_from_zero]
    rw [ih]
    simp
    rw [Finset.sum_range_succ]
    simp


    --simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro x hx

    -- congr 1
  --ext x
    --apply Finset.sum_congr rfl

    have : a.comp (a ^ (k - 1 - x)) = a ^ (k -  x ) := by
      rw [← system_power_multiplication_flopped]
      congr
      have : x < k := Finset.mem_range.mp hx
      omega




    rw [<-ContinuousLinearMap.comp_apply]
    rw [this]


/--
Theorem: Matrix Form Equivalence.
The state at time k_f is equivalent to the product of the Controllability Matrix
and the reversed input sequence.

LHS: x[k_f]
RHS: [B | AB | ... | A^(k_f-1)B] * [u[k_f-1] | u[k_f-2] | ... | u[0]]^T
-/
theorem evolution_eq_matrix_form (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (u : ℕ → ι) (kf : ℕ) :
    evolve_from_zero a B u kf =
    ∑ i : Fin kf, (controllabilityMatrix a B kf i) (u (kf - 1 - (i : ℕ))) := by
    rw [evolve_from_zero_eq_sum]
    simp only [controllabilityMatrix]

-- Then show the sums are equal by reindexing
    rw [← Finset.sum_attach]
    simp


    refine Finset.sum_bij'
      (fun j _ => ⟨kf - 1 - j.val, ?_⟩)
      (fun i _ => ⟨kf - 1 - i.val, ?_⟩)
      ?_ ?_ ?_ ?_ ?_
    · obtain ⟨j, hj⟩ := j; simp at hj ⊢; omega  -- first map well-defined
    · simp; omega                                 -- second map well-defined
    · intros; simp                                -- lands in univ
    · intros; simp                                -- lands in attach
    · intro ⟨j, hj⟩ _; ext; simp at hj ⊢; omega  -- left inverse
    · intro i _; ext; simp; omega                 -- right inverse
    · intro ⟨j, hj⟩ _; simp at hj ⊢;( congr ; omega) -- terms match




def controllabilityColumnSpace (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (k : ℕ) : Submodule ℂ σ :=
  Submodule.span ℂ (⋃ i : Fin k, Set.range (fun v => (a ^ i.val) (B v)))


/-- The set of states reachable in exactly k steps -/
def reachableSetInKSteps (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (k : ℕ) : Set σ :=
  {x : σ | ∃ u : ℕ → ι, evolve_from_zero a B u k = x}

/--
Theorem: The set of states reachable in exactly k steps equals the column space
(range) of the controllability matrix C_k = [A^(k-1)B | ... | AB | B]
-/
theorem reachable_set_eq_controllability_range (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (k : ℕ) (hk : k > 0) :
    reachableSetInKSteps a B k = controllabilityColumnSpace a B k := by
  ext x
  simp [reachableSetInKSteps, controllabilityColumnSpace]
  constructor
  · intro h_reach
    obtain ⟨u, h_reach⟩ := h_reach

    rw [evolution_eq_matrix_form] at h_reach
    rw [← h_reach]
    apply Submodule.sum_mem
    intro i _
    -- Each term (controllabilityMatrix a B k i) (u (k - 1 - ↑i)) is in the span
    -- because it's in Set.range (fun v => (a ^ i.val) (B v))
    apply Submodule.subset_span
    simp only [Set.mem_iUnion, Set.mem_range]
    use i
    use u (k - 1 - ↑i)
    -- Now we just need to show the terms match
    simp [controllabilityMatrix]
  ·
    intro h_span
    -- Use induction on the span
    induction h_span using Submodule.span_induction with
    | mem x hx =>
      -- x is a generator: x = (a ^ i) (B v) for some i, v
      simp only [Set.mem_iUnion, Set.mem_range] at hx
      obtain ⟨i, v, rfl⟩ := hx
      -- Construct input that applies v at the right time
      use fun j => if j = k - 1 - i.val then v else 0
      rw [evolve_from_zero_eq_sum]
      have hi_lt : k - 1 - i.val < k := by omega
      rw [Finset.sum_eq_single_of_mem (k - 1 - i.val) (Finset.mem_range.mpr hi_lt)]
      · -- Main term matches
        simp only [ite_true]
        congr 1
        -- Show k - 1 - (k - 1 - i.val) = i.val
        have hi_bound : i.val < k := i.isLt
        rw [Nat.sub_sub_self (Nat.lt_iff_le_pred hk |>.mp hi_bound)]
      .
        intro b bh b_diff
        rw [if_neg b_diff]
        simp only [ContinuousLinearMap.map_zero]


    | zero =>
      -- Zero is reachable with zero input
      use fun _ => 0
      rw [evolve_from_zero_eq_sum]
      simp only [ContinuousLinearMap.map_zero, Finset.sum_const_zero]
    | add x y _ _ ihx ihy =>
      obtain ⟨ux, hux⟩ := ihx
      obtain ⟨uy, huy⟩ := ihy
      use fun j => ux j + uy j
      rw [evolve_from_zero_eq_sum]
      simp only [ContinuousLinearMap.map_add, Finset.sum_add_distrib]
      rw [← evolve_from_zero_eq_sum, ← evolve_from_zero_eq_sum]
      rw [hux, huy]
    | smul c x _ ihx =>
      -- Scalar multiple of reachable state is reachable
      obtain ⟨ux, hux⟩ := ihx
      use fun j => c • ux j
      rw [evolve_from_zero_eq_sum]
      simp only [ContinuousLinearMap.map_smul]
      rw [← Finset.smul_sum]
      congr 1
      rw [evolve_from_zero_eq_sum] at hux
      exact hux

theorem controllabilityColumnSpace_mono (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    controllabilityColumnSpace a B k₁ ≤ controllabilityColumnSpace a B k₂ := by
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_iUnion, Set.mem_range] at hx ⊢

  obtain ⟨i, v, rfl⟩ := hx
  exact ⟨⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩, v, rfl⟩






theorem cayley_hamilton_controllability' [FiniteDimensional ℂ σ]
    (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (n : ℕ) (hn : n > 0)
    (h_dim : Module.finrank ℂ σ = n) :
    ∀ j ≥ n, ∀ v : ι, (a ^ j) (B v) ∈ controllabilityColumnSpace a B n := by
  intro j hj v
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hjn : j < n
    · -- j < n case: directly in the span
      unfold controllabilityColumnSpace
      apply Submodule.subset_span
      simp only [Set.mem_iUnion, Set.mem_range]
      exact ⟨⟨j, hjn⟩, v, rfl⟩

    · -- j ≥ n: use invariance and induction
      push_neg at hjn
      by_cases hj_zero : j = 0
      · -- Edge case: j = 0 but j ≥ n means n = 0, contradiction with hn
        omega
      · -- j > 0 and j ≥ n
        have hj_pos : j > 0 := Nat.pos_of_ne_zero hj_zero
        have : j = (j - 1) + 1 := by
          omega

        rw [this, pow_succ', ContinuousLinearMap.mul_apply]
        apply controllabilityColumnSpace_invariant a B n h_dim
        apply Submodule.mem_map_of_mem
        have h_pred_ge : j - 1 ≥ n ∨ j - 1 < n := by
          by_cases h : j - 1 ≥ n
          · left; exact h
          · right; push_neg at h; exact h


        cases h_pred_ge with
        | inl h_ge =>
          apply ih
          omega
          exact h_ge
        | inr h_lt =>
          -- j - 1 < n case
          -- unfold controllabilityColumnSpace
          apply Submodule.subset_span
          simp only [Set.mem_iUnion, Set.mem_range]
          exact ⟨⟨j - 1, h_lt⟩, v, rfl⟩





theorem controllabilityColumnSpace_stabilizes
    [FiniteDimensional ℂ σ]
    (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (n : ℕ) (hn : n > 0)
    (h_dim : Module.finrank ℂ σ = n) :
    ∀ k ≥ n, controllabilityColumnSpace a B k = controllabilityColumnSpace a B n := by
  intro k hk
  apply le_antisymm

  .
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx

    obtain ⟨i, v, rfl⟩ := hx
    -- Case split: i < n or i ≥ n
    by_cases hi : i.val < n
    .
      apply Submodule.subset_span
      simp only [Set.mem_iUnion, Set.mem_range]
      exact ⟨⟨i.val, hi⟩, v, rfl⟩

    .
      push_neg at hi
      -- Induction on how far i is above n
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hi
  -- Now hd : i.val = n + d
      induction d with
      | zero =>
        -- hd : i.val = n + 0, i.e., i.val = n
        simp only [Nat.add_zero] at hd
        rw [hd]
        apply cayley_hamilton_controllability' a B n hn h_dim
        trivial


      | succ m ih =>
        have h_ge : n + (m + 1) ≥ n := Nat.le_add_right n (m + 1)
        apply cayley_hamilton_controllability' a B n hn h_dim
        rw [hd]
        trivial
  .
    apply controllabilityColumnSpace_mono
    trivial


/-- The total reachable set is the union of all k-step reachable sets -/
def totalReachableSet (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) : Set σ :=
  ⋃ k : ℕ, reachableSetInKSteps a B k

/-- The total reachable subspace (as a submodule) -/
def totalReachableSubmodule (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) : Submodule ℂ σ :=
  ⨆ k : ℕ, controllabilityColumnSpace a B k

/-- Step 3a: If the system is completely reachable, every state is in the total reachable set -/
theorem reachable_implies_total_reachable_eq_univ (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ)
    (h_reach : IsReachable a B) : totalReachableSet a B = Set.univ := by
  ext x
  simp only [totalReachableSet, Set.mem_iUnion]
  simp only [Set.mem_univ, iff_true]
  -- By definition of IsReachable, for any x there exists k and u such that we reach x
  obtain ⟨k, u, hk_pos, hx⟩ := h_reach x
  exact ⟨k, u, hx⟩

/-- The total reachable set equals the controllability column space at any sufficiently large k -/
theorem totalReachableSubmodule_eq_controllabilityColumnSpace
    [FiniteDimensional ℂ σ]
    (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (n : ℕ) (hn : n > 0)
    (h_dim : Module.finrank ℂ σ = n) :
    totalReachableSubmodule a B = controllabilityColumnSpace a B n := by
  apply le_antisymm
  · -- Show ⨆ k, C_k ≤ C_n
    apply iSup_le
    intro k
    by_cases hk : k ≤ n
    · exact controllabilityColumnSpace_mono a B hk
    · push_neg at hk
      rw [controllabilityColumnSpace_stabilizes a B n hn h_dim k (le_of_lt hk)]
  · -- Show C_n ≤ ⨆ k, C_k
    exact le_iSup (controllabilityColumnSpace a B) n

/-- Step 3b: Complete reachability implies the controllability column space equals the entire space -/
theorem reachable_implies_controllabilityColumnSpace_eq_top
    [FiniteDimensional ℂ σ]
    (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (n : ℕ) (hn : n > 0)
    (h_dim : Module.finrank ℂ σ = n)
    (h_reach : IsReachable a B) :
    controllabilityColumnSpace a B n = ⊤ := by
  rw [← totalReachableSubmodule_eq_controllabilityColumnSpace a B n hn h_dim]
  rw [eq_top_iff]
  intro x _
  -- x is reachable by h_reach
  obtain ⟨k, u, hk_pos, hx⟩ := h_reach x
  -- So x ∈ reachableSetInKSteps a B k
  have h_in_k : x ∈ reachableSetInKSteps a B k := ⟨u, hx⟩
  -- Which equals controllabilityColumnSpace a B k (when k > 0)
  rw [reachable_set_eq_controllability_range a B k hk_pos] at h_in_k
  -- And that's contained in the supremum
  exact Submodule.mem_iSup_of_mem k h_in_k

/--
Step 4: The main theorem (necessity direction).
If the system is completely reachable, then the controllability matrix has full rank.

In the infinite-dimensional setting, "full rank" means the controllability column space
equals the entire state space (i.e., is the top submodule).
-/
theorem reachability_implies_full_rank
    [FiniteDimensional ℂ σ]
    (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (n : ℕ) (hn : n > 0)
    (h_dim : Module.finrank ℂ σ = n)
    (h_reach : IsReachable a B) :
    controllabilityColumnSpace a B n = ⊤ :=
  reachable_implies_controllabilityColumnSpace_eq_top a B n hn h_dim h_reach


/-- Step 4 (finite-dimensional version): Complete reachability implies rank(C) = n
    where n is the dimension of the state space σ -/

theorem reachability_implies_rank_eq_dim
    [FiniteDimensional ℂ σ]
    (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ)
    (h_reach : IsReachable a B)
    (hn : Module.finrank ℂ σ > 0) :
    Module.finrank ℂ (controllabilityColumnSpace a B (Module.finrank ℂ σ)) =
    Module.finrank ℂ σ := by
  have h_top := reachability_implies_full_rank a B (Module.finrank ℂ σ) hn rfl h_reach
  rw [h_top]
  exact finrank_top ℂ σ

/-- Alternative formulation: The controllability submodule has full rank -/
theorem reachability_implies_full_finrank
    [FiniteDimensional ℂ σ]
    (a : σ →L[ℂ] σ) (B : ι →L[ℂ] σ) (n : ℕ)
    (h_dim : Module.finrank ℂ σ = n)
    (hn : n > 0)
    (h_reach : IsReachable a B) :
    Module.finrank ℂ (controllabilityColumnSpace a B n) = n := by
  have h_top := reachability_implies_full_rank a B n hn h_dim h_reach
  rw [h_top]
  rw [finrank_top]
  exact h_dim
