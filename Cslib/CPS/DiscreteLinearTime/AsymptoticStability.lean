import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Order.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Cslib.CPS.DiscreteLinearTime.Basic
import Cslib.CPS.DiscreteLinearTime.Cayley

open scoped ComplexOrder

variable {σ ι : Type*}
variable [NormedAddCommGroup σ] [NormedSpace ℂ σ]
variable [NormedAddCommGroup ι] [NormedSpace ℂ ι]




-- System evolution function
noncomputable def system_evolution (sys : DiscreteLinearSystemState σ ι) : ℕ → σ
  | 0 => sys.x₀
  | k + 1 => sys.a (system_evolution sys k) + sys.B (sys.u k)

-- Discrete State space representatio
def state_system_equation (sys : DiscreteLinearSystemState σ ι) : Prop :=
  ∀ k : ℕ, sys.x (k + 1) = sys.a (sys.x k) + sys.B (sys.u k)






-- Lemma: State evolution under zero input
-- Lemma: State evolution under zero input
lemma state_evolution_zero_input (sys : DiscreteLinearSystemState σ ι)
 (h_init : sys.x 0 = sys.x₀)
 (h_state : state_system_equation sys)
 (h_zero_input : sys.u = zero_input) :
 ∀ k, sys.x k = (sys.a ^ k) sys.x₀ := by
  intro k
  induction k with
 | zero =>
   simp [pow_zero, h_init]
 | succ k ih =>
   have h1 : sys.x (k + 1) = sys.a (sys.x k) + sys.B (sys.u k) := h_state k
   rw [ih] at h1
   rw [h_zero_input] at h1
   unfold zero_input at h1
   simp [ContinuousLinearMap.map_zero] at h1
   rw [h1]
-- Now we need to show: sys.a ((sys.a ^ k) sys.x₀) = (sys.a ^ (k + 1)) sys.x₀
   rw [←ContinuousLinearMap.comp_apply]
   congr 1
   rw [system_power_multiplication_flopped]






-- Original theorem: Bound on state norm
theorem bound_x_norm
    (sys : DiscreteLinearSystemState σ ι)
    (hx : ∀ k, sys.x k = (sys.a ^ k) sys.x₀) (N : ℕ) :
    ∀ k, N < k → ‖sys.x k‖ ≤ ‖sys.a ^ k‖ * ‖sys.x₀‖ := by
  intro k hk
  -- Use the assumption hx to rewrite sys.x k
  rw [hx k]
  exact ContinuousLinearMap.le_opNorm (sys.a ^ k) sys.x₀

-- Definition: Spectral radius less than one
def spectral_radius_less_than_one (a : σ →L[ℂ] σ) : Prop :=
  spectralRadius ℂ a < 1

-- Theorem: If spectral radius of 'a' is less than one , then the gelfand formula tends to a limit less than one
theorem gelfand_le_one_when_spectral_radius_le_one
    [CompleteSpace σ] (a : σ →L[ℂ] σ) :
    spectral_radius_less_than_one a →
    Filter.limsup (fun (n : ℕ) => (‖a ^ n‖₊ : ENNReal) ^ (1 / n : ℝ)) Filter.atTop < 1 := by
  intro h_spectral
  unfold spectral_radius_less_than_one at h_spectral
  have h_gelfand := spectrum.limsup_pow_nnnorm_pow_one_div_le_spectralRadius a
  convert lt_of_le_of_lt h_gelfand h_spectral



-- If the gelfand formula tends to a limit less than one, then there exists  r < 1 such that gelfand is less than r , forall k > some N
theorem gelfand_eventually_bounded [CompleteSpace σ]
    (a : σ →L[ℂ] σ) (h : Filter.limsup (fun n : ℕ ↦ (‖a ^ n‖₊ : ENNReal) ^ (1 / n : ℝ)) Filter.atTop < 1) :
    ∃ (r : ENNReal) (N : ℕ), 0 < r ∧ r < 1 ∧ ∀ (k : ℕ), N < k → (‖a ^ k‖₊ : ENNReal) ^ (1 / k : ℝ) < r :=
by
  obtain ⟨r, h_limsup_lt_r, h_r_lt_one⟩ := exists_between h
  have r_pos : 0 < r := lt_of_le_of_lt (zero_le _) h_limsup_lt_r

  have eventually_lt := Filter.eventually_lt_of_limsup_lt h_limsup_lt_r


  rw [Filter.eventually_atTop] at eventually_lt
  obtain ⟨N, hN⟩ := eventually_lt

  use r, N
  refine ⟨r_pos, h_r_lt_one, fun k hk => hN k (Nat.le_of_lt hk)⟩


-- forall 0 < r < 1 and forall k > some N , if a^k < r^k  then a^k tends to zero
theorem power_to_zero [CompleteSpace σ] (sys : DiscreteLinearSystemState σ ι)
  (r : ENNReal) (N : ℕ)
  (r_pos : 0 < r)
  (r_lt_one : r < 1)
  (h_power : ∀ (k : ℕ), N < k → (‖sys.a ^ k‖₊ : ENNReal) < r ^ k) :
  Filter.Tendsto (fun k => ‖sys.a ^ k‖) Filter.atTop (nhds 0) := by


  -- first we prove that the sequence (r^n) tends to zero
  have r_real_zero : Filter.Tendsto (fun n => (r ^ n).toReal) Filter.atTop (nhds 0) := by
    simp
    cases r with
    | top => simp
    | coe x =>
      simp
      exact ENNReal.coe_lt_one_iff.mp r_lt_one

  --rewrite filter limit notation as notation with epsilon and distance norm
  rw [Metric.tendsto_atTop]
  intro ε ε_pos
  --similar to above rewrite , but for r^n
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp r_real_zero ε ε_pos

  use max N N₁ + 1
  intro k hk -- forall k > max N N₁ + 1


  -- get comparison of k with N and N₁
  have hkN : N < k := lt_of_le_of_lt (le_max_left N N₁) (Nat.lt_of_succ_le hk)
  have hkN₁ : N₁ ≤ k := le_trans (le_max_right N N₁) (Nat.le_of_succ_le hk)



  have h_bound := h_power k hkN
  have h_r_small := hN₁ k hkN₁

  simp

  simp at h_r_small

  have h_r_ennreal : (r ^ k).toReal < ε := by
    rw [ENNReal.toReal_pow]
    exact h_r_small

  --proving that r^k is not infinity
  have h_finite : (r ^ k) ≠ ⊤ := by
    simp only [ne_eq, ENNReal.pow_eq_top_iff]
    intro h
    cases h with --consider r = infinity , prove it is less than infinity , then contradiction
    | intro h_r_top h_k_ne_zero =>
      have : r < ⊤ := r_lt_one.trans_le le_top
      exact ne_of_lt this h_r_top

  calc ‖sys.a ^ k‖
  = (‖sys.a ^ k‖₊ : ℝ) := by simp
  _ = (↑‖sys.a ^ k‖₊ : ENNReal).toReal := by simp
  _ < (r ^ k).toReal := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top h_finite).mpr h_bound
  _ < ε := h_r_ennreal






-- Main theorem : If the spectral radius of the system matrix is less than one and the input sequence is null, then the state sequence converges to zero.
theorem asymptotic_stability_discrete [CompleteSpace σ] (sys : DiscreteLinearSystemState σ ι)
  (h_init : sys.x 0 = sys.x₀)
  (h_state : state_system_equation sys)
  (h_zero_input : sys.u = zero_input)
  (h_spectral : spectral_radius_less_than_one sys.a) :
  Filter.Tendsto (fun k => ‖sys.x k‖) Filter.atTop (nhds 0) := by

  -- Step 1: Apply Gelfand's spectral radius formula for the input sequence sys.a
  have h_gelfand := spectrum.limsup_pow_nnnorm_pow_one_div_le_spectralRadius sys.a

  -- Step 2: Show that limsup of ‖a^n‖^(1/n) is less than 1
  have h_gelfand_le_one : Filter.limsup (fun (n : ℕ) => (‖sys.a ^ n‖₊ : ENNReal) ^ (1 / n : ℝ)) Filter.atTop < 1 := by
      unfold spectral_radius_less_than_one at h_spectral
      refine lt_of_le_of_lt ?_ h_spectral
      exact h_gelfand

  -- Step 3: Find 0 < r < 1 such that eventually ‖a^k‖^(1/k) < r
  have eventually_bounded := gelfand_eventually_bounded sys.a h_gelfand_le_one
  obtain ⟨r, N, r_pos, r_lt_one, h_bound⟩ := eventually_bounded

  -- Step 4: Prove that ‖a^k‖ < r^k for all k > N
  have h_power : ∀ (k : ℕ), N < k → ↑‖sys.a ^ k‖₊ < r ^ k := by
      intros k' hk'
      specialize h_bound k' hk'
      -- k' must be positive since k' > N ≥ 0
      have h_k'_pos : 0 < k' := Nat.zero_lt_of_lt hk'
      -- Prepare for exponent manipulation: 1/k' * k' = 1
      have h_inv_k' : (k' : ℝ)⁻¹ * k' = 1 := by
        field_simp

      -- Raise both sides of ‖a^k'‖^(1/k') < r to the k'-th power
      have h_pow : (↑‖sys.a ^ k'‖₊ ^ (1 / k' : ℝ)) ^ (k' : ℝ) < r ^ k' := by
        rw [← ENNReal.rpow_natCast r k']
        exact ENNReal.rpow_lt_rpow h_bound (Nat.cast_pos.mpr h_k'_pos)

      -- Simplify the left side: (x^(1/k'))^k' = x^(1/k' * k') = x^1 = x
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at h_pow
      simp at h_pow
      rw [h_inv_k'] at h_pow
      simp at h_pow
      exact h_pow

  -- Step 5: Express state evolution in terms of powers of a
  have hx : ∀ k, sys.x k = (sys.a ^ k) sys.x₀ :=
      state_evolution_zero_input sys h_init h_state h_zero_input

  -- Step 6: Show that ‖a^k‖ → 0 as k → ∞
  have pow_zero : Filter.Tendsto (fun k => ‖sys.a ^ k‖) Filter.atTop (nhds 0) :=
      power_to_zero sys r N r_pos r_lt_one h_power

  -- Step 7: Rewrite goal using state evolution formula
  simp only [hx]

  -- Step 8: Use operator norm inequality: ‖Ax‖ ≤ ‖A‖ * ‖x‖
  have h_norm_eq : ∀ k, ‖(sys.a ^ k) sys.x₀‖ ≤ ‖sys.a ^ k‖ * ‖sys.x₀‖ :=
    fun k => ContinuousLinearMap.le_opNorm (sys.a ^ k) sys.x₀

  -- Step 9: Show that ‖a^k‖ * ‖x₀‖ → 0 as k → ∞
  have h_prod_zero : Filter.Tendsto (fun k => ‖sys.a ^ k‖ * ‖sys.x₀‖) Filter.atTop (nhds 0) := by
    rw [← zero_mul ‖sys.x₀‖]
    exact Filter.Tendsto.mul_const ‖sys.x₀‖ pow_zero

  -- Step 10: Conclude by squeeze theorem
  -- 0 ≤ ‖(a^k)x₀‖ ≤ ‖a^k‖ * ‖x₀‖ and both bounds → 0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds)
    h_prod_zero
    (fun k => norm_nonneg _)
    h_norm_eq
