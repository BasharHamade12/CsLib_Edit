import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Order.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Cslib.CPS.Cayley

open scoped ComplexOrder

#check (by infer_instance : NormedField ℂ)
set_option linter.flexible false
set_option linter.style.emptyLine false
set_option linter.deprecated.module false

universe u v

section DiscreteLinearSystem

variable {σ : Type u} {ι : Type v}
variable [TopologicalSpace σ] [NormedAddCommGroup σ] [NormedSpace ℂ σ]
variable [TopologicalSpace ι] [NormedAddCommGroup ι] [NormedSpace ℂ ι]
variable [Inhabited ι]

/-- Discrete-time linear dynamical system with state equation x(k+1) = A·x(k) + B·u(k) -/
structure DiscreteLinearSystemState (σ : Type u) (ι : Type v)
    [TopologicalSpace σ] [NormedAddCommGroup σ] [NormedSpace ℂ σ]
    [TopologicalSpace ι] [NormedAddCommGroup ι] [NormedSpace ℂ ι] where
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

variable {sys : DiscreteLinearSystemState σ ι}

/-- System evolution function from initial state -/
noncomputable def DiscreteLinearSystemState.system_evolution (u : ℕ → ι) : ℕ → σ
  | 0 => sys.x₀
  | k + 1 => sys.a (system_evolution u k) + sys.B (u k)

/-- Discrete state space representation property -/
def DiscreteLinearSystemState.satisfies_state_equation : Prop :=
  ∀ k : ℕ, sys.x (k + 1) = sys.a (sys.x k) + sys.B (sys.u k)


/-- Evolution from zero initial state with given input -/
noncomputable def DiscreteLinearSystemState.evolve_from_zero
   (u : ℕ → ι) (sys : DiscreteLinearSystemState σ ι) : ℕ → σ
  | 0 => 0
  | k + 1 => sys.a (evolve_from_zero u sys k) + sys.B (u k)



/-- Zero input sequence -/
def zero_input : ℕ → ι := fun _ => 0

end DiscreteLinearSystem
