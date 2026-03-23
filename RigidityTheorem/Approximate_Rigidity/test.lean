import Approximate_Rigidity.BasicDefs


import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Trace.Defs


import Approximate_Rigidity.Isometries

open scoped TensorProduct Pauli InnerProductSpace ComplexConjugate
open Quantum


/-!
This file is a scratchpad for experimenting with mathlib APIs.

Below are the three “standard” traces in mathlib’s linear algebra / ring theory hierarchy:

1. `Matrix.trace` : trace of a square matrix (sum of diagonal entries).
2. `LinearMap.trace` : trace of an endomorphism of a finite free module.
3. `Algebra.trace` : trace of an element in a (finite) commutative `R`-algebra, defined as the
   trace of the `R`-linear map “left multiplication by that element”.

For each definition we give small, self-contained examples.
-/

open scoped Matrix

namespace Approximate_Rigidity

section MatrixTrace

open Matrix

-- `Matrix.trace` is defined in `Mathlib/LinearAlgebra/Matrix/Trace.lean`.
#check Matrix.trace
#check Matrix.traceAddMonoidHom
#check Matrix.traceLinearMap

-- Concrete computation on `2 × 2` matrices (uses `Matrix.trace_fin_two_of`).
example : Matrix.trace (R := ℤ) (n := Fin 2) !![1, 2; 3, 4] = 5 := by
  simp [Matrix.trace_fin_two_of]

-- Dot-notation also works: `A.trace` is `Matrix.trace A`.
example (A : Matrix (Fin 2) (Fin 2) ℤ) : A.trace = Matrix.trace A :=
  rfl

end MatrixTrace

section LinearMapTrace

open LinearMap

-- `LinearMap.trace` is defined in `Mathlib/LinearAlgebra/Trace.lean`.
#check LinearMap.trace
#check LinearMap.trace_id
#check LinearMap.trace_mul_comm

-- Our `Qubit` space is `Fin 2 → ℂ`, so the trace of the identity is `2`.
example : LinearMap.trace ℂ Qubit LinearMap.id = (2 : ℂ) := by
  -- `trace_id` rewrites the trace to `finrank`, and `simp` computes `finrank ℂ (Fin 2 → ℂ) = 2`.
  simp [Qubit]

-- `Matrix.trace` and `LinearMap.trace` agree under the matrix/linear-map equivalence.
-- (`A.toLin'` turns a matrix into a linear map on `ι → R`.)
example (A : Matrix (Fin 2) (Fin 2) ℂ) :
    LinearMap.trace ℂ _ A.toLin' = A.trace := by
  simp

end LinearMapTrace

-- Example: using `obtain` to destructure an existential statement.
example : ∃ n : ℕ, n > 0 := by
  -- There exists some natural number greater than 0, for example 1.
  use 1
  simp

example : ∃ n m : ℕ, n < m := by
  -- We can produce a pair of numbers.
  use 2, 3
  norm_num

example : ∃ n : ℕ, n > 5 := by
  -- Now suppose we want to extract the witness using `obtain`.
  have h := exists_gt 5
  obtain ⟨w, hw⟩ := h
  -- Now `w : ℕ` and `hw : w > 5` are available.
  use w

-- `obtain` can also split up conjunctions or unique existence statements:
example (h : 2 < 5 ∧ 0 ≤ 7) : 2 < 5 := by
  obtain ⟨h₁, h₂⟩ := h
  exact h₁

end Approximate_Rigidity

namespace Approximate_Rigidity



noncomputable def cConst : Real := 16 * Real.sqrt 2

section

section ApproximateAnticomm
variable {H_A H_B : Type*}
variable [NormedAddCommGroup H_A] [NormedAddCommGroup H_B]
variable [InnerProductSpace ℂ H_A] [InnerProductSpace ℂ H_B]
variable [FiniteDimensional ℂ H_A] [FiniteDimensional ℂ H_B]
variable (S : CHSHStrategy H_A H_B)
variable (sigma : H_A →ₗ[ℂ] H_A)
variable (tau : H_B →ₗ[ℂ] H_B)
variable (epsilon : Real)


end ApproximateAnticomm

end

end Approximate_Rigidity
