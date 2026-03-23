import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic.Ring

open scoped TensorProduct ComplexConjugate InnerProductSpace

namespace Quantum

notation:100 f " ⊗ₗ " g => TensorProduct.map f g

/-!
Core reusable qubit primitives.

These definitions are shared by both the approximate-rigidity and entropy-bound
developments.
-/

abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

noncomputable def ket0 : Qubit := EuclideanSpace.single (𝕜 := ℂ) (ι := Fin 2) 0 1
noncomputable def ket1 : Qubit := EuclideanSpace.single (𝕜 := ℂ) (ι := Fin 2) 1 1

/- Projector onto the `|0⟩` state. Namely, `proj0 = |0⟩⟨0|`. -/
noncomputable abbrev proj0 : Qubit →ₗ[ℂ] Qubit :=
  (EuclideanSpace.projₗ (𝕜 := ℂ) (ι := Fin 2) 0).smulRight ket0

/- Projector onto the `|1⟩` state. Namely, `proj1 = |1⟩⟨1|`. -/
noncomputable abbrev proj1 : Qubit →ₗ[ℂ] Qubit :=
  (EuclideanSpace.projₗ (𝕜 := ℂ) (ι := Fin 2) 1).smulRight ket1

@[simp] lemma inner_ket0_ket1 : ⟪ket0, ket1⟫_ℂ = 0 := by
  simp [ket0, ket1, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

@[simp] lemma inner_ket1_ket0 : ⟪ket1, ket0⟫_ℂ = 0 := by
  simp [ket1, ket0, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

@[simp] lemma inner_ket0_ket0 : ⟪ket0, ket0⟫_ℂ = 1 := by
  simp [ket0]

@[simp] lemma inner_ket1_ket1 : ⟪ket1, ket1⟫_ℂ = 1 := by
  simp [ket1]

/-- Action of `proj0 = |0⟩⟨0|` on `|0⟩`. -/
lemma proj0_ket0 : proj0 ket0 = ket0 := by
  ext i
  fin_cases i <;> simp [proj0, ket0, EuclideanSpace.single_apply]

/-- Action of `proj0 = |0⟩⟨0|` on `|1⟩`. -/
lemma proj0_ket1 : proj0 ket1 = 0 := by
  ext i
  fin_cases i <;> simp [proj0, ket0, ket1, EuclideanSpace.single_apply]

/-- Action of `proj1 = |1⟩⟨1|` on `|0⟩`. -/
lemma proj1_ket0 : proj1 ket0 = 0 := by
  ext i
  fin_cases i <;> simp [proj1, ket0, ket1, EuclideanSpace.single_apply]

/-- Action of `proj1 = |1⟩⟨1|` on `|1⟩`. -/
lemma proj1_ket1 : proj1 ket1 = ket1 := by
  ext i
  fin_cases i <;> simp [proj1, ket1, EuclideanSpace.single_apply]

/-- `proj0` is idempotent. -/
lemma proj0_idem : proj0 ∘ₗ proj0 = (proj0 : Qubit →ₗ[ℂ] Qubit) := by
  ext v
  simp [proj0, ket0, LinearMap.smulRight_apply, PiLp.projₗ_apply, EuclideanSpace.single_apply]

/-- `proj1` is idempotent. -/
lemma proj1_idem : proj1 ∘ₗ proj1 = (proj1 : Qubit →ₗ[ℂ] Qubit) := by
  ext v
  simp [proj1, ket1, LinearMap.smulRight_apply, PiLp.projₗ_apply, EuclideanSpace.single_apply]

/-- `proj0 ∘ proj1 = 0`. -/
lemma proj0_proj1_zero : proj0 ∘ₗ proj1 = (0 : Qubit →ₗ[ℂ] Qubit) := by
  ext v
  simp [proj0, proj1, ket0, ket1, PiLp.projₗ_apply, EuclideanSpace.single_apply]

/-- `proj1 ∘ proj0 = 0`. -/
lemma proj1_proj0_zero : proj1 ∘ₗ proj0 = (0 : Qubit →ₗ[ℂ] Qubit) := by
  ext v
  simp [proj0, proj1, ket0, ket1, PiLp.projₗ_apply, EuclideanSpace.single_apply]

/-- `proj0 + proj1 = id` on `Qubit`. -/
lemma proj_sum : proj0 + proj1 = (LinearMap.id : Qubit →ₗ[ℂ] Qubit) := by
  ext v i
  fin_cases i
  · simp [proj0, proj1, LinearMap.add_apply, PiLp.projₗ_apply, LinearMap.smulRight_apply,
      ket0, ket1, EuclideanSpace.single_apply]
  · simp [proj0, proj1, LinearMap.add_apply, PiLp.projₗ_apply, LinearMap.smulRight_apply,
      ket0, ket1, EuclideanSpace.single_apply]

/-- `proj0` is self-adjoint. -/
lemma proj0_sa : LinearMap.adjoint (proj0 : Qubit →ₗ[ℂ] Qubit) = proj0 := by
  apply LinearMap.ext
  intro v
  apply ext_inner_right ℂ
  intro w
  simp only [LinearMap.adjoint_inner_left, proj0, LinearMap.smulRight_apply, PiLp.projₗ_apply,
    inner_smul_left, inner_smul_right, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, ket0, map_one, one_mul]
  ring

/-- `proj1` is self-adjoint. -/
lemma proj1_sa : LinearMap.adjoint (proj1 : Qubit →ₗ[ℂ] Qubit) = proj1 := by
  apply LinearMap.ext
  intro v
  apply ext_inner_right ℂ
  intro w
  simp only [LinearMap.adjoint_inner_left, proj1, LinearMap.smulRight_apply, PiLp.projₗ_apply,
    inner_smul_left, inner_smul_right, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, ket1, map_one, one_mul]
  ring

end Quantum
