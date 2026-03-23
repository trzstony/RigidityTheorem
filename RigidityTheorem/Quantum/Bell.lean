import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

import Quantum.Pauli

open scoped TensorProduct InnerProductSpace

namespace Quantum

open Module

/-!
Bell (EPR) state on two qubits.

This file provides a reusable definition of the standard Bell state
`(|00⟩ + |11⟩) / √2` in the conventions of this folder (`Qubit = EuclideanSpace ℂ (Fin 2)`).
-/

/-- Computational basis ket `|00⟩`. -/
noncomputable abbrev ket00 : Qubit ⊗[ℂ] Qubit := ket0 ⊗ₜ[ℂ] ket0

/-- Computational basis ket `|01⟩`. -/
noncomputable abbrev ket01 : Qubit ⊗[ℂ] Qubit := ket0 ⊗ₜ[ℂ] ket1

/-- Computational basis ket `|10⟩`. -/
noncomputable abbrev ket10 : Qubit ⊗[ℂ] Qubit := ket1 ⊗ₜ[ℂ] ket0

/-- Computational basis ket `|11⟩`. -/
noncomputable abbrev ket11 : Qubit ⊗[ℂ] Qubit := ket1 ⊗ₜ[ℂ] ket1

/-- The standard Bell state `( |00⟩ + |11⟩ ) / √2` on `Qubit ⊗ Qubit`. -/
noncomputable def Φ_plus : Qubit ⊗[ℂ] Qubit :=
  ((Real.sqrt 2 : ℂ)⁻¹) • (ket00 + ket11)

/-- Backwards-compatible name for `Φ_plus`. -/
noncomputable abbrev bellState : Qubit ⊗[ℂ] Qubit := Φ_plus

/-- The standard Bell state `( |00⟩ - |11⟩ ) / √2` on `Qubit ⊗ Qubit`. -/
noncomputable def Φ_minus : Qubit ⊗[ℂ] Qubit :=
  ((Real.sqrt 2 : ℂ)⁻¹) • (ket00 - ket11)

/-- The standard Bell state `( |01⟩ + |10⟩ ) / √2` on `Qubit ⊗ Qubit`. -/
noncomputable def Ψ_plus : Qubit ⊗[ℂ] Qubit :=
  ((Real.sqrt 2 : ℂ)⁻¹) • (ket01 + ket10)

/-- The standard Bell state `( |01⟩ - |10⟩ ) / √2` on `Qubit ⊗ Qubit`. -/
noncomputable def Ψ_minus : Qubit ⊗[ℂ] Qubit :=
  ((Real.sqrt 2 : ℂ)⁻¹) • (ket01 - ket10)



/-! ### Orthonormality of the Bell basis -/

private lemma sqrt2_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  have hR : (Real.sqrt 2 : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  exact_mod_cast hR

private lemma sqrt2_mul_sqrt2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = (2 : ℂ) := by
  have hnonneg : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
  have hR : (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) = (2 : ℝ) := by
    simp only [Nat.ofNat_nonneg, Real.mul_self_sqrt]
  exact_mod_cast hR

private lemma conj_inv_sqrt2_mul_inv_sqrt2_mul_two :
    ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) * (2 : ℂ) = 1 := by
  field_simp [sqrt2_ne_zero]
  simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using sqrt2_mul_sqrt2.symm

@[simp] lemma inner_ket00_ket00 : ⟪ket00, ket00⟫_ℂ = (1 : ℂ) := by
  simp only [ket00, TensorProduct.inner_tmul, inner_ket0_ket0, mul_one]

@[simp] lemma inner_ket01_ket01 : ⟪ket01, ket01⟫_ℂ = (1 : ℂ) := by
  simp only [ket01, TensorProduct.inner_tmul, inner_ket0_ket0, inner_ket1_ket1, mul_one]

@[simp] lemma inner_ket10_ket10 : ⟪ket10, ket10⟫_ℂ = (1 : ℂ) := by
  simp only [ket10, TensorProduct.inner_tmul, inner_ket1_ket1, inner_ket0_ket0, mul_one]

@[simp] lemma inner_ket11_ket11 : ⟪ket11, ket11⟫_ℂ = (1 : ℂ) := by
  simp only [ket11, TensorProduct.inner_tmul, inner_ket1_ket1, mul_one]

@[simp] lemma inner_ket00_ket11 : ⟪ket00, ket11⟫_ℂ = (0 : ℂ) := by
  simp only [ket00, ket11, TensorProduct.inner_tmul, inner_ket0_ket1, mul_zero]

@[simp] lemma inner_ket11_ket00 : ⟪ket11, ket00⟫_ℂ = (0 : ℂ) := by
  simp only [ket11, ket00, TensorProduct.inner_tmul, inner_ket1_ket0, mul_zero]

@[simp] lemma inner_ket01_ket10 : ⟪ket01, ket10⟫_ℂ = (0 : ℂ) := by
  simp only [ket01, ket10, TensorProduct.inner_tmul, inner_ket0_ket1, inner_ket1_ket0, mul_zero]

@[simp] lemma inner_ket10_ket01 : ⟪ket10, ket01⟫_ℂ = (0 : ℂ) := by
  simp only [ket10, ket01, TensorProduct.inner_tmul, inner_ket1_ket0, inner_ket0_ket1, mul_zero]

private lemma inner_smul_smul (s : ℂ) (v w : Qubit ⊗[ℂ] Qubit) :
    ⟪s • v, s • w⟫_ℂ = ((starRingEnd ℂ) s * s) * ⟪v, w⟫_ℂ := by
  rw [inner_smul_right (x := s • v) (y := w) (r := s)]
  rw [inner_smul_left (x := v) (y := w) (r := s)]
  simp [mul_assoc, mul_comm]


@[simp] lemma inner_Φ_plus_Φ_plus : ⟪Φ_plus, Φ_plus⟫_ℂ = (1 : ℂ) := by
  set s : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hsum : ⟪ket00 + ket11, ket00 + ket11⟫_ℂ = (2 : ℂ) := by
    simp [inner_add_left, inner_add_right, -inner_self_eq_norm_sq_to_K]
    norm_num
  calc
    ⟪Φ_plus, Φ_plus⟫_ℂ
        = ⟪s • (ket00 + ket11), s • (ket00 + ket11)⟫_ℂ := by
            simp [Φ_plus, s]
    _ = s * s * ⟪ket00 + ket11, ket00 + ket11⟫_ℂ := by
            simpa [s] using inner_smul_smul (s := s) (v := ket00 + ket11) (w := ket00 + ket11)
    _ = s * s * (2 : ℂ) := by rw [hsum]
    _ = (1 : ℂ) := by
            simpa [s, mul_assoc] using conj_inv_sqrt2_mul_inv_sqrt2_mul_two

@[simp] lemma inner_Φ_minus_Φ_minus : ⟪Φ_minus, Φ_minus⟫_ℂ = (1 : ℂ) := by
  set s : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hsum : ⟪ket00 - ket11, ket00 - ket11⟫_ℂ = (2 : ℂ) := by
    simp [inner_sub_left, inner_sub_right, -inner_self_eq_norm_sq_to_K]
    norm_num
  calc
    ⟪Φ_minus, Φ_minus⟫_ℂ
        = ⟪s • (ket00 - ket11), s • (ket00 - ket11)⟫_ℂ := by
            simp [Φ_minus, s]
    _ = s * s * ⟪ket00 - ket11, ket00 - ket11⟫_ℂ := by
            simpa [s] using inner_smul_smul (s := s) (v := ket00 - ket11) (w := ket00 - ket11)
    _ = s * s * (2 : ℂ) := by rw [hsum]
    _ = (1 : ℂ) := by
            simpa [s, mul_assoc] using conj_inv_sqrt2_mul_inv_sqrt2_mul_two

@[simp] lemma inner_Ψ_plus_Ψ_plus : ⟪Ψ_plus, Ψ_plus⟫_ℂ = (1 : ℂ) := by
  set s : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hsum : ⟪ket01 + ket10, ket01 + ket10⟫_ℂ = (2 : ℂ) := by
    simp [inner_add_left, inner_add_right, -inner_self_eq_norm_sq_to_K]
    norm_num
  calc
    ⟪Ψ_plus, Ψ_plus⟫_ℂ
        = ⟪s • (ket01 + ket10), s • (ket01 + ket10)⟫_ℂ := by
            simp [Ψ_plus, s]
    _ = s * s * ⟪ket01 + ket10, ket01 + ket10⟫_ℂ := by
            simpa [s] using inner_smul_smul (s := s) (v := ket01 + ket10) (w := ket01 + ket10)
    _ = s * s * (2 : ℂ) := by rw [hsum]
    _ = (1 : ℂ) := by
            simpa [s, mul_assoc] using conj_inv_sqrt2_mul_inv_sqrt2_mul_two

@[simp] lemma inner_Ψ_minus_Ψ_minus : ⟪Ψ_minus, Ψ_minus⟫_ℂ = (1 : ℂ) := by
  set s : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hsum : ⟪ket01 - ket10, ket01 - ket10⟫_ℂ = (2 : ℂ) := by
    simp [inner_sub_left, inner_sub_right, -inner_self_eq_norm_sq_to_K]
    norm_num
  calc
    ⟪Ψ_minus, Ψ_minus⟫_ℂ
        = ⟪s • (ket01 - ket10), s • (ket01 - ket10)⟫_ℂ := by
            simp [Ψ_minus, s]
    _ = s * s * ⟪ket01 - ket10, ket01 - ket10⟫_ℂ := by
            simpa [s] using inner_smul_smul (s := s) (v := ket01 - ket10) (w := ket01 - ket10)
    _ = s * s * (2 : ℂ) := by rw [hsum]
    _ = (1 : ℂ) := by
            simpa [s, mul_assoc] using conj_inv_sqrt2_mul_inv_sqrt2_mul_two


@[simp] lemma Φ_plus_norm : ‖Φ_plus‖ = (1 : ℝ) := by
  rw [← Real.sqrt_sq (norm_nonneg Φ_plus)]
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) Φ_plus, inner_Φ_plus_Φ_plus]
  simp [Real.sqrt_one]

@[simp] lemma Φ_minus_norm : ‖Φ_minus‖ = (1 : ℝ) := by
  rw [← Real.sqrt_sq (norm_nonneg Φ_minus)]
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) Φ_minus, inner_Φ_minus_Φ_minus]
  simp [Real.sqrt_one]

@[simp] lemma Ψ_plus_norm : ‖Ψ_plus‖ = (1 : ℝ) := by
  rw [← Real.sqrt_sq (norm_nonneg Ψ_plus)]
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) Ψ_plus, inner_Ψ_plus_Ψ_plus]
  simp [Real.sqrt_one]

@[simp] lemma Ψ_minus_norm : ‖Ψ_minus‖ = (1 : ℝ) := by
  rw [← Real.sqrt_sq (norm_nonneg Ψ_minus)]
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) Ψ_minus, inner_Ψ_minus_Ψ_minus]
  simp [Real.sqrt_one]








@[simp] lemma inner_Φ_plus_Φ_minus : ⟪Φ_plus, Φ_minus⟫_ℂ = (0 : ℂ) := by
  set s : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hsum : ⟪ket00 + ket11, ket00 - ket11⟫_ℂ = (0 : ℂ) := by
    simp only [inner_sub_right, inner_add_left, TensorProduct.inner_tmul, inner_ket0_ket0, mul_one,
      inner_ket1_ket0, mul_zero, add_zero, inner_ket0_ket1, inner_ket1_ket1, zero_add, sub_self]
  calc
    ⟪Φ_plus, Φ_minus⟫_ℂ
        = ⟪s • (ket00 + ket11), s • (ket00 - ket11)⟫_ℂ := by
            simp [Φ_plus, Φ_minus, s]
    _ = s * s * ⟪ket00 + ket11, ket00 - ket11⟫_ℂ := by
            simpa [s] using inner_smul_smul (s := s) (v := ket00 + ket11) (w := ket00 - ket11)
    _ = 0 := by simp [hsum]

@[simp] lemma inner_Φ_plus_Ψ_plus : ⟪Φ_plus, Ψ_plus⟫_ℂ = (0 : ℂ) := by
  set s : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hsum : ⟪ket00 + ket11, ket01 + ket10⟫_ℂ = (0 : ℂ) := by
    simp only [ket00, ket11, ket01, ket10, inner_add_right, inner_add_left,
      TensorProduct.inner_tmul, inner_ket0_ket0, inner_ket0_ket1, mul_zero, inner_ket1_ket0,
      inner_ket1_ket1, mul_one, add_zero]
  calc
    ⟪Φ_plus, Ψ_plus⟫_ℂ
        = ⟪s • (ket00 + ket11), s • (ket01 + ket10)⟫_ℂ := by
            simp [Φ_plus, Ψ_plus, s]
    _ = s * s * ⟪ket00 + ket11, ket01 + ket10⟫_ℂ := by
            simpa [s] using inner_smul_smul (s := s) (v := ket00 + ket11) (w := ket01 + ket10)
    _ = 0 := by simp [hsum]

@[simp] lemma inner_Φ_plus_Ψ_minus : ⟪Φ_plus, Ψ_minus⟫_ℂ = (0 : ℂ) := by
  set s : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hsum : ⟪ket00 + ket11, ket01 - ket10⟫_ℂ = (0 : ℂ) := by
    simp only [ket00, ket11, ket01, ket10, inner_sub_right, inner_add_left,
      TensorProduct.inner_tmul, inner_ket0_ket0, inner_ket0_ket1, mul_zero, inner_ket1_ket0,
      inner_ket1_ket1, mul_one, add_zero, sub_self]
  calc
    ⟪Φ_plus, Ψ_minus⟫_ℂ
        = ⟪s • (ket00 + ket11), s • (ket01 - ket10)⟫_ℂ := by
            simp [Φ_plus, Ψ_minus, s]
    _ = s * s * ⟪ket00 + ket11, ket01 - ket10⟫_ℂ := by
            simpa [s] using inner_smul_smul (s := s) (v := ket00 + ket11) (w := ket01 - ket10)
    _ = 0 := by simp [hsum]

@[simp] lemma inner_Φ_minus_Ψ_plus : ⟪Φ_minus, Ψ_plus⟫_ℂ = (0 : ℂ) := by
  set s : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hsum : ⟪ket00 - ket11, ket01 + ket10⟫_ℂ = (0 : ℂ) := by
    simp only [ket00, ket11, ket01, ket10, inner_add_right, inner_sub_left,
      TensorProduct.inner_tmul, inner_ket0_ket0, inner_ket0_ket1, mul_zero, inner_ket1_ket0,
      inner_ket1_ket1, mul_one, sub_self, add_zero]
  calc
    ⟪Φ_minus, Ψ_plus⟫_ℂ
        = ⟪s • (ket00 - ket11), s • (ket01 + ket10)⟫_ℂ := by
            simp [Φ_minus, Ψ_plus, s]
    _ = s * s * ⟪ket00 - ket11, ket01 + ket10⟫_ℂ := by
            simpa [s] using inner_smul_smul (s := s) (v := ket00 - ket11) (w := ket01 + ket10)
    _ = 0 := by simp [hsum]

@[simp] lemma inner_Φ_minus_Ψ_minus : ⟪Φ_minus, Ψ_minus⟫_ℂ = (0 : ℂ) := by
  set s : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hsum : ⟪ket00 - ket11, ket01 - ket10⟫_ℂ = (0 : ℂ) := by
    simp only [ket00, ket11, ket01, ket10, inner_sub_right, inner_sub_left,
      TensorProduct.inner_tmul, inner_ket0_ket0, inner_ket0_ket1, mul_zero, inner_ket1_ket0,
      inner_ket1_ket1, mul_one, sub_self]
  calc
    ⟪Φ_minus, Ψ_minus⟫_ℂ
        = ⟪s • (ket00 - ket11), s • (ket01 - ket10)⟫_ℂ := by
            simp [Φ_minus, Ψ_minus, s]
    _ = s * s * ⟪ket00 - ket11, ket01 - ket10⟫_ℂ := by
            simpa [s] using inner_smul_smul (s := s) (v := ket00 - ket11) (w := ket01 - ket10)
    _ = 0 := by simp [hsum]

@[simp] lemma inner_Ψ_plus_Ψ_minus : ⟪Ψ_plus, Ψ_minus⟫_ℂ = (0 : ℂ) := by
  set s : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hsum : ⟪ket01 + ket10, ket01 - ket10⟫_ℂ = (0 : ℂ) := by
    simp only [inner_sub_right, inner_add_left, TensorProduct.inner_tmul, inner_ket0_ket0,
      inner_ket1_ket1, mul_one, inner_ket1_ket0, inner_ket0_ket1, mul_zero, add_zero, zero_add,
      sub_self]
  calc
    ⟪Ψ_plus, Ψ_minus⟫_ℂ
        = ⟪s • (ket01 + ket10), s • (ket01 - ket10)⟫_ℂ := by
            simp [Ψ_plus, Ψ_minus, s]
    _ = s * s * ⟪ket01 + ket10, ket01 - ket10⟫_ℂ := by
            simpa [s] using inner_smul_smul (s := s) (v := ket01 + ket10) (w := ket01 - ket10)
    _ = 0 := by simp [hsum]

@[simp] lemma inner_Ψ_plus_Φ_plus : ⟪Ψ_plus, Φ_plus⟫_ℂ = (0 : ℂ) := by
  have h := inner_conj_symm (𝕜 := ℂ) (x := Φ_plus) (y := Ψ_plus)
  rw [inner_Φ_plus_Ψ_plus] at h
  rw [starRingEnd_apply] at h
  exact (star_eq_zero.mp h)

@[simp] lemma inner_Ψ_plus_Φ_minus : ⟪Ψ_plus, Φ_minus⟫_ℂ = (0 : ℂ) := by
  have h := inner_conj_symm (𝕜 := ℂ) (x := Φ_minus) (y := Ψ_plus)
  rw [inner_Φ_minus_Ψ_plus] at h
  rw [starRingEnd_apply] at h
  exact (star_eq_zero.mp h)

@[simp] lemma inner_Ψ_minus_Φ_plus : ⟪Ψ_minus, Φ_plus⟫_ℂ = (0 : ℂ) := by
  have h := inner_conj_symm (𝕜 := ℂ) (x := Φ_plus) (y := Ψ_minus)
  rw [inner_Φ_plus_Ψ_minus] at h
  rw [starRingEnd_apply] at h
  exact (star_eq_zero.mp h)

@[simp] lemma inner_Ψ_minus_Φ_minus : ⟪Ψ_minus, Φ_minus⟫_ℂ = (0 : ℂ) := by
  have h := inner_conj_symm (𝕜 := ℂ) (x := Φ_minus) (y := Ψ_minus)
  rw [inner_Φ_minus_Ψ_minus] at h
  rw [starRingEnd_apply] at h
  exact (star_eq_zero.mp h)

@[simp] lemma inner_Ψ_minus_Ψ_plus : ⟪Ψ_minus, Ψ_plus⟫_ℂ = (0 : ℂ) := by
  have h := inner_conj_symm (𝕜 := ℂ) (x := Ψ_plus) (y := Ψ_minus)
  rw [inner_Ψ_plus_Ψ_minus] at h
  rw [starRingEnd_apply] at h
  exact (star_eq_zero.mp h)




/-! ### Bell basis -/

noncomputable def bellVec : Fin 4 → (Qubit ⊗[ℂ] Qubit)
  | 0 => Φ_plus
  | 1 => Φ_minus
  | 2 => Ψ_plus
  | 3 => Ψ_minus

@[simp] lemma inner_Φ_minus_Φ_plus : ⟪Φ_minus, Φ_plus⟫_ℂ = (0 : ℂ) := by
  have h := inner_conj_symm (𝕜 := ℂ) (x := Φ_plus) (y := Φ_minus)
  -- `h : starRingEnd ℂ ⟪Φ_minus, Φ_plus⟫ = ⟪Φ_plus, Φ_minus⟫`
  rw [inner_Φ_plus_Φ_minus] at h
  -- Convert `starRingEnd` to `star`.
  rw [starRingEnd_apply] at h
  exact (star_eq_zero.mp h)

lemma bellVec_orthonormal : Orthonormal ℂ bellVec := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [bellVec, -inner_self_eq_norm_sq_to_K]

/-- The Bell basis `(Φ₊, Φ₋, Ψ₊, Ψ₋)` as a `Basis (Fin 4) ℂ (Qubit ⊗ Qubit)`. -/
noncomputable def bellBasis : Basis (Fin 4) ℂ (Qubit ⊗[ℂ] Qubit) := by
  classical
  refine Basis.mk (bellVec_orthonormal.linearIndependent) ?_
  have hspan : Submodule.span ℂ (Set.range bellVec) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hb : LinearIndependent ℂ bellVec :=
      bellVec_orthonormal.linearIndependent
    have h_finrank_span :
        finrank ℂ (Submodule.span ℂ (Set.range bellVec)) = Fintype.card (Fin 4) := by
      simpa using (finrank_span_eq_card (R := ℂ) (b := bellVec) hb)
    have h_finrank_total : finrank ℂ (Qubit ⊗[ℂ] Qubit) = Fintype.card (Fin 4) := by
      -- `Qubit = EuclideanSpace ℂ (Fin 2)` has finrank `2`, and finrank tensor-products multiply.
      simp [Qubit, Module.finrank_tensorProduct]
    simpa [h_finrank_total] using h_finrank_span
  exact le_of_eq hspan.symm

@[simp] lemma bellBasis_apply (i : Fin 4) : bellBasis i = bellVec i := by
  classical
  -- `bellBasis` is constructed with `Basis.mk` from the family `bellVec`.
  simp [bellBasis, bellVec]

lemma bellBasis_orthonormal : Orthonormal ℂ (bellBasis : Fin 4 → (Qubit ⊗[ℂ] Qubit)) := by
  classical
  have hcoe : (bellBasis : Fin 4 → (Qubit ⊗[ℂ] Qubit)) = bellVec := by
    funext i
    simp [bellBasis_apply]
  simpa [hcoe] using bellVec_orthonormal

-- To prove that `bellBasis 0` and `bellBasis 1` are orthogonal,
-- use the fact that `bellBasis_orthonormal` gives
-- `⟪bellBasis i, bellBasis j⟫ₖ = if i = j then 1 else 0` (for `k = ℂ`).
-- So the inner product ⟪bellBasis 0, bellBasis 1⟫_ℂ = 0.

example : ⟪bellBasis 0, bellBasis 1⟫_ℂ = 0 := by
  exact Orthonormal.inner_eq_zero bellBasis_orthonormal (by decide)

example : ⟪bellBasis 0, bellBasis 0⟫_ℂ = 1 := by
  simp only [orthonormal_iff_ite.mp bellBasis_orthonormal 0 0, ite_true]

/-! ### CHSH operator and Bell-basis eigenvectors -/

/-- The two-qubit CHSH operator in the symmetrized form:
`K = √2 (Z ⊗ Z + X ⊗ X)`. -/
noncomputable def K :
    (Qubit ⊗[ℂ] Qubit) →ₗ[ℂ] (Qubit ⊗[ℂ] Qubit) :=
  (Real.sqrt 2 : ℂ) • ((pauliZ ⊗ₗ pauliZ) + (pauliX ⊗ₗ pauliX))

/--
Canonical CHSH operator on two qubits:
`Z ⊗ H + Z ⊗ H' + X ⊗ H - X ⊗ H'`, where `H' = ZHZ`.
-/
noncomputable def canonicalCHSH :
    (Qubit ⊗[ℂ] Qubit) →ₗ[ℂ] (Qubit ⊗[ℂ] Qubit) :=
  (pauliZ ⊗ₗ Hadamard) + (pauliZ ⊗ₗ pauliZHZ) +
    (pauliX ⊗ₗ Hadamard) - (pauliX ⊗ₗ pauliZHZ)

theorem K_Φ_plus : K Φ_plus = (2 * Real.sqrt 2 : ℂ) • Φ_plus := by
  classical
  have hL :
      ((pauliZ ⊗ₗ pauliZ) + (pauliX ⊗ₗ pauliX)) (ket00 + ket11) =
        (2 : ℂ) • (ket00 + ket11) := by
    simp [ket00, ket11, TensorProduct.neg_tmul, TensorProduct.tmul_neg, two_smul,
      add_assoc, add_comm, add_left_comm]
  calc
    K Φ_plus
        = (Real.sqrt 2 : ℂ) • (((pauliZ ⊗ₗ pauliZ) + (pauliX ⊗ₗ pauliX)) Φ_plus) := by
            simp [K]
    _ = (Real.sqrt 2 : ℂ) • (((pauliZ ⊗ₗ pauliZ) + (pauliX ⊗ₗ pauliX))
            (((Real.sqrt 2 : ℂ)⁻¹) • (ket00 + ket11))) := by
            simp [Φ_plus]
    _ = (Real.sqrt 2 : ℂ) • (((Real.sqrt 2 : ℂ)⁻¹) •
            (((pauliZ ⊗ₗ pauliZ) + (pauliX ⊗ₗ pauliX)) (ket00 + ket11))) := by
            simp
    _ = (Real.sqrt 2 : ℂ) • (((Real.sqrt 2 : ℂ)⁻¹) • ((2 : ℂ) • (ket00 + ket11))) := by
            simp [hL]
    _ = (2 : ℂ) • (ket00 + ket11) := by
            simp [smul_smul]
    _ = (2 * Real.sqrt 2 : ℂ) • Φ_plus := by
            simp [Φ_plus, smul_smul]

theorem K_Φ_minus : K Φ_minus = 0 := by
  classical
  have hL : ((pauliZ ⊗ₗ pauliZ) + (pauliX ⊗ₗ pauliX)) (ket00 - ket11) = 0 := by
    simp [ket00, ket11, TensorProduct.neg_tmul, TensorProduct.tmul_neg, sub_eq_add_neg,
      add_assoc, add_comm, add_left_comm]
  calc
    K Φ_minus
        = (Real.sqrt 2 : ℂ) • (((pauliZ ⊗ₗ pauliZ) + (pauliX ⊗ₗ pauliX)) Φ_minus) := by
            simp [K]
    _ = (Real.sqrt 2 : ℂ) • (((Real.sqrt 2 : ℂ)⁻¹) •
            (((pauliZ ⊗ₗ pauliZ) + (pauliX ⊗ₗ pauliX)) (ket00 - ket11))) := by
            simp [Φ_minus]
    _ = 0 := by simp [hL]

theorem K_Ψ_plus : K Ψ_plus = 0 := by
  classical
  have hL : ((pauliZ ⊗ₗ pauliZ) + (pauliX ⊗ₗ pauliX)) (ket01 + ket10) = 0 := by
    simp [ket01, ket10, TensorProduct.neg_tmul, TensorProduct.tmul_neg,
      add_assoc, add_comm, add_left_comm]
  calc
    K Ψ_plus
        = (Real.sqrt 2 : ℂ) • (((pauliZ ⊗ₗ pauliZ) + (pauliX ⊗ₗ pauliX)) Ψ_plus) := by
            simp [K]
    _ = (Real.sqrt 2 : ℂ) • (((Real.sqrt 2 : ℂ)⁻¹) •
            (((pauliZ ⊗ₗ pauliZ) + (pauliX ⊗ₗ pauliX)) (ket01 + ket10))) := by
            simp [Ψ_plus]
    _ = 0 := by simp [hL]

theorem K_Ψ_minus : K Ψ_minus = (-2 * Real.sqrt 2 : ℂ) • Ψ_minus := by
  classical
  have hL :
      ((pauliZ ⊗ₗ pauliZ) + (pauliX ⊗ₗ pauliX)) (ket01 - ket10) =
        (-2 : ℂ) • (ket01 - ket10) := by
    simp [ket01, ket10, TensorProduct.neg_tmul, TensorProduct.tmul_neg, two_smul,
      sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  calc
    K Ψ_minus
        = (Real.sqrt 2 : ℂ) • (((pauliZ ⊗ₗ pauliZ) + (pauliX ⊗ₗ pauliX)) Ψ_minus) := by
            simp [K]
    _ = (Real.sqrt 2 : ℂ) • (((Real.sqrt 2 : ℂ)⁻¹) •
            (((pauliZ ⊗ₗ pauliZ) + (pauliX ⊗ₗ pauliX)) (ket01 - ket10))) := by
            simp [Ψ_minus]
    _ = (Real.sqrt 2 : ℂ) • (((Real.sqrt 2 : ℂ)⁻¹) • ((-2 : ℂ) • (ket01 - ket10))) := by
            simp [hL]
    _ = (-2 : ℂ) • (ket01 - ket10) := by
            simp [smul_smul]
    _ = (-2 * Real.sqrt 2 : ℂ) • Ψ_minus := by
            simp [Ψ_minus, smul_smul]

lemma K_as_CHSH :
    (K : (Qubit ⊗[ℂ] Qubit) →ₗ[ℂ] (Qubit ⊗[ℂ] Qubit)) = canonicalCHSH := by
  classical
  -- We expand `canonicalCHSH` and the definitions `Hadamard = (Z + X)/√2` and
  -- `pauliZHZ = (Z - X)/√2`,
  -- and simplify. All mixed terms cancel, leaving `√2 (Z ⊗ Z + X ⊗ X) = K`.
  have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by
    have hs : (Real.sqrt 2 : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    exact_mod_cast hs
  have hmul : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = (2 : ℂ) := by
    have hreal : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
      simp only [Nat.ofNat_nonneg, Real.mul_self_sqrt]
    exact_mod_cast hreal
  have htwo_inv : (2 : ℂ) * (Real.sqrt 2 : ℂ)⁻¹ = (Real.sqrt 2 : ℂ) := by
    rw [← hmul]
    simp [hsqrt]
  have hnegX : (-pauliX : Qubit →ₗ[ℂ] Qubit) = (-1 : ℂ) • pauliX := by
    simp only [neg_smul, one_smul]
  have hCHSH :
      canonicalCHSH =
        (Real.sqrt 2 : ℂ)⁻¹ •
          ((2 : ℂ) • ((pauliZ ⊗ₗ pauliZ) + (pauliX ⊗ₗ pauliX))) := by
    -- Expand `canonicalCHSH` and distribute `⊗ₗ` over `+` and scalar multiples on the right,
    -- but keep scalar multiplication factored (avoid `smul_add`/`smul_sub` expansions).
    simp only [canonicalCHSH, Hadamard, pauliZHZ, sub_eq_add_neg, hnegX,
      TensorProduct.map_add_right, TensorProduct.map_smul_right]
    -- The mixed terms cancel and the remaining duplicates collect into `2 • _`.
    simp [smul_smul]
    abel_nf
    -- Rewrite `2 * T` as `T + T` and `s * 2` as `s + s`, then expand scalar multiplication.
    simp [two_mul, mul_two, smul_add, add_smul, add_assoc]
  -- Finish the main goal by rewriting with `hCHSH` and simplifying the scalar.
  rw [hCHSH]
  simp [K, smul_smul, mul_comm, htwo_inv, smul_add]

end Quantum
