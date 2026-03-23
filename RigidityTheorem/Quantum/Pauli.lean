import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.InnerProductSpace.PiL2

import Quantum.Qubit

open Complex
open Matrix
open scoped Matrix

namespace Pauli

abbrev sigma0 : Matrix (Fin 2) (Fin 2) ℂ := 1
abbrev sigma1 : Matrix (Fin 2) (Fin 2) ℂ := !![(0 : ℂ), 1; 1, 0]
abbrev sigma2 : Matrix (Fin 2) (Fin 2) ℂ := !![(0 : ℂ), -Complex.I; Complex.I, 0]
abbrev sigma3 : Matrix (Fin 2) (Fin 2) ℂ := !![(1 : ℂ), 0; 0, -1]

@[simp] lemma sigma0_apply00 : sigma0 0 0 = (1 : ℂ) := by simp [sigma0]
@[simp] lemma sigma0_apply01 : sigma0 0 1 = (0 : ℂ) := by simp [sigma0]
@[simp] lemma sigma0_apply10 : sigma0 1 0 = (0 : ℂ) := by simp [sigma0]
@[simp] lemma sigma0_apply11 : sigma0 1 1 = (1 : ℂ) := by simp [sigma0]

@[simp] lemma sigma1_apply00 : sigma1 0 0 = (0 : ℂ) := by simp [sigma1]
@[simp] lemma sigma1_apply01 : sigma1 0 1 = (1 : ℂ) := by simp [sigma1]
@[simp] lemma sigma1_apply10 : sigma1 1 0 = (1 : ℂ) := by simp [sigma1]
@[simp] lemma sigma1_apply11 : sigma1 1 1 = (0 : ℂ) := by simp [sigma1]

@[simp] lemma sigma2_apply00 : sigma2 0 0 = (0 : ℂ) := by simp [sigma2]
@[simp] lemma sigma2_apply01 : sigma2 0 1 = (-Complex.I : ℂ) := by simp [sigma2]
@[simp] lemma sigma2_apply10 : sigma2 1 0 = (Complex.I : ℂ) := by simp [sigma2]
@[simp] lemma sigma2_apply11 : sigma2 1 1 = (0 : ℂ) := by simp [sigma2]

@[simp] lemma sigma3_apply00 : sigma3 0 0 = (1 : ℂ) := by simp [sigma3]
@[simp] lemma sigma3_apply01 : sigma3 0 1 = (0 : ℂ) := by simp [sigma3]
@[simp] lemma sigma3_apply10 : sigma3 1 0 = (0 : ℂ) := by simp [sigma3]
@[simp] lemma sigma3_apply11 : sigma3 1 1 = (-1 : ℂ) := by simp [sigma3]


-- Commutator/anticommutator notation.
notation:max "⟦" A ", " B "⟧" => A * B - B * A
notation:max "⦃" A ", " B "⦄" => A * B + B * A

@[simp] lemma sigma1_sq : sigma1 * sigma1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sigma1, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma sigma2_sq : sigma2 * sigma2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sigma2, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma sigma3_sq : sigma3 * sigma3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sigma3]

lemma sigma1_mul_sigma2 : sigma1 * sigma2 = Complex.I • sigma3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sigma1, sigma2, sigma3]

lemma sigma2_mul_sigma3 : sigma2 * sigma3 = Complex.I • sigma1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sigma1, sigma2, sigma3]

lemma sigma3_mul_sigma1 : sigma3 * sigma1 = Complex.I • sigma2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sigma1, sigma2, sigma3]


lemma sigma2_mul_sigma1 : sigma2 * sigma1 = -Complex.I • sigma3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sigma3, Matrix.mul_apply, Fin.sum_univ_two]


lemma sigma3_mul_sigma2 : sigma3 * sigma2 = -Complex.I • sigma1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sigma1, sigma2, sigma3]


lemma sigma1_mul_sigma3 : sigma1 * sigma3 = -Complex.I • sigma2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sigma1, sigma2, sigma3]


lemma comm_sigma1_sigma2 : ⟦sigma1, sigma2⟧ = (2 * Complex.I) • sigma3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sigma1, sigma2, sigma3] <;> ring


lemma comm_sigma2_sigma3 : ⟦sigma2, sigma3⟧ = (2 * Complex.I) • sigma1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sigma1, sigma2, sigma3] <;> ring


lemma comm_sigma3_sigma1 : ⟦sigma3, sigma1⟧ = (2 * Complex.I) • sigma2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sigma1, sigma2, I_mul_I, mul_assoc] <;> norm_num


lemma anticomm_sigma1_sigma2 : ⦃sigma1, sigma2⦄ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sigma1, sigma2]


lemma anticomm_sigma2_sigma3 : ⦃sigma2, sigma3⦄ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sigma2, sigma3]


lemma anticomm_sigma3_sigma1 : ⦃sigma3, sigma1⦄ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sigma1, sigma3]


lemma anticomm_sigma1_sigma1 : ⦃sigma1, sigma1⦄ = 2 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sigma1] <;> ring


lemma anticomm_sigma2_sigma2 : ⦃sigma2, sigma2⦄ = 2 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sigma2] <;> ring


lemma anticomm_sigma3_sigma3 : ⦃sigma3, sigma3⦄ = 2 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sigma3] <;> ring

lemma sigma1_mul_sigma2_mul_sigma3 : sigma1 * sigma2 * sigma3 = Complex.I • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [sigma1, sigma2, sigma3]

@[simp] lemma trace_sigma1 : Matrix.trace sigma1 = 0 := by
  simp [sigma1, Matrix.trace_fin_two_of]

@[simp] lemma trace_sigma2 : Matrix.trace sigma2 = 0 := by
  simp [sigma2, Matrix.trace_fin_two_of]

@[simp] lemma trace_sigma3 : Matrix.trace sigma3 = 0 := by
  simp [sigma3, Matrix.trace_fin_two_of]

@[simp] lemma trace_sigma1_mul_sigma1 : Matrix.trace (sigma1 * sigma1) = 2 := by
  simp [Matrix.trace_fin_two_of]
  norm_num

@[simp] lemma trace_sigma2_mul_sigma2 : Matrix.trace (sigma2 * sigma2) = 2 := by
  simp [Matrix.trace_fin_two_of]
  norm_num

@[simp] lemma trace_sigma3_mul_sigma3 : Matrix.trace (sigma3 * sigma3) = 2 := by
  simp [Matrix.trace_fin_two_of]
  norm_num


end Pauli

namespace Quantum

open scoped ComplexConjugate

/-- Pauli `X` as a linear map on `Qubit = EuclideanSpace ℂ (Fin 2)`.

This is the operator corresponding to `Pauli.sigma1` (bit-flip). -/
noncomputable abbrev pauliX : Qubit →ₗ[ℂ] Qubit :=
  { toFun := fun v =>
      EuclideanSpace.single (𝕜 := ℂ) (ι := Fin 2) 0 (v 1) +
      EuclideanSpace.single (𝕜 := ℂ) (ι := Fin 2) 1 (v 0)
    map_add' := by
      intro v w
      ext i
      fin_cases i <;> simp [EuclideanSpace.single_apply, add_comm]
    map_smul' := by
      intro a v
      ext i
      fin_cases i <;> simp [EuclideanSpace.single_apply, add_comm] }


@[simp] lemma pauliX_adjoint : pauliX.adjoint = pauliX := by
  classical
  let v : OrthonormalBasis (Fin 2) ℂ Qubit := EuclideanSpace.basisFun (Fin 2) ℂ
  have hX : LinearMap.toMatrix v.toBasis v.toBasis pauliX = Pauli.sigma1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, v, pauliX, Pauli.sigma1,
        EuclideanSpace.single_apply, add_comm]
  have hsigma1 : (Pauli.sigma1)ᴴ = Pauli.sigma1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Pauli.sigma1]
  apply (LinearMap.toMatrix v.toBasis v.toBasis).injective
  calc
    LinearMap.toMatrix v.toBasis v.toBasis pauliX.adjoint
        = (LinearMap.toMatrix v.toBasis v.toBasis pauliX)ᴴ := by
            simpa using (LinearMap.toMatrix_adjoint (v₁ := v) (v₂ := v) (f := pauliX))
    _ = (Pauli.sigma1)ᴴ := by simp [hX]
    _ = Pauli.sigma1 := by simp [hsigma1]
    _ = LinearMap.toMatrix v.toBasis v.toBasis pauliX := by simp [hX]

/-- Pauli `Z` as a linear map on `Qubit = EuclideanSpace ℂ (Fin 2)`.

This is the operator corresponding to `Pauli.sigma3` (phase-flip). -/
noncomputable abbrev pauliZ : Qubit →ₗ[ℂ] Qubit :=
  { toFun := fun v =>
      EuclideanSpace.single (𝕜 := ℂ) (ι := Fin 2) 0 (v 0) +
      EuclideanSpace.single (𝕜 := ℂ) (ι := Fin 2) 1 (-v 1)
    map_add' := by
      intro v w
      ext i
      fin_cases i <;> simp [EuclideanSpace.single_apply, add_comm]
    map_smul' := by
      intro a v
      ext i
      fin_cases i <;> simp [EuclideanSpace.single_apply, add_comm] }

@[simp] lemma pauliZ_adjoint : pauliZ.adjoint = pauliZ := by
  classical
  let v : OrthonormalBasis (Fin 2) ℂ Qubit := EuclideanSpace.basisFun (Fin 2) ℂ
  have hZ : LinearMap.toMatrix v.toBasis v.toBasis pauliZ = Pauli.sigma3 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, v, pauliZ, Pauli.sigma3,
        EuclideanSpace.single_apply, add_comm]
  have hsigma3 : (Pauli.sigma3)ᴴ = Pauli.sigma3 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Pauli.sigma3]
  apply (LinearMap.toMatrix v.toBasis v.toBasis).injective
  calc
    LinearMap.toMatrix v.toBasis v.toBasis pauliZ.adjoint
        = (LinearMap.toMatrix v.toBasis v.toBasis pauliZ)ᴴ := by
            simpa using (LinearMap.toMatrix_adjoint (v₁ := v) (v₂ := v) (f := pauliZ))
    _ = (Pauli.sigma3)ᴴ := by simp [hZ]
    _ = Pauli.sigma3 := by simp [hsigma3]
    _ = LinearMap.toMatrix v.toBasis v.toBasis pauliZ := by simp [hZ]


/- Pauli `H` as a linear map on `Qubit = EuclideanSpace ℂ (Fin 2)`.-/
noncomputable abbrev Hadamard : Qubit →ₗ[ℂ] Qubit :=
  (Real.sqrt 2 : ℂ)⁻¹ • (pauliZ + pauliX)

/-- The single-qubit operator `H'` (used in some CHSH conventions). -/
noncomputable abbrev Hadamard' : Qubit →ₗ[ℂ] Qubit :=
  (Real.sqrt 2 : ℂ)⁻¹ • (pauliZ - pauliX)


@[simp] lemma Hadamard_adjoint : Hadamard.adjoint = Hadamard := by
  classical
  -- Switch to the `star`-structure on endomorphisms (`star = adjoint`), then simplify.
  rw [(LinearMap.star_eq_adjoint (A := Hadamard)).symm]
  simp [Hadamard, LinearMap.star_eq_adjoint, add_comm]


noncomputable abbrev cosPi8 : ℂ := (Real.cos (Real.pi / 8) : ℂ)
noncomputable abbrev sinPi8 : ℂ := (Real.sin (Real.pi / 8) : ℂ)

/-!
`R := sin(π/8) X + cos(π/8) Z`.
-/
noncomputable def Rotation : Qubit →ₗ[ℂ] Qubit :=
  sinPi8 • pauliX + cosPi8 • pauliZ

@[simp] lemma Rotation_adjoint : Rotation = Rotation.adjoint := by
  calc
    Rotation = star Rotation := by
      simp [Rotation, sinPi8, cosPi8, LinearMap.star_eq_adjoint]
    _ = Rotation.adjoint := by
      simpa using (LinearMap.star_eq_adjoint (A := Rotation))


@[simp] lemma pauliX_ket0 : pauliX ket0 = ket1 := by
  ext i
  fin_cases i <;> simp [pauliX, ket0, ket1, EuclideanSpace.single_apply, add_comm]

@[simp] lemma pauliX_ket1 : pauliX ket1 = ket0 := by
  ext i
  fin_cases i <;> simp [pauliX, ket0, ket1, EuclideanSpace.single_apply, add_comm]

@[simp] lemma pauliZ_ket0 : pauliZ ket0 = ket0 := by
  ext i
  fin_cases i <;> simp [pauliZ, ket0, EuclideanSpace.single_apply, add_comm]

@[simp] lemma pauliZ_ket1 : pauliZ ket1 = -ket1 := by
  ext i
  fin_cases i <;> simp [pauliZ, ket1, EuclideanSpace.single_apply]

@[simp] lemma Hadamard_ket0 : Hadamard ket0 = (Real.sqrt 2 : ℂ)⁻¹ • (ket0 + ket1) := by
  ext i
  fin_cases i <;>
    simp [Hadamard, ket0, ket1, EuclideanSpace.single_apply, add_assoc, add_left_comm, add_comm]

@[simp] lemma Hadamard_ket1 : Hadamard ket1 = (Real.sqrt 2 : ℂ)⁻¹ • (ket0 - ket1) := by
  ext i
  fin_cases i <;>
    simp [Hadamard, ket0, ket1, EuclideanSpace.single_apply, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm]

private lemma sqrt2_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  have hR : (Real.sqrt 2 : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  exact_mod_cast hR

private lemma two_mul_inv_sqrt2_mul_inv_sqrt2 :
    (2 : ℂ) * (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 := by
  have hreal : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
    simp only [Nat.ofNat_nonneg, Real.mul_self_sqrt]
  have hcomplex : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = (2 : ℂ) := by
    exact_mod_cast hreal
  -- Clear denominators.
  field_simp [sqrt2_ne_zero]
  -- Goal is now `2 = (√2) * (√2)`.
  simpa [pow_two] using hcomplex.symm

private lemma sqrt2_div_two_eq_inv_sqrt2 :
    (Real.sqrt 2 : ℂ) / 2 = (Real.sqrt 2 : ℂ)⁻¹ := by
  have hreal : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
    simp only [Nat.ofNat_nonneg, Real.mul_self_sqrt]
  have hcomplex : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = (2 : ℂ) := by
    exact_mod_cast hreal
  field_simp [sqrt2_ne_zero]
  simpa [pow_two] using hcomplex

private lemma cos_pi_div_four_eq_inv_sqrt2 :
    Complex.cos ((Real.pi : ℂ) / 4) = (Real.sqrt 2 : ℂ)⁻¹ := by
  calc
    Complex.cos ((Real.pi : ℂ) / 4) = Complex.cos (Real.pi / 4 : ℂ) := by
      simp
    _ = (Real.cos (Real.pi / 4) : ℂ) := by
      simpa using (Complex.ofReal_cos (Real.pi / 4)).symm
    _ = (Real.sqrt 2 : ℂ) / 2 := by
      simp [Real.cos_pi_div_four]
    _ = (Real.sqrt 2 : ℂ)⁻¹ := by
      simp [sqrt2_div_two_eq_inv_sqrt2]

private lemma sin_pi_div_four_eq_inv_sqrt2 :
    Complex.sin ((Real.pi : ℂ) / 4) = (Real.sqrt 2 : ℂ)⁻¹ := by
  calc
    Complex.sin ((Real.pi : ℂ) / 4) = Complex.sin (Real.pi / 4 : ℂ) := by
      simp
    _ = (Real.sin (Real.pi / 4) : ℂ) := by
      simpa using (Complex.ofReal_sin (Real.pi / 4)).symm
    _ = (Real.sqrt 2 : ℂ) / 2 := by
      simp [Real.sin_pi_div_four]
    _ = (Real.sqrt 2 : ℂ)⁻¹ := by
      simp [sqrt2_div_two_eq_inv_sqrt2]

private lemma inv_sqrt2_mul_cos_add_sin_pi_div_eight :
    (Real.sqrt 2 : ℂ)⁻¹ *
        (Complex.cos ((Real.pi : ℂ) / 8) + Complex.sin ((Real.pi : ℂ) / 8)) =
      Complex.cos ((Real.pi : ℂ) / 8) := by
  have hsub : (Real.pi : ℂ) / 4 - (Real.pi : ℂ) / 8 = (Real.pi : ℂ) / 8 := by
    field_simp
    ring
  have hcos :
      Complex.cos ((Real.pi : ℂ) / 4) * Complex.cos ((Real.pi : ℂ) / 8) +
          Complex.sin ((Real.pi : ℂ) / 4) * Complex.sin ((Real.pi : ℂ) / 8) =
        Complex.cos ((Real.pi : ℂ) / 8) := by
    simpa [hsub] using
      (Complex.cos_sub (x := (Real.pi : ℂ) / 4) (y := (Real.pi : ℂ) / 8)).symm
  -- Replace `cos(π/4)` and `sin(π/4)` by `1/√2`, then factor.
  have hcos' :
      (Real.sqrt 2 : ℂ)⁻¹ * Complex.cos ((Real.pi : ℂ) / 8) +
          (Real.sqrt 2 : ℂ)⁻¹ * Complex.sin ((Real.pi : ℂ) / 8) =
        Complex.cos ((Real.pi : ℂ) / 8) := by
    simpa [cos_pi_div_four_eq_inv_sqrt2, sin_pi_div_four_eq_inv_sqrt2, mul_assoc] using hcos
  -- Rewrite `a * (b + c)` as `a*b + a*c`.
  simpa [mul_add] using hcos'

private lemma inv_sqrt2_mul_cos_sub_sin_pi_div_eight :
    (Real.sqrt 2 : ℂ)⁻¹ *
        (Complex.cos ((Real.pi : ℂ) / 8) - Complex.sin ((Real.pi : ℂ) / 8)) =
      Complex.sin ((Real.pi : ℂ) / 8) := by
  have hsub : (Real.pi : ℂ) / 4 - (Real.pi : ℂ) / 8 = (Real.pi : ℂ) / 8 := by
    field_simp
    ring
  have hsin :
      Complex.sin ((Real.pi : ℂ) / 4) * Complex.cos ((Real.pi : ℂ) / 8) -
          Complex.cos ((Real.pi : ℂ) / 4) * Complex.sin ((Real.pi : ℂ) / 8) =
        Complex.sin ((Real.pi : ℂ) / 8) := by
    simpa [hsub] using
      (Complex.sin_sub (x := (Real.pi : ℂ) / 4) (y := (Real.pi : ℂ) / 8)).symm
  have hsin' :
      (Real.sqrt 2 : ℂ)⁻¹ * Complex.cos ((Real.pi : ℂ) / 8) -
          (Real.sqrt 2 : ℂ)⁻¹ * Complex.sin ((Real.pi : ℂ) / 8) =
        Complex.sin ((Real.pi : ℂ) / 8) := by
    simpa [cos_pi_div_four_eq_inv_sqrt2, sin_pi_div_four_eq_inv_sqrt2, mul_assoc] using hsin
  simpa [mul_sub] using hsin'

private lemma inv_sqrt2_mul_cosPi8_add_sinPi8 :
    (Real.sqrt 2 : ℂ)⁻¹ * (cosPi8 + sinPi8) = cosPi8 := by
  have hpi8 : (Real.pi : ℂ) / 8 = (Real.pi / 8 : ℂ) := by simp
  have hcos : Complex.cos ((Real.pi : ℂ) / 8) = (Real.cos (Real.pi / 8) : ℂ) := by
    simpa [hpi8] using (Complex.ofReal_cos (Real.pi / 8)).symm
  have hsin : Complex.sin ((Real.pi : ℂ) / 8) = (Real.sin (Real.pi / 8) : ℂ) := by
    simpa [hpi8] using (Complex.ofReal_sin (Real.pi / 8)).symm
  have h := inv_sqrt2_mul_cos_add_sin_pi_div_eight
  -- Rewrite everything into `Real.sin/Real.cos` (cast to `ℂ`), then fold back to `cosPi8/sinPi8`.
  simpa only [cosPi8, sinPi8] using (by simpa [hcos, hsin] using h)

private lemma inv_sqrt2_mul_cosPi8_sub_sinPi8 :
    (Real.sqrt 2 : ℂ)⁻¹ * (cosPi8 - sinPi8) = sinPi8 := by
  have hpi8 : (Real.pi : ℂ) / 8 = (Real.pi / 8 : ℂ) := by simp
  have hcos : Complex.cos ((Real.pi : ℂ) / 8) = (Real.cos (Real.pi / 8) : ℂ) := by
    simpa [hpi8] using (Complex.ofReal_cos (Real.pi / 8)).symm
  have hsin : Complex.sin ((Real.pi : ℂ) / 8) = (Real.sin (Real.pi / 8) : ℂ) := by
    simpa [hpi8] using (Complex.ofReal_sin (Real.pi / 8)).symm
  have h := inv_sqrt2_mul_cos_sub_sin_pi_div_eight
  simpa only [cosPi8, sinPi8] using (by simpa [hcos, hsin] using h)


@[simp] lemma pauliZ_sq : pauliZ ∘ₗ pauliZ = LinearMap.id := by
  ext v i
  fin_cases i <;>
    simp [pauliZ, LinearMap.comp_apply, EuclideanSpace.single_apply, add_comm]

@[simp] lemma pauliX_sq : pauliX ∘ₗ pauliX = LinearMap.id := by
  ext v i
  fin_cases i <;>
    simp [pauliX, LinearMap.comp_apply, EuclideanSpace.single_apply, add_comm]

@[simp] lemma pauliZ_pauliX : pauliZ ∘ₗ pauliX = -pauliX ∘ₗ pauliZ := by
  ext v i
  fin_cases i <;>
    simp [pauliZ, pauliX, LinearMap.comp_apply, EuclideanSpace.single_apply, add_comm]

lemma pauliX_pauliZ : pauliX ∘ₗ pauliZ = -pauliZ ∘ₗ pauliX := by
  simp only [pauliZ_pauliX, neg_neg]

@[simp] lemma Rotation_sq : Rotation ∘ₗ Rotation = LinearMap.id := by
  classical
  have hsc : sinPi8 ^ 2 + cosPi8 ^ 2 = (1 : ℂ) := by
    -- Cast `Real.sin^2 + Real.cos^2 = 1` to `ℂ`.
    simpa [sinPi8, cosPi8, pow_two] using
      (congrArg (fun r : ℝ => (r : ℂ)) (Real.sin_sq_add_cos_sq (Real.pi / 8)))
  -- Expand `(sX + cZ)²`, cancel cross terms using `ZX = -XZ`, and use `s² + c² = 1`.
  calc
    Rotation ∘ₗ Rotation
        =
          (sinPi8 * sinPi8) • (pauliX ∘ₗ pauliX) +
            (sinPi8 * cosPi8) • (pauliX ∘ₗ pauliZ) +
              (cosPi8 * sinPi8) • (pauliZ ∘ₗ pauliX) +
                (cosPi8 * cosPi8) • (pauliZ ∘ₗ pauliZ) := by
          simp only [Rotation, LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_smul,
            LinearMap.smul_comp, smul_add, smul_smul]
          ac_rfl
    _ =
          (sinPi8 * sinPi8) • LinearMap.id +
            (sinPi8 * cosPi8) • (pauliX ∘ₗ pauliZ) +
              -((cosPi8 * sinPi8) • (pauliX ∘ₗ pauliZ)) +
                (cosPi8 * cosPi8) • LinearMap.id := by
          -- simplify squares and rewrite the cross term using `ZX = -XZ`
          simp [pauliX_sq, pauliZ_sq, pauliZ_pauliX]
    _ = (sinPi8 * sinPi8) • LinearMap.id + (cosPi8 * cosPi8) • LinearMap.id := by
          rw [mul_comm sinPi8 cosPi8]; abel
    _ = (sinPi8 ^ 2 + cosPi8 ^ 2) • LinearMap.id := by
          -- fold into a single scalar multiple of `id`
          simp [pow_two, add_smul]
    _ = LinearMap.id := by simp


@[simp] lemma Hadamard_sq : Hadamard ∘ₗ Hadamard = LinearMap.id := by
  classical
  have hs : (2 : ℂ) * (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = 1 := by
    simpa [mul_assoc] using two_mul_inv_sqrt2_mul_inv_sqrt2
  have hinv2 : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 * (2 : ℂ) = 1 := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hs
  have hinv2' : ((Real.sqrt 2 : ℂ) ^ 2)⁻¹ * (2 : ℂ) = 1 := by
    simpa [inv_pow] using hinv2
  ext v i
  fin_cases i
  · -- i = 0
    simp [Hadamard, LinearMap.comp_apply, EuclideanSpace.single_apply, add_comm]
    ring_nf
    simp only [inv_pow, Fin.isValue]
    calc
      ((Real.sqrt 2 : ℂ) ^ 2)⁻¹ * v.ofLp 0 * 2
          = (((Real.sqrt 2 : ℂ) ^ 2)⁻¹ * (2 : ℂ)) * v.ofLp 0 := by
              simp [mul_assoc, mul_comm]
      _ = v.ofLp 0 := by simp [hinv2']
  · -- i = 1
    simp [Hadamard, LinearMap.comp_apply, EuclideanSpace.single_apply, add_comm]
    ring_nf
    simp only [inv_pow, Fin.isValue]
    calc
      ((Real.sqrt 2 : ℂ) ^ 2)⁻¹ * v.ofLp 1 * 2
          = (((Real.sqrt 2 : ℂ) ^ 2)⁻¹ * (2 : ℂ)) * v.ofLp 1 := by
              simp [mul_assoc, mul_comm]
      _ = v.ofLp 1 := by simp [hinv2']


-- This proof uses broad `simp` normalization inside a hand-structured trig/ring derivation.
-- Restricting to `simp only` here is brittle; scope-disable flexible-lint for this declaration.
set_option linter.flexible false in
@[simp] lemma Rotation_pauliZ : Rotation ∘ₗ pauliZ = Hadamard ∘ₗ Rotation := by
  classical
  let t : ℂ := (Real.pi : ℂ) / 8
  have hcos : (Real.sqrt 2 : ℂ)⁻¹ * (Complex.cos t + Complex.sin t) = Complex.cos t := by
    simpa [t] using inv_sqrt2_mul_cos_add_sin_pi_div_eight
  have hsin : (Real.sqrt 2 : ℂ)⁻¹ * (Complex.cos t - Complex.sin t) = Complex.sin t := by
    simpa [t] using inv_sqrt2_mul_cos_sub_sin_pi_div_eight
  ext v i
  fin_cases i
  · -- i = 0
    simp [Rotation, Hadamard, pauliX, pauliZ, LinearMap.comp_apply, EuclideanSpace.single_apply]
    have hrhs :
        (Real.sqrt 2 : ℂ)⁻¹ * (sin t * v.ofLp 1 + cos t * v.ofLp 0) +
            (Real.sqrt 2 : ℂ)⁻¹ * (sin t * v.ofLp 0 + -(cos t * v.ofLp 1)) =
          (Real.sqrt 2 : ℂ)⁻¹ * ((cos t + sin t) * v.ofLp 0 + (sin t - cos t) * v.ofLp 1) := by
      ring_nf
    rw [hrhs]
    have hR :
        (Real.sqrt 2 : ℂ)⁻¹ * ((cos t + sin t) * v.ofLp 0 + (sin t - cos t) * v.ofLp 1) =
          cos t * v.ofLp 0 + (-sin t) * v.ofLp 1 := by
      linear_combination v.ofLp 0 * hcos - v.ofLp 1 * hsin
    rw [hR]
    ring
  · -- i = 1
    simp [Rotation, Hadamard, pauliX, pauliZ, LinearMap.comp_apply, EuclideanSpace.single_apply]
    have hrhs :
        (Real.sqrt 2 : ℂ)⁻¹ * (cos t * v.ofLp 1 + -(sin t * v.ofLp 0)) +
            (Real.sqrt 2 : ℂ)⁻¹ * (sin t * v.ofLp 1 + cos t * v.ofLp 0) =
          (Real.sqrt 2 : ℂ)⁻¹ * ((cos t - sin t) * v.ofLp 0 + (cos t + sin t) * v.ofLp 1) := by
      ring_nf
    rw [hrhs]
    have hR :
        (Real.sqrt 2 : ℂ)⁻¹ * ((cos t - sin t) * v.ofLp 0 + (cos t + sin t) * v.ofLp 1) =
          sin t * v.ofLp 0 + cos t * v.ofLp 1 := by
      linear_combination v.ofLp 0 * hsin + v.ofLp 1 * hcos
    simp [t, hR]

-- Same rationale as `Rotation_pauliZ`.
set_option linter.flexible false in
@[simp] lemma Rotation_pauliX : Rotation ∘ₗ pauliX = Hadamard' ∘ₗ Rotation := by
  classical
  let t : ℂ := (Real.pi : ℂ) / 8
  have hcos : (Real.sqrt 2 : ℂ)⁻¹ * (Complex.cos t + Complex.sin t) = Complex.cos t := by
    simpa [t] using inv_sqrt2_mul_cos_add_sin_pi_div_eight
  have hsin : (Real.sqrt 2 : ℂ)⁻¹ * (Complex.cos t - Complex.sin t) = Complex.sin t := by
    simpa [t] using inv_sqrt2_mul_cos_sub_sin_pi_div_eight
  ext v i
  fin_cases i
  · -- i = 0
    simp [Rotation, Hadamard', pauliX, pauliZ, LinearMap.comp_apply, EuclideanSpace.single_apply]
    have hrhs :
        (Real.sqrt 2 : ℂ)⁻¹ *
            (sin t * v.ofLp 1 + cos t * v.ofLp 0 -
              (sin t * v.ofLp 0 + -(cos t * v.ofLp 1))) =
          (Real.sqrt 2 : ℂ)⁻¹ * ((cos t - sin t) * v.ofLp 0 + (cos t + sin t) * v.ofLp 1) := by
      ring_nf
    rw [hrhs]
    have hR :
        (Real.sqrt 2 : ℂ)⁻¹ * ((cos t - sin t) * v.ofLp 0 + (cos t + sin t) * v.ofLp 1) =
          sin t * v.ofLp 0 + cos t * v.ofLp 1 := by
      linear_combination v.ofLp 0 * hsin + v.ofLp 1 * hcos
    simp [t, hR]
  · -- i = 1
    simp [Rotation, Hadamard', pauliX, pauliZ, LinearMap.comp_apply, EuclideanSpace.single_apply]
    have hrhs :
        (Real.sqrt 2 : ℂ)⁻¹ *
            (cos t * v.ofLp 1 + -(sin t * v.ofLp 0) -
              (sin t * v.ofLp 1 + cos t * v.ofLp 0)) =
          (Real.sqrt 2 : ℂ)⁻¹ * ((-sin t + -cos t) * v.ofLp 0 + (cos t - sin t) * v.ofLp 1) := by
      ring_nf
    rw [hrhs]
    have hcos_neg : (Real.sqrt 2 : ℂ)⁻¹ * (-sin t + -cos t) = -cos t := by
      linear_combination -hcos
    have hR :
        (Real.sqrt 2 : ℂ)⁻¹ * ((-sin t + -cos t) * v.ofLp 0 + (cos t - sin t) * v.ofLp 1) =
          sin t * v.ofLp 1 + -(cos t * v.ofLp 0) := by
      linear_combination v.ofLp 1 * hsin + v.ofLp 0 * hcos_neg
    simp [t, hR]

/-!
`pauliZHZ` is the operator `Z H Z`. With our definition `H = (Z + X)/√2`,
this simplifies to `(Z - X)/√2`, i.e. `Hadamard'`.
-/

/-- The single-qubit operator `Z H Z`. -/
noncomputable abbrev pauliZHZ : Qubit →ₗ[ℂ] Qubit :=
  Hadamard'

end Quantum
