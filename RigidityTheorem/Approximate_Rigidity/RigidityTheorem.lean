import Approximate_Rigidity.SpectralArgument
import Approximate_Rigidity.Isometries
import Approximate_Rigidity.chsh_link
import Approximate_Rigidity.StateExtraction

open scoped TensorProduct InnerProductSpace
open Quantum

namespace Approximate_Rigidity

/-!
Main rigidity theorem statements (Theorem 11.1).

All theorems in this file are currently stated with placeholder proofs and are
meant to be filled in after the supporting library is completed.
-/

/-!
Auxiliary placeholders used in the theorem statements.

These are defined here (rather than in `BasicDefs.lean`) so that the statement
file compiles while the library is under construction.
-/

section LocalActions
variable {H_A H_B : Type*}
variable [AddCommMonoid H_A] [AddCommMonoid H_B]
variable [Module ℂ H_A] [Module ℂ H_B]

noncomputable def applyAlice (A : H_A →ₗ[ℂ] H_A) :
    (H_A ⊗[ℂ] H_B) →ₗ[ℂ] (H_A ⊗[ℂ] H_B) :=
  A ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)

noncomputable def applyBob (B : H_B →ₗ[ℂ] H_B) :
    (H_A ⊗[ℂ] H_B) →ₗ[ℂ] (H_A ⊗[ℂ] H_B) :=
  (LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ B
end LocalActions


section MainTheorems
open Approximate_Rigidity

variable {H_A H_B : Type*}
variable [NormedAddCommGroup H_A] [NormedAddCommGroup H_B]
variable [InnerProductSpace ℂ H_A] [InnerProductSpace ℂ H_B]
variable [FiniteDimensional ℂ H_A] [FiniteDimensional ℂ H_B]
variable (A0 : H_A →ₗ[ℂ] H_A) (A1 : H_A →ₗ[ℂ] H_A) (B0 : H_B →ₗ[ℂ] H_B) (B1 : H_B →ₗ[ℂ] H_B)
variable (S : CHSHStrategy H_A H_B)
variable (ε : Real)

private lemma K_expectation_upper_bound
    (Ψ : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B))
    (hΨ : ‖Ψ‖ = 1) :
    (⟪Ψ, ((K ⊗ₗ (LinearMap.id : (H_A ⊗[ℂ] H_B) →ₗ[ℂ] (H_A ⊗[ℂ] H_B))) Ψ)⟫_ℂ).re
      ≤ 2 * Real.sqrt 2 := by
  classical
  let η : Fin 4 → (H_A ⊗[ℂ] H_B) := bellDecomposition (J := (H_A ⊗[ℂ] H_B)) Ψ
  have hsum : (∑ i : Fin 4, ‖η i‖ ^ 2) = 1 := by
    simpa [η] using (decomposition_probs_sum_eq_one (J := (H_A ⊗[ℂ] H_B)) (Ψ := Ψ) hΨ)
  have hη0_le : ‖η 0‖ ^ 2 ≤ 1 := by
    have h0 : ‖η 0‖ ^ 2 ≤ ∑ i : Fin 4, ‖η i‖ ^ 2 := by
      simpa using
        (Finset.single_le_sum (s := (Finset.univ : Finset (Fin 4)))
          (f := fun i : Fin 4 => ‖η i‖ ^ 2) (a := (0 : Fin 4))
          (by intro i hi; positivity) (by simp))
    exact le_trans h0 (le_of_eq hsum)
  have hdiff_le : (‖η 0‖ ^ 2 - ‖η 3‖ ^ 2) ≤ 1 :=
    (sub_le_self _ (by positivity : 0 ≤ ‖η 3‖ ^ 2)).trans hη0_le
  have hre :
      (⟪Ψ, ((K ⊗ₗ (LinearMap.id :
            (H_A ⊗[ℂ] H_B) →ₗ[ℂ] (H_A ⊗[ℂ] H_B))) Ψ)⟫_ℂ).re
        = 2 * Real.sqrt 2 * (‖η 0‖ ^ 2 - ‖η 3‖ ^ 2) := by
    have hpow : ∀ r : ℝ, ((r : ℂ) ^ 2).re = r ^ 2 := by
      intro r
      simpa using (RCLike.re_ofReal_pow (K := ℂ) (a := r) (n := 2))
    simpa [η, hpow] using
      congrArg Complex.re
        (inner_K_tensor_id_eq_bellDecomposition (H_A := H_A) (H_B := H_B) (Ψ := Ψ))
  have hpos : 0 ≤ (2 * Real.sqrt 2 : Real) := by
    nlinarith [Real.sqrt_nonneg (2 : Real)]
  have hmul : 2 * Real.sqrt 2 * (‖η 0‖ ^ 2 - ‖η 3‖ ^ 2) ≤ 2 * Real.sqrt 2 := by
    simpa [mul_one] using (mul_le_mul_of_nonneg_left hdiff_le hpos)
  simpa [hre] using hmul

private lemma regSwap_qubit_naturality
    (fA fB : Qubit →ₗ[ℂ] Qubit) :
    (((fA ⊗ₗ fB) ⊗ₗ
        (LinearMap.id : (H_A ⊗[ℂ] H_B) →ₗ[ℂ] (H_A ⊗[ℂ] H_B))) ∘ₗ
      regSwap (H_A := H_A) (H_B := H_B))
      =
    (regSwap (H_A := H_A) (H_B := H_B) ∘ₗ
      (((fA ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
          (fB ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))) :
        ((Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B)) →ₗ[ℂ]
          ((Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B)))) := by
  classical
  ext q a q' b
  simp [regSwap]


theorem state_extraction
    (hε : 0 ≤ ε) (hBias : chshBias S ≥ 2 * Real.sqrt 2 - ε) :
    ∃ V_A : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A),
      ∃ V_B : H_B →ₗ[ℂ] (Qubit ⊗[ℂ] H_B),
      ∃ junk : H_A ⊗[ℂ] H_B,
        Isometry V_A ∧
          Isometry V_B ∧
            ‖(regSwap ((V_A ⊗ₗ V_B) S.psi) - bellState ⊗ₜ[ℂ] junk)‖
              ≤ Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
  let V_A : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) := VA (H := H_A) S.A0 S.A1
  let V_B : H_B →ₗ[ℂ] (Qubit ⊗[ℂ] H_B) := VB (H := H_B) S.B0 S.B1
  let Ψ : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B) := regSwap ((V_A ⊗ₗ V_B) S.psi)
  -- From the CHSH bias assumption, the extracted state `Ψ` has large overlap with the
  -- max-eigenvector of the 2-qubit CHSH operator `K` (see `theorem11_1_proof_modified.md`).
  have hVA : Isometry V_A := by
      simpa [V_A] using (VA_is_isometry S.A0 S.A1)
  have hVB : Isometry V_B := by
      simpa [V_B] using (VB_is_isometry S.B0 S.B1)
  have hExp :
      Complex.re
          (⟪Ψ,((K ⊗ₗ (LinearMap.id : (H_A ⊗[ℂ] H_B) →ₗ[ℂ] (H_A ⊗[ℂ] H_B))) Ψ)⟫_ℂ)
        ≥ 2 * Real.sqrt 2 - delta ε := by
    simpa [V_A, V_B, Ψ] using (chsh_to_K_expectation (S := S) (ε := ε) hBias)
  have hΨ : ‖Ψ‖ = 1 := by
    simpa [Ψ] using
      (regSwap_map_norm_eq_one (H_A := H_A) (H_B := H_B)
        (V_A := V_A) (V_B := V_B) hVA hVB (ψ := S.psi) S.psi_norm)
  have hδ : 0 ≤ delta ε := by
    -- `delta ε ≥ 0` follows from `ε ≥ 0` (implied by the CHSH bound).
    exact delta_nonneg (epsilon := ε) hε
  have hjunk :
      ‖Ψ - bellState ⊗ₜ[ℂ] junkState (H_A := H_A) (H_B := H_B) (Ψ := Ψ)‖
        ≤ Real.sqrt (2 * Real.sqrt 2 * delta ε) :=
    state_extraction_bound (H_A := H_A) (H_B := H_B) (Ψ := Ψ) (delta := delta ε) hΨ hδ hExp
  exact ⟨V_A, V_B, junkState (H_A := H_A) (H_B := H_B) (Ψ := Ψ),
          hVA,
          hVB,
          hjunk⟩



set_option maxHeartbeats 1200000 in
theorem Alice_operator_extraction
    (hε : 0 ≤ ε) (hBias : chshBias S ≥ 2 * Real.sqrt 2 - ε) :
    ∃ V_A : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A),
      ∃ V_B : H_B →ₗ[ℂ] (Qubit ⊗[ℂ] H_B),
      ∃ junk : H_A ⊗[ℂ] H_B,
        Isometry V_A ∧
          Isometry V_B ∧
            ‖(regSwap ((V_A ⊗ₗ V_B) ((applyAlice S.A0) S.psi))
              - ((pauliZ ⊗ₗ LinearMap.id) bellState) ⊗ₜ[ℂ] junk)‖
              ≤ Real.sqrt (2 * Real.sqrt 2 * delta ε) ∧
            ‖(regSwap ((V_A ⊗ₗ V_B) ((applyAlice S.A1) S.psi))
              - ((pauliX ⊗ₗ LinearMap.id) bellState) ⊗ₜ[ℂ] junk)‖
              ≤ Real.sqrt (cConst * ε) + Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
    classical
    let V_A : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) := VA (H := H_A) S.A0 S.A1
    let V_B : H_B →ₗ[ℂ] (Qubit ⊗[ℂ] H_B) := VB (H := H_B) S.B0 S.B1
    let idJ : (H_A ⊗[ℂ] H_B) →ₗ[ℂ] (H_A ⊗[ℂ] H_B) := LinearMap.id
    let KJ := (K ⊗ₗ idJ)
    have hVA : Isometry V_A := by simpa [V_A] using (VA_is_isometry S.A0 S.A1)
    have hVB : Isometry V_B := by simpa [V_B] using (VB_is_isometry S.B0 S.B1)
    let Ψ := regSwap ((V_A ⊗ₗ V_B) S.psi)
    have hΨ : ‖Ψ‖ = 1 := by
      simpa [Ψ] using (regSwap_map_norm_eq_one (H_A := H_A) (H_B := H_B) (V_A := V_A) (V_B := V_B) hVA hVB (ψ := S.psi) S.psi_norm)
    have hExp : (⟪Ψ, KJ Ψ⟫_ℂ).re ≥ 2 * Real.sqrt 2 - delta ε := by
      simpa [KJ, idJ, V_A, V_B, Ψ] using (chsh_to_K_expectation (S := S) (ε := ε) hBias)
    have hExp_le : (⟪Ψ, KJ Ψ⟫_ℂ).re ≤ 2 * Real.sqrt 2 := by
      simpa [KJ, idJ] using
        (K_expectation_upper_bound (H_A := H_A) (H_B := H_B) (Ψ := Ψ) hΨ)
    have hδ : 0 ≤ delta ε := by linarith [hExp, hExp_le]
    have hjunk := state_extraction_bound (H_A := H_A) (H_B := H_B) (Ψ := Ψ) (delta := delta ε) hΨ hδ hExp
    let junk : H_A ⊗[ℂ] H_B := junkState (H_A := H_A) (H_B := H_B) (Ψ := Ψ)

    let Zᵢ : Qubit →ₗᵢ[ℂ] Qubit :=
      { toLinearMap := (pauliZ : Qubit →ₗ[ℂ] Qubit)
        norm_map' := (AddMonoidHomClass.isometry_iff_norm (pauliZ : Qubit →ₗ[ℂ] Qubit)).1 PauliZ_is_isometry }
    let Xᵢ : Qubit →ₗᵢ[ℂ] Qubit :=
      { toLinearMap := (pauliX : Qubit →ₗ[ℂ] Qubit)
        norm_map' := (AddMonoidHomClass.isometry_iff_norm (pauliX : Qubit →ₗ[ℂ] Qubit)).1 PauliX_is_isometry }
    let idQᵢ : Qubit →ₗᵢ[ℂ] Qubit := LinearIsometry.id
    let idJᵢ : (H_A ⊗[ℂ] H_B) →ₗᵢ[ℂ] (H_A ⊗[ℂ] H_B) := LinearIsometry.id
    let PZ2ᵢ : (Qubit ⊗[ℂ] Qubit) →ₗᵢ[ℂ] (Qubit ⊗[ℂ] Qubit) := TensorProduct.mapIsometry Zᵢ idQᵢ
    let PX2ᵢ : (Qubit ⊗[ℂ] Qubit) →ₗᵢ[ℂ] (Qubit ⊗[ℂ] Qubit) := TensorProduct.mapIsometry Xᵢ idQᵢ
    let PZᵢ := TensorProduct.mapIsometry PZ2ᵢ idJᵢ
    let PXᵢ := TensorProduct.mapIsometry PX2ᵢ idJᵢ
    let PZ := PZᵢ.toLinearMap
    let PX := PXᵢ.toLinearMap
    have hA0_vec : regSwap ((V_A ⊗ₗ V_B) ((applyAlice S.A0) S.psi)) = PZ Ψ := by
      have hpre :
          (V_A ⊗ₗ V_B) ((applyAlice S.A0) S.psi) =
            (((pauliZ ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
                  (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))) ((V_A ⊗ₗ V_B) S.psi)) := by
        simpa [V_A, V_B, applyAlice, LinearMap.comp_apply] using congrArg (fun f => f S.psi) (a0_extraction_intertwining (S := S))
      have hnat :=
        congrArg (fun f => f ((V_A ⊗ₗ V_B) S.psi))
          (regSwap_qubit_naturality (H_A := H_A) (H_B := H_B)
            (fA := pauliZ) (fB := (LinearMap.id : Qubit →ₗ[ℂ] Qubit)))
      have hnat' :
          regSwap (H_A := H_A) (H_B := H_B)
              (((pauliZ ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
                    (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B)))
                ((V_A ⊗ₗ V_B) S.psi)) = PZ Ψ := by
        simpa [PZ, Ψ, LinearMap.comp_apply] using hnat.symm
      simpa [hpre] using hnat'
    have hA0_bound : ‖regSwap ((V_A ⊗ₗ V_B) ((applyAlice S.A0) S.psi)) - ((pauliZ ⊗ₗ LinearMap.id) bellState) ⊗ₜ[ℂ] junk‖ ≤
        Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
      have hEq : ‖PZ (Ψ - bellState ⊗ₜ[ℂ] junk)‖ = ‖Ψ - bellState ⊗ₜ[ℂ] junk‖ := by
        simpa [PZ] using (PZᵢ.norm_map (Ψ - bellState ⊗ₜ[ℂ] junk))
      have h0 : ‖PZ (Ψ - bellState ⊗ₜ[ℂ] junk)‖ ≤ Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
        have hbase :
            ‖Ψ - bellState ⊗ₜ[ℂ] junk‖ ≤ Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
          simpa [junk] using hjunk
        simpa only [hEq] using hbase
      have h1 :
          ‖PZ Ψ - PZ (bellState ⊗ₜ[ℂ] junk)‖ ≤ Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
        simpa [LinearMap.map_sub] using h0
      simpa [hA0_vec, junk, PZ, TensorProduct.map_tmul, LinearMap.id_apply] using h1

    have hA1_pre := (a1_extraction_approx (S := S) (epsilon := ε) hBias)
    have hA1_post : ‖regSwap ((V_A ⊗ₗ V_B) ((applyAlice S.A1) S.psi)) - PX Ψ‖ ≤ Real.sqrt (cConst * ε) := by
      let u := (((V_A ⊗ₗ V_B) ∘ₗ (S.A1 ⊗ₗ LinearMap.id)) S.psi)
      let v := ((((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
            (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))) ∘ₗ (V_A ⊗ₗ V_B)) S.psi)
      have huv : ‖u - v‖ ≤ Real.sqrt (cConst * ε) := by
        simpa [u, v, V_A, V_B, S.psi_norm, mul_one, sub_eq_add_neg] using hA1_pre
      have huv' : ‖regSwap (H_A := H_A) (H_B := H_B) (u - v)‖ ≤ Real.sqrt (cConst * ε) := by
        simpa only [regSwap_norm (ψ := (u - v))] using huv
      have huv'' : ‖regSwap (H_A := H_A) (H_B := H_B) u - regSwap (H_A := H_A) (H_B := H_B) v‖ ≤ Real.sqrt (cConst * ε) := by
        simpa [LinearMap.map_sub] using huv'
      have hnat := congrArg (fun f => f ((V_A ⊗ₗ V_B) S.psi))
        (regSwap_qubit_naturality (H_A := H_A) (H_B := H_B)
          (fA := pauliX) (fB := (LinearMap.id : Qubit →ₗ[ℂ] Qubit)))
      have hrew : regSwap (H_A := H_A) (H_B := H_B) v = PX Ψ := by
        simpa [PX, Ψ, v, LinearMap.comp_apply] using hnat.symm
      simpa [u, applyAlice, LinearMap.comp_apply, hrew] using huv''

    have hPX_bound :
        ‖(PX Ψ - ((pauliX ⊗ₗ LinearMap.id) bellState) ⊗ₜ[ℂ] junk)‖
          ≤ Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
      have hEq : ‖PX (Ψ - bellState ⊗ₜ[ℂ] junk)‖ = ‖Ψ - bellState ⊗ₜ[ℂ] junk‖ := by
        simpa [PX] using (PXᵢ.norm_map (Ψ - bellState ⊗ₜ[ℂ] junk))
      have h0 : ‖PX (Ψ - bellState ⊗ₜ[ℂ] junk)‖ ≤ Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
        have hbase :
            ‖Ψ - bellState ⊗ₜ[ℂ] junk‖ ≤ Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
          simpa [junk] using hjunk
        simpa only [hEq] using hbase
      have h1 :
          ‖PX Ψ - PX (bellState ⊗ₜ[ℂ] junk)‖ ≤ Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
        simpa [LinearMap.map_sub] using h0
      simpa [PX, junk, TensorProduct.map_tmul, LinearMap.id_apply] using h1

    have hA1_bound :
        ‖(regSwap ((V_A ⊗ₗ V_B) ((applyAlice S.A1) S.psi))
            - ((pauliX ⊗ₗ LinearMap.id) bellState) ⊗ₜ[ℂ] junk)‖
          ≤ Real.sqrt (cConst * ε) + Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
      set a :=
        regSwap ((V_A ⊗ₗ V_B) ((applyAlice S.A1) S.psi)) with ha
      set b := PX Ψ with hb
      set c := ((pauliX ⊗ₗ LinearMap.id) bellState) ⊗ₜ[ℂ] junk with hc
      have htri : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
        have habc : a - c = (a - b) + (b - c) := by abel
        have hnorm : ‖a - c‖ = ‖(a - b) + (b - c)‖ := by
          simp only [sub_add_sub_cancel]
        simpa [hnorm] using (norm_add_le (a - b) (b - c))
      have hsum :
          ‖a - b‖ + ‖b - c‖ ≤
            Real.sqrt (cConst * ε) + Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
        have := add_le_add hA1_post hPX_bound
        simpa [ha, hb, hc] using this
      exact le_trans (by simpa [ha, hb, hc] using htri) hsum
    exact ⟨V_A, V_B, junk, hVA, hVB, hA0_bound, hA1_bound⟩


set_option maxHeartbeats 1200000 in
theorem Bob_operator_extraction
    (hBias : chshBias S ≥ 2 * Real.sqrt 2 - ε) :
    ∃ V_A : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A),
      ∃ V_B : H_B →ₗ[ℂ] (Qubit ⊗[ℂ] H_B),
      ∃ junk : H_A ⊗[ℂ] H_B,
        Isometry V_A ∧
          Isometry V_B ∧
            ‖(regSwap ((V_A ⊗ₗ V_B) ((applyBob S.B0) S.psi))
              - ((LinearMap.id ⊗ₗ Hadamard) bellState) ⊗ₜ[ℂ] junk)‖
              ≤ Real.sqrt (2 * Real.sqrt 2 * delta ε) ∧
            ‖(regSwap ((V_A ⊗ₗ V_B) ((applyBob S.B1) S.psi))
              - ((LinearMap.id ⊗ₗ pauliZHZ) bellState) ⊗ₜ[ℂ] junk)‖
              ≤ Real.sqrt (cConst * ε) + Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
  classical
  let V_A : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) := VA (H := H_A) S.A0 S.A1
  let V_B : H_B →ₗ[ℂ] (Qubit ⊗[ℂ] H_B) := VB (H := H_B) S.B0 S.B1
  let idJ : (H_A ⊗[ℂ] H_B) →ₗ[ℂ] (H_A ⊗[ℂ] H_B) := LinearMap.id
  let KJ := (K ⊗ₗ idJ)
  have hVA : Isometry V_A := by simpa [V_A] using (VA_is_isometry S.A0 S.A1)
  have hVB : Isometry V_B := by simpa [V_B] using (VB_is_isometry S.B0 S.B1)
  let Ψ := regSwap ((V_A ⊗ₗ V_B) S.psi)
  have hΨ : ‖Ψ‖ = 1 := by
    simpa [Ψ] using
      (regSwap_map_norm_eq_one (H_A := H_A) (H_B := H_B)
        (V_A := V_A) (V_B := V_B) hVA hVB (ψ := S.psi) S.psi_norm)
  have hExp : (⟪Ψ, KJ Ψ⟫_ℂ).re ≥ 2 * Real.sqrt 2 - delta ε := by
    simpa [KJ, idJ, V_A, V_B, Ψ] using (chsh_to_K_expectation (S := S) (ε := ε) hBias)
  have hExp_le : (⟪Ψ, KJ Ψ⟫_ℂ).re ≤ 2 * Real.sqrt 2 := by
    simpa [KJ, idJ] using
      (K_expectation_upper_bound (H_A := H_A) (H_B := H_B) (Ψ := Ψ) hΨ)
  have hδ : 0 ≤ delta ε := by linarith [hExp, hExp_le]
  have hjunk := state_extraction_bound (H_A := H_A) (H_B := H_B) (Ψ := Ψ) (delta := delta ε) hΨ hδ hExp
  let junk : H_A ⊗[ℂ] H_B := junkState (H_A := H_A) (H_B := H_B) (Ψ := Ψ)

  have hRotIso : Isometry (Rotation : Qubit →ₗ[ℂ] Qubit) := by
    exact
      (isometry_of_adjoint_eq_self_and_sq_one
        (H := Qubit)
        (A := (Rotation : Qubit →ₗ[ℂ] Qubit))
        (hAdj := (Rotation_adjoint : Rotation = Rotation.adjoint).symm)
        (hSq := Rotation_sq))
  have hRotNorm : ∀ z : Qubit, ‖Rotation z‖ = ‖z‖ :=
    (AddMonoidHomClass.isometry_iff_norm (Rotation : Qubit →ₗ[ℂ] Qubit)).1 hRotIso
  have hZNorm : ∀ z : Qubit, ‖pauliZ z‖ = ‖z‖ :=
    (AddMonoidHomClass.isometry_iff_norm (pauliZ : Qubit →ₗ[ℂ] Qubit)).1 PauliZ_is_isometry
  have hXNorm : ∀ z : Qubit, ‖pauliX z‖ = ‖z‖ :=
    (AddMonoidHomClass.isometry_iff_norm (pauliX : Qubit →ₗ[ℂ] Qubit)).1 PauliX_is_isometry

  have hHad_comp : (Hadamard : Qubit →ₗ[ℂ] Qubit) = Rotation ∘ₗ pauliZ ∘ₗ Rotation := by
    calc
      Hadamard = Hadamard ∘ₗ (Rotation ∘ₗ Rotation) := by
        rw [Rotation_sq, LinearMap.comp_id]
      _ = (Hadamard ∘ₗ Rotation) ∘ₗ Rotation := by
        rw [LinearMap.comp_assoc]
      _ = (Rotation ∘ₗ pauliZ) ∘ₗ Rotation := by
        rw [← Rotation_pauliZ]
      _ = Rotation ∘ₗ pauliZ ∘ₗ Rotation := by
        rw [LinearMap.comp_assoc]

  have hZHZ_comp : (pauliZHZ : Qubit →ₗ[ℂ] Qubit) = Rotation ∘ₗ pauliX ∘ₗ Rotation := by
    calc
      pauliZHZ = Hadamard' := by simp [pauliZHZ]
      _ = Hadamard' ∘ₗ (Rotation ∘ₗ Rotation) := by
            rw [Rotation_sq, LinearMap.comp_id]
      _ = (Hadamard' ∘ₗ Rotation) ∘ₗ Rotation := by
            rw [LinearMap.comp_assoc]
      _ = (Rotation ∘ₗ pauliX) ∘ₗ Rotation := by
            rw [← Rotation_pauliX]
      _ = Rotation ∘ₗ pauliX ∘ₗ Rotation := by
            rw [LinearMap.comp_assoc]

  have hHadIso : Isometry (Hadamard : Qubit →ₗ[ℂ] Qubit) := by
    refine (AddMonoidHomClass.isometry_iff_norm (Hadamard : Qubit →ₗ[ℂ] Qubit)).2 ?_
    intro z
    rw [hHad_comp]
    change ‖Rotation (pauliZ (Rotation z))‖ = ‖z‖
    calc
      ‖Rotation (pauliZ (Rotation z))‖ = ‖pauliZ (Rotation z)‖ := by
        exact hRotNorm (pauliZ (Rotation z))
      _ = ‖Rotation z‖ := by
        exact hZNorm (Rotation z)
      _ = ‖z‖ := by
        exact hRotNorm z

  have hZHZIso : Isometry (pauliZHZ : Qubit →ₗ[ℂ] Qubit) := by
    refine (AddMonoidHomClass.isometry_iff_norm (pauliZHZ : Qubit →ₗ[ℂ] Qubit)).2 ?_
    intro z
    rw [hZHZ_comp]
    change ‖Rotation (pauliX (Rotation z))‖ = ‖z‖
    calc
      ‖Rotation (pauliX (Rotation z))‖ = ‖pauliX (Rotation z)‖ := by
        exact hRotNorm (pauliX (Rotation z))
      _ = ‖Rotation z‖ := by
        exact hXNorm (Rotation z)
      _ = ‖z‖ := by
        exact hRotNorm z

  let Hᵢ : Qubit →ₗᵢ[ℂ] Qubit :=
    { toLinearMap := (Hadamard : Qubit →ₗ[ℂ] Qubit)
      norm_map' := (AddMonoidHomClass.isometry_iff_norm (Hadamard : Qubit →ₗ[ℂ] Qubit)).1 hHadIso }
  let ZHZᵢ : Qubit →ₗᵢ[ℂ] Qubit :=
    { toLinearMap := (pauliZHZ : Qubit →ₗ[ℂ] Qubit)
      norm_map' := (AddMonoidHomClass.isometry_iff_norm (pauliZHZ : Qubit →ₗ[ℂ] Qubit)).1 hZHZIso }
  let idQᵢ : Qubit →ₗᵢ[ℂ] Qubit := LinearIsometry.id
  let idJᵢ : (H_A ⊗[ℂ] H_B) →ₗᵢ[ℂ] (H_A ⊗[ℂ] H_B) := LinearIsometry.id
  let PH2ᵢ : (Qubit ⊗[ℂ] Qubit) →ₗᵢ[ℂ] (Qubit ⊗[ℂ] Qubit) := TensorProduct.mapIsometry idQᵢ Hᵢ
  let PZHZ2ᵢ : (Qubit ⊗[ℂ] Qubit) →ₗᵢ[ℂ] (Qubit ⊗[ℂ] Qubit) := TensorProduct.mapIsometry idQᵢ ZHZᵢ
  let PHᵢ := TensorProduct.mapIsometry PH2ᵢ idJᵢ
  let PZHZᵢ := TensorProduct.mapIsometry PZHZ2ᵢ idJᵢ
  let PH : ((Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B)) →ₗ[ℂ]
      ((Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B)) :=
    (((LinearMap.id : Qubit →ₗ[ℂ] Qubit) ⊗ₗ Hadamard) ⊗ₗ idJ)
  let PZHZ : ((Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B)) →ₗ[ℂ]
      ((Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B)) :=
    (((LinearMap.id : Qubit →ₗ[ℂ] Qubit) ⊗ₗ pauliZHZ) ⊗ₗ idJ)
  have hPHIso : Isometry PH := by
    simpa [PH, PHᵢ, PH2ᵢ, idJᵢ, idQᵢ, Hᵢ, TensorProduct.mapIsometry_apply] using PHᵢ.isometry
  have hPZHZIso : Isometry PZHZ := by
    simpa [PZHZ, PZHZᵢ, PZHZ2ᵢ, idJᵢ, idQᵢ, ZHZᵢ, TensorProduct.mapIsometry_apply] using PZHZᵢ.isometry

  have hB0_vec : regSwap ((V_A ⊗ₗ V_B) ((applyBob S.B0) S.psi)) = PH Ψ := by
    have hpre :
        (V_A ⊗ₗ V_B) ((applyBob S.B0) S.psi) =
          ((((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ
                (Hadamard ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))) ∘ₗ
              (V_A ⊗ₗ V_B)) S.psi) := by
      simpa [V_A, V_B, applyBob, LinearMap.comp_apply] using
        congrArg (fun f => f S.psi) (b0_extraction_intertwining (S := S))
    have hnat :=
      congrArg (fun f => f ((V_A ⊗ₗ V_B) S.psi))
        (regSwap_qubit_naturality (H_A := H_A) (H_B := H_B)
          (fA := (LinearMap.id : Qubit →ₗ[ℂ] Qubit)) (fB := Hadamard))
    have hnat' :
        regSwap (H_A := H_A) (H_B := H_B)
            ((((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ
                  (Hadamard ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)))
              ((V_A ⊗ₗ V_B) S.psi))) = PH Ψ := by
      simpa [PH, Ψ, idJ, LinearMap.comp_apply] using hnat.symm
    simpa [hpre] using hnat'

  have hB0_bound :
      ‖regSwap ((V_A ⊗ₗ V_B) ((applyBob S.B0) S.psi))
          - ((LinearMap.id ⊗ₗ Hadamard) bellState) ⊗ₜ[ℂ] junk‖
        ≤ Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
    have hEq : ‖PH (Ψ - bellState ⊗ₜ[ℂ] junk)‖ = ‖Ψ - bellState ⊗ₜ[ℂ] junk‖ := by
      exact (AddMonoidHomClass.isometry_iff_norm PH).1 hPHIso (Ψ - bellState ⊗ₜ[ℂ] junk)
    have h0 : ‖PH (Ψ - bellState ⊗ₜ[ℂ] junk)‖ ≤ Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
      have hbase : ‖Ψ - bellState ⊗ₜ[ℂ] junk‖ ≤ Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
        simpa [junk] using hjunk
      simpa only [hEq] using hbase
    have h1 :
        ‖PH Ψ - PH (bellState ⊗ₜ[ℂ] junk)‖ ≤ Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
      simpa [LinearMap.map_sub] using h0
    simpa [hB0_vec, junk, PH, TensorProduct.map_tmul, LinearMap.id_apply] using h1

  have hB1_pre := (b1_extraction_approx (S := S) (epsilon := ε) hBias)
  have hB1_post :
      ‖regSwap ((V_A ⊗ₗ V_B) ((applyBob S.B1) S.psi)) - PZHZ Ψ‖
        ≤ Real.sqrt (cConst * ε) := by
    let u := (((V_A ⊗ₗ V_B) ∘ₗ ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B1)) S.psi)
    let v := ((((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ
          (pauliZHZ ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))) ∘ₗ (V_A ⊗ₗ V_B)) S.psi)
    have huv : ‖u - v‖ ≤ Real.sqrt (cConst * ε) := by
      simpa [u, v, V_A, V_B, S.psi_norm, mul_one, sub_eq_add_neg] using hB1_pre
    have huv' : ‖regSwap (H_A := H_A) (H_B := H_B) (u - v)‖ ≤ Real.sqrt (cConst * ε) := by
      simpa only [regSwap_norm (ψ := (u - v))] using huv
    have huv'' :
        ‖regSwap (H_A := H_A) (H_B := H_B) u - regSwap (H_A := H_A) (H_B := H_B) v‖
          ≤ Real.sqrt (cConst * ε) := by
      simpa [LinearMap.map_sub] using huv'
    have hnat := congrArg (fun f => f ((V_A ⊗ₗ V_B) S.psi))
      (regSwap_qubit_naturality (H_A := H_A) (H_B := H_B)
        (fA := (LinearMap.id : Qubit →ₗ[ℂ] Qubit)) (fB := pauliZHZ))
    have hrew : regSwap (H_A := H_A) (H_B := H_B) v = PZHZ Ψ := by
      simpa [PZHZ, Ψ, v, idJ, LinearMap.comp_apply] using hnat.symm
    simpa [u, applyBob, LinearMap.comp_apply, hrew] using huv''

  have hPZHZ_bound :
      ‖(PZHZ Ψ - ((LinearMap.id ⊗ₗ pauliZHZ) bellState) ⊗ₜ[ℂ] junk)‖
        ≤ Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
    have hEq : ‖PZHZ (Ψ - bellState ⊗ₜ[ℂ] junk)‖ = ‖Ψ - bellState ⊗ₜ[ℂ] junk‖ := by
      exact (AddMonoidHomClass.isometry_iff_norm PZHZ).1 hPZHZIso (Ψ - bellState ⊗ₜ[ℂ] junk)
    have h0 : ‖PZHZ (Ψ - bellState ⊗ₜ[ℂ] junk)‖ ≤ Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
      have hbase : ‖Ψ - bellState ⊗ₜ[ℂ] junk‖ ≤ Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
        simpa [junk] using hjunk
      simpa only [hEq] using hbase
    have h1 :
        ‖PZHZ Ψ - PZHZ (bellState ⊗ₜ[ℂ] junk)‖ ≤ Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
      simpa [LinearMap.map_sub] using h0
    simpa [PZHZ, junk, TensorProduct.map_tmul, LinearMap.id_apply] using h1

  have hB1_bound :
      ‖(regSwap ((V_A ⊗ₗ V_B) ((applyBob S.B1) S.psi))
          - ((LinearMap.id ⊗ₗ pauliZHZ) bellState) ⊗ₜ[ℂ] junk)‖
        ≤ Real.sqrt (cConst * ε) + Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
    set a :=
      regSwap ((V_A ⊗ₗ V_B) ((applyBob S.B1) S.psi)) with ha
    set b := PZHZ Ψ with hb
    set c := ((LinearMap.id ⊗ₗ pauliZHZ) bellState) ⊗ₜ[ℂ] junk with hc
    have htri : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
      have habc : a - c = (a - b) + (b - c) := by abel
      have hnorm : ‖a - c‖ = ‖(a - b) + (b - c)‖ := by
        simp only [sub_add_sub_cancel]
      simpa [hnorm] using (norm_add_le (a - b) (b - c))
    have hsum :
        ‖a - b‖ + ‖b - c‖ ≤
          Real.sqrt (cConst * ε) + Real.sqrt (2 * Real.sqrt 2 * delta ε) := by
      have := add_le_add hB1_post hPZHZ_bound
      simpa [ha, hb, hc] using this
    exact le_trans (by simpa [ha, hb, hc] using htri) hsum
  exact ⟨V_A, V_B, junk, hVA, hVB, hB0_bound, hB1_bound⟩

end MainTheorems

end Approximate_Rigidity
