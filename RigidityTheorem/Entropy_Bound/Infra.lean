import Quantum.Density
import Quantum.TraceDistance
import Quantum.POVM
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

open scoped TensorProduct InnerProductSpace
open Quantum

namespace Entropy_Bound

section ClassicalRegister

/-- Classical basis vector `|x⟩` for a finite register `X`. -/
noncomputable def classicalKet
    {X : Type*} [Fintype X] (x : X) : EuclideanSpace ℂ X := by
  classical
  exact EuclideanSpace.single (𝕜 := ℂ) (ι := X) x 1

/-- Rank-one projector `|x⟩⟨x|` on a finite classical register `X`. -/
noncomputable def classicalProjector
    {X : Type*} [Fintype X] (x : X) : Operator (EuclideanSpace ℂ X) :=
  pureOp (classicalKet (X := X) x)

/-- Uniform classical bit tensored with Eve's state. -/
noncomputable def idealBitTensorState {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (σE : Operator E) :
    Operator (Qubit ⊗[ℂ] E) :=
  ∑ x : Fin 2, (classicalProjector (X := Fin 2) x) ⊗ₗ ((1 / 2 : ℂ) • σE)

/-- Mark a state as classical on the bit register and independent of Eve. -/
def IsUniformBitIndependent {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (σXE : Operator (Qubit ⊗[ℂ] E)) : Prop :=
  ∃ σE : DensityOperator E, σXE = idealBitTensorState (σE : Operator E)

end ClassicalRegister

section TensorProjectorHelpers

private lemma inner_contractLeft_eq_inner_tensorLeft
    {H K : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    (h : H) (ψ : K) (z : H ⊗[ℂ] K) :
    ⟪ψ, Quantum.contractLeft (H := H) (K := K) h z⟫_ℂ
      = ⟪Quantum.tensorLeft (H := H) (K := K) h ψ, z⟫_ℂ := by
  refine TensorProduct.induction_on z ?h0 ?ht ?ha
  · simp [Quantum.contractLeft]
  · intro h' k
    simp [Quantum.contractLeft, Quantum.tensorLeft, TensorProduct.inner_tmul, inner_smul_right]
  · intro z₁ z₂ hz₁ hz₂
    simp [hz₁, hz₂, inner_add_right]

private lemma inner_contractLeft_left_eq_inner_tensorLeft
    {H K : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    (h : H) (z : H ⊗[ℂ] K) (ψ : K) :
    ⟪Quantum.contractLeft (H := H) (K := K) h z, ψ⟫_ℂ
      = ⟪z, Quantum.tensorLeft (H := H) (K := K) h ψ⟫_ℂ := by
  calc
    ⟪Quantum.contractLeft (H := H) (K := K) h z, ψ⟫_ℂ
        = star (⟪ψ, Quantum.contractLeft (H := H) (K := K) h z⟫_ℂ) := by
            simp
    _ = star (⟪Quantum.tensorLeft (H := H) (K := K) h ψ, z⟫_ℂ) := by
          rw [inner_contractLeft_eq_inner_tensorLeft (h := h) (ψ := ψ) (z := z)]
    _ = ⟪z, Quantum.tensorLeft (H := H) (K := K) h ψ⟫_ℂ := by
          exact inner_conj_symm z (Quantum.tensorLeft (H := H) (K := K) h ψ)

private lemma adjoint_tensorLeft_eq_contractLeft
    {H K : Type*}
    [CpxFiniteHilbert H] [CpxFiniteHilbert K]
    (h : H) :
    LinearMap.adjoint (Quantum.tensorLeft (H := H) (K := K) h)
      = Quantum.contractLeft (H := H) (K := K) h := by
  apply LinearMap.ext
  intro z
  apply ext_inner_right ℂ
  intro ψ
  calc
    ⟪(LinearMap.adjoint (Quantum.tensorLeft (H := H) (K := K) h)) z, ψ⟫_ℂ
        = ⟪z, (Quantum.tensorLeft (H := H) (K := K) h) ψ⟫_ℂ := by
            simpa using
              (LinearMap.adjoint_inner_left (A := Quantum.tensorLeft (H := H) (K := K) h)
                (x := ψ) (y := z))
    _ = ⟪Quantum.contractLeft (H := H) (K := K) h z, ψ⟫_ℂ := by
          simpa using
            (inner_contractLeft_left_eq_inner_tensorLeft (h := h) (z := z) (ψ := ψ)).symm

private lemma projector_tensor_eq_conj
    {E : Type*} [CpxFiniteHilbert E]
    (x : Fin 2) (A : Operator E) :
    ((classicalProjector (X := Fin 2) x) ⊗ₗ A)
      = (Quantum.tensorLeft (H := EuclideanSpace ℂ (Fin 2)) (K := E)
            (classicalKet (X := Fin 2) x))
          ∘ₗ A
          ∘ₗ (LinearMap.adjoint
            (Quantum.tensorLeft (H := EuclideanSpace ℂ (Fin 2)) (K := E)
              (classicalKet (X := Fin 2) x))) := by
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?h0 ?ht ?ha
  · simp
  · intro q k
    rw [adjoint_tensorLeft_eq_contractLeft (H := EuclideanSpace ℂ (Fin 2))
      (K := E) (h := classicalKet (X := Fin 2) x)]
    simp [classicalProjector, pureOp, Quantum.tensorLeft, Quantum.contractLeft,
      LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.smul_tmul']
  · intro z₁ z₂ hz₁ hz₂
    simp [hz₁, hz₂]

end TensorProjectorHelpers

section DecisionOperatorEffects

theorem classicalProjector_tensor_isPositive
    {E : Type*} [CpxFiniteHilbert E]
    (x : Fin 2) (A : Operator E) (hA : A.IsPositive) :
    (((classicalProjector (X := Fin 2) x) ⊗ₗ A)
      : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)).IsPositive := by
  have hconj :
      ((Quantum.tensorLeft (H := EuclideanSpace ℂ (Fin 2)) (K := E) (classicalKet (X := Fin 2) x))
        ∘ₗ A
        ∘ₗ (LinearMap.adjoint
          (Quantum.tensorLeft (H := EuclideanSpace ℂ (Fin 2)) (K := E)
            (classicalKet (X := Fin 2) x)))).IsPositive := by
    exact LinearMap.IsPositive.conj_adjoint hA
      (Quantum.tensorLeft (H := EuclideanSpace ℂ (Fin 2)) (K := E)
        (classicalKet (X := Fin 2) x))
  simpa [projector_tensor_eq_conj (E := E) x A] using hconj

private lemma projector_sum_fin2 :
    (∑ x : Fin 2, classicalProjector (X := Fin 2) x)
      = (LinearMap.id : Operator (EuclideanSpace ℂ (Fin 2))) := by
  ext q i
  fin_cases i
  · simp [Fin.sum_univ_two, classicalProjector, classicalKet, pureOp,
      EuclideanSpace.single_apply, EuclideanSpace.inner_single_left]
  · simp [Fin.sum_univ_two, classicalProjector, classicalKet, pureOp,
      EuclideanSpace.single_apply, EuclideanSpace.inner_single_left]

private theorem decisionOp_isPositive_fin2
    {E : Type*} [CpxFiniteHilbert E]
    (M : POVM (Fin 2) E) :
    ((∑ x : Fin 2,
        (classicalProjector (X := Fin 2) x) ⊗ₗ (M.effect x))
      : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)).IsPositive := by
  rw [Fin.sum_univ_two]
  exact (classicalProjector_tensor_isPositive (E := E) 0 (M.effect 0) (M.effect_pos 0)).add
    (classicalProjector_tensor_isPositive (E := E) 1 (M.effect 1) (M.effect_pos 1))

private theorem decisionOp_complement_eq_fin2
    {E : Type*} [CpxFiniteHilbert E]
    (M : POVM (Fin 2) E) :
    ((LinearMap.id : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))
      - (∑ x : Fin 2, (classicalProjector (X := Fin 2) x) ⊗ₗ (M.effect x)))
      = (∑ x : Fin 2, (classicalProjector (X := Fin 2) x)
          ⊗ₗ ((LinearMap.id : Operator E) - M.effect x)) := by
  let P0 : Operator (EuclideanSpace ℂ (Fin 2)) := classicalProjector (X := Fin 2) 0
  let P1 : Operator (EuclideanSpace ℂ (Fin 2)) := classicalProjector (X := Fin 2) 1
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on z ?h0 ?ht ?ha
  · simp
  · intro q k
    have hsplitq : q = P0 q + P1 q := by
      have hq := congrArg (fun T : Operator (EuclideanSpace ℂ (Fin 2)) => T q) projector_sum_fin2
      simpa [P0, P1, Fin.sum_univ_two] using hq.symm
    have hsplit_tmul : q ⊗ₜ[ℂ] k = (P0 q ⊗ₜ[ℂ] k) + (P1 q ⊗ₜ[ℂ] k) := by
      conv_lhs => rw [hsplitq]
      rw [TensorProduct.add_tmul]
    rw [LinearMap.sub_apply]
    simp only [LinearMap.id_coe, id_eq, Fin.sum_univ_two, Fin.isValue, LinearMap.add_apply,
      TensorProduct.map_tmul, LinearMap.sub_apply]
    rw [hsplit_tmul, TensorProduct.tmul_sub, TensorProduct.tmul_sub]
    simp [sub_eq_add_neg]
    ac_rfl
  · intro z₁ z₂ hz₁ hz₂
    calc
      ((LinearMap.id : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))
        - (∑ x : Fin 2, (classicalProjector (X := Fin 2) x) ⊗ₗ (M.effect x)))
        (z₁ + z₂)
          = ((LinearMap.id : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))
              - (∑ x : Fin 2, (classicalProjector (X := Fin 2) x) ⊗ₗ (M.effect x))) z₁
            + ((LinearMap.id : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))
              - (∑ x : Fin 2, (classicalProjector (X := Fin 2) x) ⊗ₗ (M.effect x))) z₂ := by
              simp [LinearMap.map_add]
      _ = (∑ x : Fin 2, (classicalProjector (X := Fin 2) x)
            ⊗ₗ ((LinearMap.id : Operator E) - M.effect x)) z₁
          + (∑ x : Fin 2, (classicalProjector (X := Fin 2) x)
            ⊗ₗ ((LinearMap.id : Operator E) - M.effect x)) z₂ := by
            rw [hz₁, hz₂]
      _ = (∑ x : Fin 2, (classicalProjector (X := Fin 2) x)
            ⊗ₗ ((LinearMap.id : Operator E) - M.effect x))
            (z₁ + z₂) := by
            simp [LinearMap.map_add]

private lemma effect_complement_zero
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (M : POVM (Fin 2) E) :
    (LinearMap.id : Operator E) - M.effect 0 = M.effect 1 := by
  have hsum : M.effect 0 + M.effect 1 = (LinearMap.id : Operator E) := by
    have hs := M.sum_effect
    rw [Fin.sum_univ_two] at hs
    exact hs
  calc
    (LinearMap.id : Operator E) - M.effect 0
        = (M.effect 0 + M.effect 1) - M.effect 0 := by rw [← hsum]
    _ = M.effect 1 := by
      abel

private lemma effect_complement_one
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (M : POVM (Fin 2) E) :
    (LinearMap.id : Operator E) - M.effect 1 = M.effect 0 := by
  have hsum : M.effect 0 + M.effect 1 = (LinearMap.id : Operator E) := by
    have hs := M.sum_effect
    rw [Fin.sum_univ_two] at hs
    exact hs
  calc
    (LinearMap.id : Operator E) - M.effect 1
        = (M.effect 0 + M.effect 1) - M.effect 1 := by rw [← hsum]
    _ = M.effect 0 := by
      abel

private theorem decisionOp_complement_isPositive_fin2
    {E : Type*} [CpxFiniteHilbert E]
    (M : POVM (Fin 2) E) :
    ((LinearMap.id : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))
      - (∑ x : Fin 2, (classicalProjector (X := Fin 2) x) ⊗ₗ (M.effect x))).IsPositive := by
  have hComp0 : ((LinearMap.id : Operator E) - M.effect 0).IsPositive := by
    rw [effect_complement_zero (M := M)]
    exact M.effect_pos 1
  have hComp1 : ((LinearMap.id : Operator E) - M.effect 1).IsPositive := by
    rw [effect_complement_one (M := M)]
    exact M.effect_pos 0
  have hSumComp :
      ((∑ x : Fin 2, (classicalProjector (X := Fin 2) x)
        ⊗ₗ ((LinearMap.id : Operator E) - M.effect x))
        : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)).IsPositive := by
    rw [Fin.sum_univ_two]
    exact (classicalProjector_tensor_isPositive (E := E) 0
      ((LinearMap.id : Operator E) - M.effect 0) hComp0).add
      (classicalProjector_tensor_isPositive (E := E) 1
        ((LinearMap.id : Operator E) - M.effect 1) hComp1)
  rw [decisionOp_complement_eq_fin2 (M := M)]
  exact hSumComp

/-!
Binary POVM decision operators are effects.
-/
theorem decisionOp_isEffect_fin2
    {E : Type*} [CpxFiniteHilbert E]
    (M : POVM (Fin 2) E) :
    IsEffect
      (((∑ x : Fin 2, (classicalProjector (X := Fin 2) x) ⊗ₗ (M.effect x))
        : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))) := by
  constructor
  · exact decisionOp_isPositive_fin2 (E := E) M
  · exact decisionOp_complement_isPositive_fin2 (E := E) M

end DecisionOperatorEffects

section EffectVariationalCore

private theorem re_trace_nonneg_of_isPositive
    {H : Type*} [CpxFiniteHilbert H]
    {T : Operator H}
    (hT : T.IsPositive) :
    0 ≤ Complex.re (trace T) := by
  let b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H := stdOrthonormalBasis ℂ H
  have hsum :
      0 ≤
        ∑ i : Fin (Module.finrank ℂ H),
          Complex.re ⟪b i, T (b i)⟫_ℂ := by
    refine Finset.sum_nonneg ?_
    intro i hi
    simpa using hT.re_inner_nonneg_right (b i)
  have htrace :
      trace T =
        ∑ i : Fin (Module.finrank ℂ H), ⟪b i, T (b i)⟫_ℂ := by
    simpa [trace, b] using
      (LinearMap.trace_eq_sum_inner (T := T) (b := b))
  calc
    0 ≤
      ∑ i : Fin (Module.finrank ℂ H),
        Complex.re ⟪b i, T (b i)⟫_ℂ := hsum
    _ = Complex.re
        (∑ i : Fin (Module.finrank ℂ H), ⟪b i, T (b i)⟫_ℂ) := by
          simp
    _ = Complex.re (trace T) := by simp [htrace]

private theorem re_trace_mul_nonneg_of_isPositive
    {H : Type*} [CpxFiniteHilbert H]
    {A B : Operator H}
    (hA : A.IsPositive) (hB : B.IsPositive) :
    0 ≤ Complex.re (trace (B * A)) := by
  let Ac : H →L[ℂ] H := LinearMap.toContinuousLinearMap A
  let Bc : H →L[ℂ] H := LinearMap.toContinuousLinearMap B
  have hAc : Ac.IsPositive := by
    simpa [Ac] using (LinearMap.isPositive_toContinuousLinearMap_iff A).2 hA
  have hBc : Bc.IsPositive := by
    simpa [Bc] using (LinearMap.isPositive_toContinuousLinearMap_iff B).2 hB
  obtain ⟨C, hC⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self).1
    ((ContinuousLinearMap.nonneg_iff_isPositive Bc).2 hBc)
  let CAC_adj : H →L[ℂ] H := C.comp (Ac.comp (ContinuousLinearMap.adjoint C))
  have hConj : (CAC_adj : Operator H).IsPositive :=
    ContinuousLinearMap.IsPositive.toLinearMap _
      (ContinuousLinearMap.IsPositive.conj_adjoint (hT := hAc) (S := C))
  have hBc_lin : (B : Operator H) = ((star C * C : H →L[ℂ] H) : Operator H) := by
    simpa [Bc] using congrArg (fun T : H →L[ℂ] H => (T : Operator H)) hC
  have htrace_cycle : trace (B * A) = trace (CAC_adj : Operator H) :=
    calc trace (B * A)
        = trace (((star C : H →L[ℂ] H) : Operator H)
            * (((C : H →L[ℂ] H) : Operator H) * A)) := by
              rw [hBc_lin]
              change trace (((star C : H →L[ℂ] H) : Operator H)
                * ((C : H →L[ℂ] H) : Operator H) * A) = _
              rw [mul_assoc]
      _ = trace ((((C : H →L[ℂ] H) : Operator H) * A)
            * ((ContinuousLinearMap.adjoint C : H →L[ℂ] H) : Operator H)) := by
              simpa [ContinuousLinearMap.star_eq_adjoint] using
                LinearMap.trace_mul_comm ℂ ((star C : H →L[ℂ] H) : Operator H)
                  (((C : H →L[ℂ] H) : Operator H) * A)
      _ = trace (CAC_adj : Operator H) := by congr 1
  simpa [htrace_cycle] using re_trace_nonneg_of_isPositive hConj

theorem re_trace_mul_le_re_trace_of_isPositive_of_isEffectLike
    {H : Type*} [CpxFiniteHilbert H]
    {A B : Operator H}
    (hA : A.IsPositive)
    (hB_le_one : ((LinearMap.id : Operator H) - B).IsPositive) :
    Complex.re (trace (B * A)) ≤ Complex.re (trace A) := by
  have hnonneg :
      0 ≤ Complex.re (trace (((LinearMap.id : Operator H) - B) * A)) :=
    re_trace_mul_nonneg_of_isPositive (A := A) (B := (LinearMap.id : Operator H) - B)
      hA hB_le_one
  have htrace_expand :
      trace (((LinearMap.id : Operator H) - B) * A) = trace A - trace (B * A) := by
    calc
      trace (((LinearMap.id : Operator H) - B) * A)
          = trace (((LinearMap.id : Operator H) * A) - (B * A)) := by
              simp [sub_mul]
      _ = trace ((LinearMap.id : Operator H) * A) - trace (B * A) := by
            unfold trace
            simp
      _ = trace A - trace (B * A) := by
            rw [Module.End.mul_eq_comp, LinearMap.id_comp]
  have hreal :
      0 ≤ Complex.re (trace A) - Complex.re (trace (B * A)) := by
    simpa [htrace_expand, Complex.sub_re] using hnonneg
  linarith

private lemma abs_toContinuous_eq_operatorSqrt_adjoint_mul
    {H : Type*} [CpxFiniteHilbert H]
    (X : Operator H) :
    (((CFC.abs (LinearMap.toContinuousLinearMap X)) : H →L[ℂ] H) : Operator H)
      = operatorSqrt ((LinearMap.adjoint X) ∘ₗ X) := by
  let Xc : H →L[ℂ] H := LinearMap.toContinuousLinearMap X
  have hadj : star Xc = LinearMap.toContinuousLinearMap (LinearMap.adjoint X) := by
    simpa [Xc, ContinuousLinearMap.star_eq_adjoint] using
      (LinearMap.adjoint_toContinuousLinearMap (A := X)).symm
  have hmul : (star Xc * Xc : H →L[ℂ] H)
      = LinearMap.toContinuousLinearMap ((LinearMap.adjoint X) ∘ₗ X) := by
    rw [hadj]
    rfl
  calc
    (((CFC.abs (LinearMap.toContinuousLinearMap X)) : H →L[ℂ] H) : Operator H)
        = (((CFC.sqrt (star Xc * Xc)) : H →L[ℂ] H) : Operator H) := by
            simp [CFC.abs, Xc]
    _ = (((cfcₙ Real.sqrt (star Xc * Xc)) : H →L[ℂ] H) : Operator H) := by
          simp [CFC.sqrt_eq_real_sqrt]
    _ = (((cfcₙ Real.sqrt (LinearMap.toContinuousLinearMap ((LinearMap.adjoint X) ∘ₗ X)))
          : H →L[ℂ] H) : Operator H) := by
          simp [hmul]
    _ = operatorSqrt ((LinearMap.adjoint X) ∘ₗ X) := by
          simp [operatorSqrt]


set_option maxHeartbeats 400000 in
private lemma re_trace_posPart_eq_half_traceNorm_of_isHermitian_of_trace_zero
    {H : Type*} [CpxFiniteHilbert H]
    (X : Operator H)
    (hHerm : IsHermitian X)
    (htr0 : trace X = 0) :
    Complex.re (trace (((LinearMap.toContinuousLinearMap X)⁺ : H →L[ℂ] H) : Operator H))
      = (1 / 2 : Real) * traceNorm X := by
  let Xc : H →L[ℂ] H := LinearMap.toContinuousLinearMap X
  have hXc_sa : IsSelfAdjoint Xc := by
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).2 (by simpa [Xc] using hHerm)
  have hdecomp :
      (((Xc)⁺ : H →L[ℂ] H) : Operator H) - (((Xc)⁻ : H →L[ℂ] H) : Operator H) = X := by
    have h := CFC.posPart_sub_negPart Xc hXc_sa
    exact congrArg (fun T : H →L[ℂ] H => (T : Operator H)) h
  have habs :
      (((Xc)⁺ : H →L[ℂ] H) : Operator H) + (((Xc)⁻ : H →L[ℂ] H) : Operator H)
        = (((CFC.abs Xc) : H →L[ℂ] H) : Operator H) := by
    have h := CFC.posPart_add_negPart Xc hXc_sa
    exact congrArg (fun T : H →L[ℂ] H => (T : Operator H)) h
  have htr_diff :
      trace (((Xc)⁺ : H →L[ℂ] H) : Operator H)
        - trace (((Xc)⁻ : H →L[ℂ] H) : Operator H) = 0 := by
    calc
      trace (((Xc)⁺ : H →L[ℂ] H) : Operator H)
          - trace (((Xc)⁻ : H →L[ℂ] H) : Operator H)
          = trace ((((Xc)⁺ : H →L[ℂ] H) : Operator H) - (((Xc)⁻ : H →L[ℂ] H) : Operator H)) := by
              unfold trace
              simp
      _ = trace X := by simp [hdecomp]
      _ = 0 := htr0
  have htr_sum :
      trace (((Xc)⁺ : H →L[ℂ] H) : Operator H)
        + trace (((Xc)⁻ : H →L[ℂ] H) : Operator H)
      = trace (((CFC.abs Xc : H →L[ℂ] H) : Operator H)) := by
    calc
      trace (((Xc)⁺ : H →L[ℂ] H) : Operator H)
          + trace (((Xc)⁻ : H →L[ℂ] H) : Operator H)
          = trace ((((Xc)⁺ : H →L[ℂ] H) : Operator H) + (((Xc)⁻ : H →L[ℂ] H) : Operator H)) := by
              unfold trace
              simp
      _ = trace (((CFC.abs Xc : H →L[ℂ] H) : Operator H)) := by simp [habs]
  have hEqRe :
      Complex.re (trace (((Xc)⁺ : H →L[ℂ] H) : Operator H))
        = Complex.re (trace (((Xc)⁻ : H →L[ℂ] H) : Operator H)) := by
    have htr_diff_re :
        Complex.re (trace (((Xc)⁺ : H →L[ℂ] H) : Operator H)
          - trace (((Xc)⁻ : H →L[ℂ] H) : Operator H)) = 0 := by
      simp [htr_diff]
    have hsub :
        Complex.re (trace (((Xc)⁺ : H →L[ℂ] H) : Operator H))
          - Complex.re (trace (((Xc)⁻ : H →L[ℂ] H) : Operator H)) = 0 := by
      simpa [Complex.sub_re] using htr_diff_re
    linarith
  have hNorm :
      traceNorm X =
        Complex.re (trace (((CFC.abs Xc : H →L[ℂ] H) : Operator H))) := by
    calc
      traceNorm X
          = Complex.re (trace (operatorSqrt ((LinearMap.adjoint X) ∘ₗ X))) := rfl
      _ = Complex.re (trace (((CFC.abs Xc : H →L[ℂ] H) : Operator H))) := by
            simp [Xc, abs_toContinuous_eq_operatorSqrt_adjoint_mul]
  have hsum_re :
      Complex.re (trace (((Xc)⁺ : H →L[ℂ] H) : Operator H))
        + Complex.re (trace (((Xc)⁻ : H →L[ℂ] H) : Operator H))
      = traceNorm X := by
    calc
      Complex.re (trace (((Xc)⁺ : H →L[ℂ] H) : Operator H))
          + Complex.re (trace (((Xc)⁻ : H →L[ℂ] H) : Operator H))
          = Complex.re (trace (((Xc)⁺ : H →L[ℂ] H) : Operator H)
              + trace (((Xc)⁻ : H →L[ℂ] H) : Operator H)) := by
                simp [Complex.add_re]
      _ = Complex.re (trace (((CFC.abs Xc : H →L[ℂ] H) : Operator H))) := by simp [htr_sum]
      _ = traceNorm X := by simp [hNorm]
  have hdouble :
      (2 : Real) * Complex.re (trace (((Xc)⁺ : H →L[ℂ] H) : Operator H)) = traceNorm X := by
    calc
      (2 : Real) * Complex.re (trace (((Xc)⁺ : H →L[ℂ] H) : Operator H))
          = Complex.re (trace (((Xc)⁺ : H →L[ℂ] H) : Operator H))
            + Complex.re (trace (((Xc)⁺ : H →L[ℂ] H) : Operator H)) := by ring
      _ = Complex.re (trace (((Xc)⁺ : H →L[ℂ] H) : Operator H))
            + Complex.re (trace (((Xc)⁻ : H →L[ℂ] H) : Operator H)) := by
            simp [hEqRe]
      _ = traceNorm X := hsum_re
  have hfinal :
      Complex.re (trace (((Xc)⁺ : H →L[ℂ] H) : Operator H)) = (1 / 2 : Real) * traceNorm X := by
    linarith [hdouble]
  simpa [Xc] using hfinal

private theorem re_trace_mul_le_half_traceNorm_of_effect_of_isHermitian_of_trace_zero
    {H : Type*} [CpxFiniteHilbert H]
    {B X : Operator H}
    (hB_nonneg : B.IsPositive)
    (hB_le_one : ((LinearMap.id : Operator H) - B).IsPositive)
    (hX_herm : IsHermitian X)
    (hX_tr0 : trace X = 0) :
    Complex.re (trace (B * X)) ≤ (1 / 2 : Real) * traceNorm X := by
  let Xc : H →L[ℂ] H := LinearMap.toContinuousLinearMap X
  have hXc_sa : IsSelfAdjoint Xc := by
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).2 (by simpa [Xc] using hX_herm)
  let Xp : Operator H := (((Xc)⁺ : H →L[ℂ] H) : Operator H)
  let Xm : Operator H := (((Xc)⁻ : H →L[ℂ] H) : Operator H)
  have hdecomp : X = Xp - Xm := by
    have h := CFC.posPart_sub_negPart Xc hXc_sa
    have h' := congrArg (fun T : H →L[ℂ] H => (T : Operator H)) h
    simpa [Xp, Xm, sub_eq_add_neg] using h'.symm
  have hXp_nonneg_clm : (0 : H →L[ℂ] H) ≤ (Xc)⁺ := CFC.posPart_nonneg Xc
  have hXm_nonneg_clm : (0 : H →L[ℂ] H) ≤ (Xc)⁻ := CFC.negPart_nonneg Xc
  have hXp_pos : Xp.IsPositive := by
    exact (ContinuousLinearMap.IsPositive.toLinearMap _)
      ((ContinuousLinearMap.nonneg_iff_isPositive ((Xc)⁺)).1 hXp_nonneg_clm)
  have hXm_pos : Xm.IsPositive := by
    exact (ContinuousLinearMap.IsPositive.toLinearMap _)
      ((ContinuousLinearMap.nonneg_iff_isPositive ((Xc)⁻)).1 hXm_nonneg_clm)
  have htrace_expand :
      trace (B * X) = trace (B * Xp) - trace (B * Xm) := by
    calc
      trace (B * X) = trace (B * (Xp - Xm)) := by simp [hdecomp]
      _ = trace ((B * Xp) - (B * Xm)) := by simp [mul_sub]
      _ = trace (B * Xp) - trace (B * Xm) := by
            unfold trace
            simp
  have hXm_term_nonneg : 0 ≤ Complex.re (trace (B * Xm)) :=
    re_trace_mul_nonneg_of_isPositive (A := Xm) (B := B) hXm_pos hB_nonneg
  have hXp_term_le :
      Complex.re (trace (B * Xp)) ≤ Complex.re (trace Xp) :=
    re_trace_mul_le_re_trace_of_isPositive_of_isEffectLike (A := Xp) (B := B)
      hXp_pos hB_le_one
  have hmul_le :
      Complex.re (trace (B * X)) ≤ Complex.re (trace Xp) := by
    have hreal :
        Complex.re (trace (B * X))
          = Complex.re (trace (B * Xp)) - Complex.re (trace (B * Xm)) := by
      simp [htrace_expand, Complex.sub_re]
    rw [hreal]
    linarith [hXp_term_le, hXm_term_nonneg]
  have hhalf :
      Complex.re (trace Xp) = (1 / 2 : Real) * traceNorm X :=
    re_trace_posPart_eq_half_traceNorm_of_isHermitian_of_trace_zero
      (X := X) hX_herm hX_tr0
  simpa [Xp] using hmul_le.trans_eq hhalf

/--
Effect-variational upper bound on a difference of density operators.

For any effect `B` and density operators `ρ,σ`,
\[
\operatorname{Re}\operatorname{Tr}\!\bigl(B(\rho-\sigma)\bigr)\le D(\rho,\sigma).
\]
-/
theorem re_trace_mul_le_traceDistance_of_isEffect_of_density_diff
    {H : Type*} [CpxFiniteHilbert H]
    {B : Operator H}
    (hB : IsEffect B)
    (ρ σ : DensityOperator H) :
    Complex.re
        (trace
          (B *
            (((ρ : DensityOperator H) : Operator H)
              - ((σ : DensityOperator H) : Operator H))))
      ≤ D((((ρ : DensityOperator H) : Operator H)),
          (((σ : DensityOperator H) : Operator H))) := by
  let Δ : Operator H :=
    (((ρ : DensityOperator H) : Operator H) - ((σ : DensityOperator H) : Operator H))
  have hΔ_herm : IsHermitian Δ := by
    simpa [Δ, sub_eq_add_neg] using ρ.isHermitian.sub σ.isHermitian
  have hΔ_tr0 : trace Δ = 0 := by
    calc
      trace Δ = trace (((ρ : DensityOperator H) : Operator H))
          - trace (((σ : DensityOperator H) : Operator H)) := by
            simp [Δ, trace]
      _ = 1 - 1 := by simp [ρ.trace_one, σ.trace_one]
      _ = 0 := by ring
  have hmain :
      Complex.re (trace (B * Δ)) ≤ (1 / 2 : Real) * traceNorm Δ :=
    re_trace_mul_le_half_traceNorm_of_effect_of_isHermitian_of_trace_zero
      (B := B) (X := Δ) hB.1 hB.2 hΔ_herm hΔ_tr0
  simpa [traceDistance, Δ] using hmain

end EffectVariationalCore

section DecisionOpVariational

/--
Blueprint variational lemma specialized to binary decision operators.

This corresponds to `lem:trace-variational` instantiated at
`Π_M = ∑ x, |x⟩⟨x| ⊗ M_x`.
-/
theorem trace_variational_decisionOp_fin2
    {E : Type*} [CpxFiniteHilbert E]
    (M : POVM (Fin 2) E)
    (ρ σ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) :
    Complex.re
        (trace
          ((∑ x : Fin 2,
              (classicalProjector (X := Fin 2) x) ⊗ₗ (M.effect x))
            ∘ₗ (((ρ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) : Operator
              ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))
              - ((σ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) : Operator
                ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)))))
      ≤ (1 / 2 : Real) * traceNorm
          ((((ρ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) : Operator
              ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))
            - ((σ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) : Operator
              ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)))) := by
  let Δ : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E) :=
    (((ρ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) : Operator
        ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))
      - ((σ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) : Operator
        ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)))
  have hΔ_herm : IsHermitian Δ := by
    simpa [Δ, sub_eq_add_neg] using ρ.isHermitian.sub σ.isHermitian
  have hΔ_tr0 : trace Δ = 0 := by
    calc
      trace Δ
          = trace
              (((ρ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) : Operator
                ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)))
            - trace
              (((σ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) : Operator
                ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))) := by
              simp [Δ, trace]
      _ = 1 - 1 := by simp [ρ.trace_one, σ.trace_one]
      _ = 0 := by ring
  have hPi_effect :
      IsEffect
        (((∑ x : Fin 2, (classicalProjector (X := Fin 2) x) ⊗ₗ (M.effect x))
          : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))) :=
    decisionOp_isEffect_fin2 (E := E) M
  simpa [Δ] using
    (re_trace_mul_le_half_traceNorm_of_effect_of_isHermitian_of_trace_zero
      (B := ((∑ x : Fin 2, (classicalProjector (X := Fin 2) x) ⊗ₗ (M.effect x))
        : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)))
      (X := Δ) hPi_effect.1 hPi_effect.2 hΔ_herm hΔ_tr0)

end DecisionOpVariational

section minEntropy

noncomputable def minEntropy {E : Type*} [CpxFiniteHilbert E]
    (pGuess : Real) : Real :=
  -Real.logb (2 : Real) pGuess

end minEntropy

end Entropy_Bound
