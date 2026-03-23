import Quantum.Qubit

import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.Seminorm

open scoped TensorProduct InnerProductSpace

namespace Quantum

universe u

section CoreDefinitions

/-- Bundled assumptions for finite-dimensional complex Hilbert spaces. -/
class CpxFiniteHilbert (H : Type*) extends NormedAddCommGroup H, InnerProductSpace ℂ H where
  finiteDimensional : FiniteDimensional ℂ H

attribute [instance] CpxFiniteHilbert.finiteDimensional

instance (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] :
    CpxFiniteHilbert H where
  finiteDimensional := inferInstance

/-- Density operators on complex Hilbert spaces. -/
abbrev Operator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] := H →ₗ[ℂ] H

/-- Hermitian operators on complex Hilbert spaces. -/
def IsHermitian {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (X : Operator H) : Prop :=
  X.IsSymmetric

/-- Positive-semidefinite operators via quadratic forms. -/
def IsPSD {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (X : Operator H) : Prop :=
  ∀ ψ : H, 0 ≤ Complex.re ⟪ψ, X ψ⟫_ℂ

/-- Orthogonal projectors (Hermitian idempotents). -/
def IsProjector {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : Operator H) : Prop :=
  IsHermitian P ∧ (P ∘ₗ P = P)

/-- Trace of an endomorphism. -/
noncomputable def trace {H : Type*}
    [CpxFiniteHilbert H]
    (X : Operator H) : ℂ :=
  LinearMap.trace ℂ H X


/-- Density matrices as bundled operators. -/
structure DensityOperator (H : Type*)
    [CpxFiniteHilbert H] where
  val : Operator H
  isPSD : IsPSD val
  isHermitian : IsHermitian val
  trace_one : trace val = 1

instance {H : Type*}
    [CpxFiniteHilbert H] :
    Coe (DensityOperator H) (Operator H) where
  coe ρ := ρ.val

/-- Unbundled rank-one projector `|ψ⟩⟨ψ|` as an operator. -/
noncomputable def pureOp {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ : H) : Operator H :=
  (InnerProductSpace.rankOne ℂ ψ ψ).toLinearMap

@[simp] theorem pureOp_apply {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ φ : H) :
    (pureOp ψ) φ = (⟪ψ, φ⟫_ℂ) • ψ := by
  simp [pureOp, InnerProductSpace.rankOne_apply]

/-- Pure-state density operator `|ψ⟩⟨ψ|`. -/
noncomputable def pureDM {H : Type*}
    [CpxFiniteHilbert H]
    (ψ : H) (hψ : ‖ψ‖ = 1) : DensityOperator H := by
  let hPosCLM : (InnerProductSpace.rankOne ℂ ψ ψ).IsPositive := by
    exact (InnerProductSpace.isPositive_rankOne_self (𝕜 := ℂ) ψ)
  let hPos : (pureOp ψ).IsPositive := by
    simpa [pureOp] using
      (ContinuousLinearMap.isPositive_toLinearMap_iff (InnerProductSpace.rankOne ℂ ψ ψ)).2 hPosCLM
  refine
    { val := pureOp ψ
      isPSD := ?_
      isHermitian := hPos.isSymmetric
      trace_one := ?_ }
  · intro φ
    exact hPos.re_inner_nonneg_right φ
  · unfold trace pureOp
    calc
      LinearMap.trace ℂ H ((InnerProductSpace.rankOne ℂ ψ ψ).toLinearMap) = ⟪ψ, ψ⟫_ℂ := by
        simpa using (InnerProductSpace.trace_rankOne (𝕜 := ℂ) (E := H) ψ ψ)
      _ = 1 := by
        rw [inner_self_eq_norm_sq_to_K, hψ]
        norm_num

@[simp] theorem pureDM_coe {H : Type*}
    [CpxFiniteHilbert H]
    (ψ : H) (hψ : ‖ψ‖ = 1) :
    ((pureDM ψ hψ : DensityOperator H) : Operator H) = pureOp ψ := rfl

@[simp] theorem trace_pureDM_comp {H : Type*}
    [CpxFiniteHilbert H]
    (ψ : H) (hψ : ‖ψ‖ = 1) (X : Operator H) :
    trace (((pureDM ψ hψ : DensityOperator H) : Operator H) ∘ₗ X) = ⟪ψ, X ψ⟫_ℂ := by
  change trace (pureOp ψ ∘ₗ X) = ⟪ψ, X ψ⟫_ℂ
  unfold trace
  rw [LinearMap.trace_comp_comm']
  have hXP : X ∘ₗ pureOp ψ = (innerₛₗ ℂ ψ).smulRight (X ψ) := by
    ext φ
    simp [pureOp]
  rw [hXP]
  exact
    (LinearMap.trace_smulRight (R := ℂ) (M := H) (f := innerₛₗ ℂ ψ) (x := X ψ))

@[simp] theorem trace_pureOp_comp {H : Type*}
    [CpxFiniteHilbert H]
    (ψ : H) (X : Operator H) :
    trace (pureOp ψ ∘ₗ X) = ⟪ψ, X ψ⟫_ℂ := by
  unfold trace
  rw [LinearMap.trace_comp_comm']
  have hXP : X ∘ₗ pureOp ψ = (innerₛₗ ℂ ψ).smulRight (X ψ) := by
    ext φ
    simp [pureOp]
  rw [hXP]
  exact
    (LinearMap.trace_smulRight (R := ℂ) (M := H) (f := innerₛₗ ℂ ψ) (x := X ψ))

end CoreDefinitions




section PartialTraceToolkit

/-!
Concrete partial-trace and distance primitives used by the entropy-bound layer.
-/

noncomputable def tensorRight {H K : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    (k : K) : H →ₗ[ℂ] (H ⊗[ℂ] K) :=
  {
    toFun := fun h => h ⊗ₜ[ℂ] k
    map_add' := by
      intro h₁ h₂
      simp [TensorProduct.add_tmul]
    map_smul' := by
      intro c h
      simp [TensorProduct.smul_tmul']
  }

noncomputable def tensorLeft {H K : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    (h : H) : K →ₗ[ℂ] (H ⊗[ℂ] K) :=
  {
    toFun := fun k => h ⊗ₜ[ℂ] k
    map_add' := by
      intro k₁ k₂
      simp [TensorProduct.tmul_add]
    map_smul' := by
      intro c k
      calc
        h ⊗ₜ[ℂ] (c • k) = (c • h) ⊗ₜ[ℂ] k := by
          simpa using (TensorProduct.smul_tmul (R := ℂ) c h k).symm
        _ = c • (h ⊗ₜ[ℂ] k) := by
          simp [TensorProduct.smul_tmul']
  }

noncomputable def contractRight {H K : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    (k : K) : (H ⊗[ℂ] K) →ₗ[ℂ] H :=
  (TensorProduct.rid ℂ H).toLinearMap ∘ₗ (LinearMap.lTensor H ((innerₛₗ ℂ) k))

noncomputable def contractLeft {H K : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    (h : H) : (H ⊗[ℂ] K) →ₗ[ℂ] K :=
  (TensorProduct.lid ℂ K).toLinearMap ∘ₗ (LinearMap.rTensor K ((innerₛₗ ℂ) h))

noncomputable def partialTraceRight {H K : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    [FiniteDimensional ℂ K] :
    Operator (H ⊗[ℂ] K) → Operator H :=
  fun X =>
    let b := stdOrthonormalBasis ℂ K
    ∑ i : Fin (Module.finrank ℂ K),
      contractRight (H := H) (K := K) (b i) ∘ₗ X ∘ₗ tensorRight (H := H) (K := K) (b i)

noncomputable def partialTraceLeft {H K : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    [FiniteDimensional ℂ H] :
    Operator (H ⊗[ℂ] K) → Operator K :=
  fun X =>
    let b := stdOrthonormalBasis ℂ H
    ∑ i : Fin (Module.finrank ℂ H),
      contractLeft (H := H) (K := K) (b i) ∘ₗ X ∘ₗ tensorLeft (H := H) (K := K) (b i)

lemma inner_contractRight_eq_inner_tensorRight
    {H K : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    (k : K) (ψ : H) (z : H ⊗[ℂ] K) :
    ⟪ψ, contractRight (H := H) (K := K) k z⟫_ℂ
      = ⟪tensorRight (H := H) (K := K) k ψ, z⟫_ℂ := by
  refine TensorProduct.induction_on z ?h0 ?ht ?ha
  · simp [contractRight]
  · intro h k'
    simp [contractRight, tensorRight, TensorProduct.inner_tmul, inner_smul_right, mul_comm]
  · intro z₁ z₂ hz₁ hz₂
    simp [hz₁, hz₂, inner_add_right]

private lemma inner_contractRight_left_eq_inner_tensorRight
    {H K : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    (k : K) (z : H ⊗[ℂ] K) (ψ : H) :
    ⟪contractRight (H := H) (K := K) k z, ψ⟫_ℂ
      = ⟪z, tensorRight (H := H) (K := K) k ψ⟫_ℂ := by
  calc
    ⟪contractRight (H := H) (K := K) k z, ψ⟫_ℂ
        = star (⟪ψ, contractRight (H := H) (K := K) k z⟫_ℂ) := by
            simpa using (inner_conj_symm ψ (contractRight (H := H) (K := K) k z))
    _ = star (⟪tensorRight (H := H) (K := K) k ψ, z⟫_ℂ) := by
          rw [inner_contractRight_eq_inner_tensorRight (k := k) (ψ := ψ) (z := z)]
    _ = ⟪z, tensorRight (H := H) (K := K) k ψ⟫_ℂ := by
          exact inner_conj_symm z (tensorRight (H := H) (K := K) k ψ)

private lemma inner_contractLeft_eq_inner_tensorLeft
    {H K : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    (h : H) (ψ : K) (z : H ⊗[ℂ] K) :
    ⟪ψ, contractLeft (H := H) (K := K) h z⟫_ℂ
      = ⟪tensorLeft (H := H) (K := K) h ψ, z⟫_ℂ := by
  refine TensorProduct.induction_on z ?h0 ?ht ?ha
  · simp [contractLeft]
  · intro h' k
    simp [contractLeft, tensorLeft, TensorProduct.inner_tmul, inner_smul_right]
  · intro z₁ z₂ hz₁ hz₂
    simp [hz₁, hz₂, inner_add_right]

private lemma inner_contractLeft_left_eq_inner_tensorLeft
    {H K : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    (h : H) (z : H ⊗[ℂ] K) (ψ : K) :
    ⟪contractLeft (H := H) (K := K) h z, ψ⟫_ℂ
      = ⟪z, tensorLeft (H := H) (K := K) h ψ⟫_ℂ := by
  calc
    ⟪contractLeft (H := H) (K := K) h z, ψ⟫_ℂ
        = star (⟪ψ, contractLeft (H := H) (K := K) h z⟫_ℂ) := by
            simpa using (inner_conj_symm ψ (contractLeft (H := H) (K := K) h z))
    _ = star (⟪tensorLeft (H := H) (K := K) h ψ, z⟫_ℂ) := by
          rw [inner_contractLeft_eq_inner_tensorLeft (h := h) (ψ := ψ) (z := z)]
    _ = ⟪z, tensorLeft (H := H) (K := K) h ψ⟫_ℂ := by
          exact inner_conj_symm z (tensorLeft (H := H) (K := K) h ψ)

/-- Positivity is preserved by right partial trace. -/
theorem IsPSD.partialTraceRight {H K : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    [FiniteDimensional ℂ K]
    {X : Operator (H ⊗[ℂ] K)}
    (hX : IsPSD X) :
    IsPSD (Quantum.partialTraceRight (H := H) (K := K) X) := by
  intro ψ
  let b := stdOrthonormalBasis ℂ K
  have hterm :
      ∀ i : Fin (Module.finrank ℂ K),
        0 ≤ Complex.re
          ⟪ψ,
            ((contractRight (H := H) (K := K) (b i)) ∘ₗ X ∘ₗ
              (tensorRight (H := H) (K := K) (b i))) ψ⟫_ℂ := by
    intro i
    simpa [LinearMap.comp_apply, inner_contractRight_eq_inner_tensorRight]
      using hX ((tensorRight (H := H) (K := K) (b i)) ψ)
  rw [Quantum.partialTraceRight]
  simp [inner_sum]
  exact Finset.sum_nonneg (fun i _ => hterm i)

/-- Hermiticity is preserved by right partial trace. -/
theorem IsHermitian.partialTraceRight {H K : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    [FiniteDimensional ℂ K]
    {X : Operator (H ⊗[ℂ] K)}
    (hX : IsHermitian X) :
    IsHermitian (Quantum.partialTraceRight (H := H) (K := K) X) := by
  intro φ ψ
  let b := stdOrthonormalBasis ℂ K
  calc
    ⟪(Quantum.partialTraceRight (H := H) (K := K) X) φ, ψ⟫_ℂ
        = ∑ i : Fin (Module.finrank ℂ K),
            ⟪((contractRight (H := H) (K := K) (b i)) ∘ₗ X ∘ₗ
                (tensorRight (H := H) (K := K) (b i))) φ, ψ⟫_ℂ := by
            simp [Quantum.partialTraceRight, b, sum_inner]
    _ = ∑ i : Fin (Module.finrank ℂ K),
          ⟪X ((tensorRight (H := H) (K := K) (b i)) φ),
            (tensorRight (H := H) (K := K) (b i)) ψ⟫_ℂ := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [LinearMap.comp_apply, inner_contractRight_left_eq_inner_tensorRight]
    _ = ∑ i : Fin (Module.finrank ℂ K),
          ⟪(tensorRight (H := H) (K := K) (b i)) φ,
            X ((tensorRight (H := H) (K := K) (b i)) ψ)⟫_ℂ := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa [IsHermitian] using (hX ((tensorRight (H := H) (K := K) (b i)) φ)
            ((tensorRight (H := H) (K := K) (b i)) ψ))
    _ = ∑ i : Fin (Module.finrank ℂ K),
          ⟪φ,
            ((contractRight (H := H) (K := K) (b i)) ∘ₗ X ∘ₗ
              (tensorRight (H := H) (K := K) (b i))) ψ⟫_ℂ := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [LinearMap.comp_apply, inner_contractRight_eq_inner_tensorRight]
    _ = ⟪φ, (Quantum.partialTraceRight (H := H) (K := K) X) ψ⟫_ℂ := by
          simp [Quantum.partialTraceRight, b, inner_sum]

/-- Right partial trace is trace-preserving. -/
@[simp] theorem trace_partialTraceRight {H K : Type*}
    [CpxFiniteHilbert H] [CpxFiniteHilbert K]
    (X : Operator (H ⊗[ℂ] K)) :
    trace (Quantum.partialTraceRight (H := H) (K := K) X) = trace X := by
  let bH : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H := stdOrthonormalBasis ℂ H
  let bK : OrthonormalBasis (Fin (Module.finrank ℂ K)) ℂ K := stdOrthonormalBasis ℂ K
  calc
    trace (Quantum.partialTraceRight (H := H) (K := K) X)
        = ∑ i : Fin (Module.finrank ℂ H),
            ⟪bH i, (Quantum.partialTraceRight (H := H) (K := K) X) (bH i)⟫_ℂ := by
            simpa [trace, bH] using
              (LinearMap.trace_eq_sum_inner
                (T := Quantum.partialTraceRight (H := H) (K := K) X) (b := bH))
    _ = ∑ i : Fin (Module.finrank ℂ H),
          ∑ j : Fin (Module.finrank ℂ K),
            ⟪bH i ⊗ₜ[ℂ] bK j, X (bH i ⊗ₜ[ℂ] bK j)⟫_ℂ := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [Quantum.partialTraceRight, bK, inner_sum,
            inner_contractRight_eq_inner_tensorRight, tensorRight]
    _ = ∑ p : (Fin (Module.finrank ℂ H)) × (Fin (Module.finrank ℂ K)),
          ⟪bH p.1 ⊗ₜ[ℂ] bK p.2, X (bH p.1 ⊗ₜ[ℂ] bK p.2)⟫_ℂ := by
          simpa using
            (Fintype.sum_prod_type
              (f := fun p : (Fin (Module.finrank ℂ H)) × (Fin (Module.finrank ℂ K)) =>
                ⟪bH p.1 ⊗ₜ[ℂ] bK p.2, X (bH p.1 ⊗ₜ[ℂ] bK p.2)⟫_ℂ)).symm
    _ = ∑ p : (Fin (Module.finrank ℂ H)) × (Fin (Module.finrank ℂ K)),
          ⟪(bH.tensorProduct bK) p, X ((bH.tensorProduct bK) p)⟫_ℂ := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rcases p with ⟨i, j⟩
          simp [OrthonormalBasis.tensorProduct_apply]
    _ = trace X := by
          simpa [trace] using
            (LinearMap.trace_eq_sum_inner (T := X) (b := bH.tensorProduct bK)).symm

/--
Trace intertwines right partial trace with tensoring by the identity:
`Tr(A ∘ Tr_K X) = Tr((A ⊗ I_K) ∘ X)`.
-/
theorem trace_comp_partialTraceRight {H K : Type*}
    [CpxFiniteHilbert H] [CpxFiniteHilbert K]
    (A : Operator H) (X : Operator (H ⊗[ℂ] K)) :
    trace (A ∘ₗ Quantum.partialTraceRight (H := H) (K := K) X)
      = trace ((A ⊗ₗ (LinearMap.id : Operator K)) ∘ₗ X) := by
  let bH : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H := stdOrthonormalBasis ℂ H
  let bK : OrthonormalBasis (Fin (Module.finrank ℂ K)) ℂ K := stdOrthonormalBasis ℂ K
  calc
    trace (A ∘ₗ Quantum.partialTraceRight (H := H) (K := K) X)
        = trace ((Quantum.partialTraceRight (H := H) (K := K) X) ∘ₗ A) := by
            simpa [Module.End.mul_eq_comp] using
              (LinearMap.trace_mul_comm ℂ A (Quantum.partialTraceRight (H := H) (K := K) X))
    _ = ∑ i : Fin (Module.finrank ℂ H),
          ⟪bH i, (Quantum.partialTraceRight (H := H) (K := K) X) (A (bH i))⟫_ℂ := by
          simpa [trace, bH] using
            (LinearMap.trace_eq_sum_inner
              (T := ((Quantum.partialTraceRight (H := H) (K := K) X) ∘ₗ A)) (b := bH))
    _ = ∑ i : Fin (Module.finrank ℂ H),
          ∑ j : Fin (Module.finrank ℂ K),
            ⟪bH i ⊗ₜ[ℂ] bK j, X (A (bH i) ⊗ₜ[ℂ] bK j)⟫_ℂ := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [Quantum.partialTraceRight, bK, inner_sum,
            inner_contractRight_eq_inner_tensorRight, tensorRight]
    _ = ∑ p : (Fin (Module.finrank ℂ H)) × (Fin (Module.finrank ℂ K)),
          ⟪bH p.1 ⊗ₜ[ℂ] bK p.2, X (A (bH p.1) ⊗ₜ[ℂ] bK p.2)⟫_ℂ := by
          simpa using
            (Fintype.sum_prod_type
              (f := fun p : (Fin (Module.finrank ℂ H)) × (Fin (Module.finrank ℂ K)) =>
                ⟪bH p.1 ⊗ₜ[ℂ] bK p.2, X (A (bH p.1) ⊗ₜ[ℂ] bK p.2)⟫_ℂ)).symm
    _ = ∑ p : (Fin (Module.finrank ℂ H)) × (Fin (Module.finrank ℂ K)),
          ⟪(bH.tensorProduct bK) p,
            (X ∘ₗ (A ⊗ₗ (LinearMap.id : Operator K))) ((bH.tensorProduct bK) p)⟫_ℂ := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rcases p with ⟨i, j⟩
          simp [OrthonormalBasis.tensorProduct_apply, LinearMap.comp_apply]
    _ = trace (X ∘ₗ (A ⊗ₗ (LinearMap.id : Operator K))) := by
          simpa [trace] using
            (LinearMap.trace_eq_sum_inner
              (T := (X ∘ₗ (A ⊗ₗ (LinearMap.id : Operator K))))
              (b := bH.tensorProduct bK)).symm
    _ = trace ((A ⊗ₗ (LinearMap.id : Operator K)) ∘ₗ X) := by
          simpa [Module.End.mul_eq_comp] using
            (LinearMap.trace_mul_comm ℂ X (A ⊗ₗ (LinearMap.id : Operator K)))

/-- Positivity is preserved by left partial trace. -/
theorem IsPSD.partialTraceLeft {H K : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    [FiniteDimensional ℂ H]
    {X : Operator (H ⊗[ℂ] K)}
    (hX : IsPSD X) :
    IsPSD (Quantum.partialTraceLeft (H := H) (K := K) X) := by
  intro ψ
  let b := stdOrthonormalBasis ℂ H
  have hterm :
      ∀ i : Fin (Module.finrank ℂ H),
        0 ≤ Complex.re
          ⟪ψ,
            ((contractLeft (H := H) (K := K) (b i)) ∘ₗ X ∘ₗ
              (tensorLeft (H := H) (K := K) (b i))) ψ⟫_ℂ := by
    intro i
    simpa [LinearMap.comp_apply, inner_contractLeft_eq_inner_tensorLeft]
      using hX ((tensorLeft (H := H) (K := K) (b i)) ψ)
  rw [Quantum.partialTraceLeft]
  simp only [LinearMap.coe_sum, LinearMap.coe_comp, Finset.sum_apply, Function.comp_apply,
    inner_sum, Complex.re_sum, ge_iff_le]
  exact Finset.sum_nonneg (fun i _ => hterm i)

/-- Hermiticity is preserved by left partial trace. -/
theorem IsHermitian.partialTraceLeft {H K : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    [FiniteDimensional ℂ H]
    {X : Operator (H ⊗[ℂ] K)}
    (hX : IsHermitian X) :
    IsHermitian (Quantum.partialTraceLeft (H := H) (K := K) X) := by
  intro φ ψ
  let b := stdOrthonormalBasis ℂ H
  calc
    ⟪(Quantum.partialTraceLeft (H := H) (K := K) X) φ, ψ⟫_ℂ
        = ∑ i : Fin (Module.finrank ℂ H),
            ⟪((contractLeft (H := H) (K := K) (b i)) ∘ₗ X ∘ₗ
                (tensorLeft (H := H) (K := K) (b i))) φ, ψ⟫_ℂ := by
            simp [Quantum.partialTraceLeft, b, sum_inner]
    _ = ∑ i : Fin (Module.finrank ℂ H),
          ⟪X ((tensorLeft (H := H) (K := K) (b i)) φ),
            (tensorLeft (H := H) (K := K) (b i)) ψ⟫_ℂ := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [LinearMap.comp_apply, inner_contractLeft_left_eq_inner_tensorLeft]
    _ = ∑ i : Fin (Module.finrank ℂ H),
          ⟪(tensorLeft (H := H) (K := K) (b i)) φ,
            X ((tensorLeft (H := H) (K := K) (b i)) ψ)⟫_ℂ := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa [IsHermitian] using (hX ((tensorLeft (H := H) (K := K) (b i)) φ)
            ((tensorLeft (H := H) (K := K) (b i)) ψ))
    _ = ∑ i : Fin (Module.finrank ℂ H),
          ⟪φ,
            ((contractLeft (H := H) (K := K) (b i)) ∘ₗ X ∘ₗ
              (tensorLeft (H := H) (K := K) (b i))) ψ⟫_ℂ := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [LinearMap.comp_apply, inner_contractLeft_eq_inner_tensorLeft]
    _ = ⟪φ, (Quantum.partialTraceLeft (H := H) (K := K) X) ψ⟫_ℂ := by
          simp [Quantum.partialTraceLeft, b, inner_sum]

/-- Left partial trace is trace-preserving. -/
@[simp] theorem trace_partialTraceLeft {H K : Type*}
    [CpxFiniteHilbert H] [CpxFiniteHilbert K]
    (X : Operator (H ⊗[ℂ] K)) :
    trace (Quantum.partialTraceLeft (H := H) (K := K) X) = trace X := by
  let bH : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H := stdOrthonormalBasis ℂ H
  let bK : OrthonormalBasis (Fin (Module.finrank ℂ K)) ℂ K := stdOrthonormalBasis ℂ K
  calc
    trace (Quantum.partialTraceLeft (H := H) (K := K) X)
        = ∑ j : Fin (Module.finrank ℂ K),
            ⟪bK j, (Quantum.partialTraceLeft (H := H) (K := K) X) (bK j)⟫_ℂ := by
            simpa [trace, bK] using
              (LinearMap.trace_eq_sum_inner
                (T := Quantum.partialTraceLeft (H := H) (K := K) X) (b := bK))
    _ = ∑ j : Fin (Module.finrank ℂ K),
          ∑ i : Fin (Module.finrank ℂ H),
            ⟪bH i ⊗ₜ[ℂ] bK j, X (bH i ⊗ₜ[ℂ] bK j)⟫_ℂ := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [Quantum.partialTraceLeft, bH, inner_sum,
            inner_contractLeft_eq_inner_tensorLeft, tensorLeft]
    _ = ∑ p : (Fin (Module.finrank ℂ H)) × (Fin (Module.finrank ℂ K)),
          ⟪bH p.1 ⊗ₜ[ℂ] bK p.2, X (bH p.1 ⊗ₜ[ℂ] bK p.2)⟫_ℂ := by
          simpa using
            (Fintype.sum_prod_type_right'
              (f := fun i : Fin (Module.finrank ℂ H) =>
                fun j : Fin (Module.finrank ℂ K) =>
                  ⟪bH i ⊗ₜ[ℂ] bK j, X (bH i ⊗ₜ[ℂ] bK j)⟫_ℂ)).symm
    _ = ∑ p : (Fin (Module.finrank ℂ H)) × (Fin (Module.finrank ℂ K)),
          ⟪(bH.tensorProduct bK) p, X ((bH.tensorProduct bK) p)⟫_ℂ := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rcases p with ⟨i, j⟩
          simp [OrthonormalBasis.tensorProduct_apply]
    _ = trace X := by
          simpa [trace] using
            (LinearMap.trace_eq_sum_inner (T := X) (b := bH.tensorProduct bK)).symm

/--
Trace-pairing identity for left partial trace:
\[
\operatorname{Tr}(A\,\operatorname{Tr}_H(X))
=
\operatorname{Tr}((I_H\otimes A)\,X).
\]
-/
theorem trace_mul_partialTraceLeft
    {H K : Type*}
    [CpxFiniteHilbert H] [CpxFiniteHilbert K]
    (A : Operator K) (X : Operator (H ⊗[ℂ] K)) :
    trace (A ∘ₗ (Quantum.partialTraceLeft (H := H) (K := K) X))
      = trace (((LinearMap.id : Operator H) ⊗ₗ A) ∘ₗ X) := by
  let bH : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H := stdOrthonormalBasis ℂ H
  let bK : OrthonormalBasis (Fin (Module.finrank ℂ K)) ℂ K := stdOrthonormalBasis ℂ K
  calc
    trace (A ∘ₗ (Quantum.partialTraceLeft (H := H) (K := K) X))
        = trace ((Quantum.partialTraceLeft (H := H) (K := K) X) ∘ₗ A) := by
            simpa [Module.End.mul_eq_comp] using
              (LinearMap.trace_mul_comm ℂ A (Quantum.partialTraceLeft (H := H) (K := K) X))
    _ = ∑ j : Fin (Module.finrank ℂ K),
          ⟪bK j, (Quantum.partialTraceLeft (H := H) (K := K) X) (A (bK j))⟫_ℂ := by
          simpa [trace, bK] using
            (LinearMap.trace_eq_sum_inner
              (T := ((Quantum.partialTraceLeft (H := H) (K := K) X) ∘ₗ A)) (b := bK))
    _ = ∑ j : Fin (Module.finrank ℂ K),
          ∑ i : Fin (Module.finrank ℂ H),
            ⟪bH i ⊗ₜ[ℂ] bK j, X (bH i ⊗ₜ[ℂ] A (bK j))⟫_ℂ := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [Quantum.partialTraceLeft, bH, inner_sum,
            inner_contractLeft_eq_inner_tensorLeft, tensorLeft, LinearMap.comp_apply]
    _ = ∑ p : (Fin (Module.finrank ℂ H)) × (Fin (Module.finrank ℂ K)),
          ⟪bH p.1 ⊗ₜ[ℂ] bK p.2, X (bH p.1 ⊗ₜ[ℂ] A (bK p.2))⟫_ℂ := by
          simpa using
            (Fintype.sum_prod_type_right'
              (f := fun i : Fin (Module.finrank ℂ H) =>
                fun j : Fin (Module.finrank ℂ K) =>
                  ⟪bH i ⊗ₜ[ℂ] bK j, X (bH i ⊗ₜ[ℂ] A (bK j))⟫_ℂ)).symm
    _ = ∑ p : (Fin (Module.finrank ℂ H)) × (Fin (Module.finrank ℂ K)),
          ⟪(bH.tensorProduct bK) p,
            (X ∘ₗ ((LinearMap.id : Operator H) ⊗ₗ A)) ((bH.tensorProduct bK) p)⟫_ℂ := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          rcases p with ⟨i, j⟩
          simp [OrthonormalBasis.tensorProduct_apply, LinearMap.comp_apply]
    _ = trace (X ∘ₗ ((LinearMap.id : Operator H) ⊗ₗ A)) := by
          simpa [trace] using
            (LinearMap.trace_eq_sum_inner
              (T := (X ∘ₗ ((LinearMap.id : Operator H) ⊗ₗ A))) (b := bH.tensorProduct bK)).symm
    _ = trace (((LinearMap.id : Operator H) ⊗ₗ A) ∘ₗ X) := by
          simpa [Module.End.mul_eq_comp] using
            (LinearMap.trace_mul_comm ℂ X (((LinearMap.id : Operator H) ⊗ₗ A)))

end PartialTraceToolkit

section BundledPartialTrace

namespace DensityOperator

/-- Bundled right partial trace on density operators. -/
noncomputable def partialTraceRight {H K : Type*}
    [CpxFiniteHilbert H] [CpxFiniteHilbert K]
    (ρ : DensityOperator (H ⊗[ℂ] K)) : DensityOperator H where
  val := Quantum.partialTraceRight (H := H) (K := K) ρ.val
  isPSD := IsPSD.partialTraceRight (H := H) (K := K) ρ.isPSD
  isHermitian := IsHermitian.partialTraceRight (H := H) (K := K) ρ.isHermitian
  trace_one := by
    simp [ρ.trace_one]

/-- Bundled left partial trace on density operators. -/
noncomputable def partialTraceLeft {H K : Type*}
    [CpxFiniteHilbert H] [CpxFiniteHilbert K]
    (ρ : DensityOperator (H ⊗[ℂ] K)) : DensityOperator K where
  val := Quantum.partialTraceLeft (H := H) (K := K) ρ.val
  isPSD := IsPSD.partialTraceLeft (H := H) (K := K) ρ.isPSD
  isHermitian := IsHermitian.partialTraceLeft (H := H) (K := K) ρ.isHermitian
  trace_one := by
    simp [ρ.trace_one]

end DensityOperator

end BundledPartialTrace

section PurificationAndSqrtSetup

/-- `Ψ` is a purification of `ρ` when tracing out the right subsystem of `|Ψ⟩⟨Ψ|`
recovers `ρ`. -/
def IsPurificationOf {H K : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    [FiniteDimensional ℂ K]
    (ρ : Operator H) (Ψ : H ⊗[ℂ] K) : Prop :=
  partialTraceRight (H := H) (K := K) (pureOp Ψ) = ρ

/-- Vectorization of an operator using the standard orthonormal basis. -/
noncomputable def vecOp {H : Type*}
    [CpxFiniteHilbert H]
    (T : Operator H) : H ⊗[ℂ] H :=
  let b := stdOrthonormalBasis ℂ H
  ∑ i : Fin (Module.finrank ℂ H), (T (b i)) ⊗ₜ[ℂ] (b i)

@[simp] theorem partialTraceRight_pureDM_vecOp {H : Type*}
    [CpxFiniteHilbert H]
    (T : Operator H) :
    partialTraceRight (H := H) (K := H) (pureOp (vecOp T))
      = T * (LinearMap.adjoint T) := by
  ext φ
  let b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H := stdOrthonormalBasis ℂ H
  have h_expand :
      (∑ x,
        ⟪∑ i, T (b i) ⊗ₜ[ℂ] b i, φ ⊗ₜ[ℂ] b x⟫_ℂ •
          (∑ x_1, ⟪b x, b x_1⟫_ℂ • T (b x_1)))
      = ∑ x, ⟪T (b x), φ⟫_ℂ • T (b x) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have h1 :
        ⟪∑ i, T (b i) ⊗ₜ[ℂ] b i, φ ⊗ₜ[ℂ] b x⟫_ℂ = ⟪T (b x), φ⟫_ℂ := by
      rw [sum_inner]
      simp [orthonormal_iff_ite.mp b.orthonormal]
    have h2 :
        (∑ x_1, ⟪b x, b x_1⟫_ℂ • T (b x_1)) = T (b x) := by
      simp [orthonormal_iff_ite.mp b.orthonormal]
    simp [h1, h2]
  have h_adj_expand : (LinearMap.adjoint T) φ = ∑ x, ⟪T (b x), φ⟫_ℂ • b x := by
    calc
      (LinearMap.adjoint T) φ = ∑ x, ⟪b x, (LinearMap.adjoint T) φ⟫_ℂ • b x := by
        symm
        exact b.sum_repr' ((LinearMap.adjoint T) φ)
      _ = ∑ x, ⟪T (b x), φ⟫_ℂ • b x := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact congrArg (fun z : ℂ => z • b i)
          (LinearMap.adjoint_inner_right (A := T) (x := b i) (y := φ))
  have h_rhs : T ((LinearMap.adjoint T) φ) = ∑ x, ⟪T (b x), φ⟫_ℂ • T (b x) := by
    rw [h_adj_expand, map_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [map_smul]
  calc
    partialTraceRight (H := H) (K := H) (pureOp (vecOp T)) φ
        = (∑ x,
            ⟪∑ i, T (b i) ⊗ₜ[ℂ] b i, φ ⊗ₜ[ℂ] b x⟫_ℂ •
              (∑ x_1, ⟪b x, b x_1⟫_ℂ • T (b x_1))) := by
            simp [partialTraceRight, pureOp_apply, vecOp, tensorRight, contractRight, b]
    _ = ∑ x, ⟪T (b x), φ⟫_ℂ • T (b x) := h_expand
    _ = T ((LinearMap.adjoint T) φ) := h_rhs.symm
    _ = (T * LinearMap.adjoint T) φ := by rfl

lemma IsPSD.isPositive {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {X : Operator H} (hHerm : IsHermitian X) (hPSD : IsPSD X) :
    X.IsPositive := by
  refine ⟨hHerm, ?_⟩
  intro ψ
  simpa [inner_re_symm] using hPSD ψ

/-- Square root of an operator via continuous functional calculus on endomorphisms. -/
noncomputable def operatorSqrt {H : Type*}
    [CpxFiniteHilbert H] [CompleteSpace H]
    (X : Operator H) : Operator H :=
  let Xc : H →L[ℂ] H :=
    LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := H) (F' := H) X
  (cfcₙ (Real.sqrt) Xc).toLinearMap

end PurificationAndSqrtSetup


section PurificationExistence


/-- Every density operator admits a purification on `H ⊗ H`. -/
theorem exists_purification_on_self {H : Type*}
    [CpxFiniteHilbert H]
    (ρ : DensityOperator H) :
    ∃ Ψ : H ⊗[ℂ] H, IsPurificationOf (ρ : Operator H) Ψ := by
  let ρc : H →L[ℂ] H :=
    LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := H) (F' := H) (ρ : Operator H)
  have hnonneg : (0 : H →L[ℂ] H) ≤ ρc := by
    refine (ContinuousLinearMap.nonneg_iff_isPositive ρc).2 ?_
    exact (LinearMap.isPositive_toContinuousLinearMap_iff (ρ : Operator H)).2
      (IsPSD.isPositive ρ.isHermitian ρ.isPSD)
  obtain ⟨Tc, hTc⟩ := (CStarAlgebra.nonneg_iff_eq_mul_star_self (a := ρc)).1 hnonneg
  have hStar :
      ((star Tc : H →L[ℂ] H) : Operator H) = LinearMap.adjoint ((Tc : Operator H)) := by
    have h := LinearMap.adjoint_toContinuousLinearMap (A := (Tc : Operator H))
    have h' := congrArg (fun S : H →L[ℂ] H => (S : Operator H)) h
    exact h'.symm
  have hTc_lin : (ρ : Operator H) = (Tc : Operator H) * LinearMap.adjoint (Tc : Operator H) := by
    have h' := congrArg (fun S : H →L[ℂ] H => (S : Operator H)) hTc
    simpa [ρc, hStar] using h'
  refine ⟨vecOp (Tc : Operator H), ?_⟩
  rw [IsPurificationOf, partialTraceRight_pureDM_vecOp, ← hTc_lin]

/-- Every density operator admits a purification on some ancilla Hilbert space. -/
theorem exists_purification {H : Type u}
    [CpxFiniteHilbert H]
    (ρ : DensityOperator H) :
    ∃ (K : Type u) (_ : CpxFiniteHilbert K),
      ∃ Ψ : H ⊗[ℂ] K, IsPurificationOf (ρ : Operator H) Ψ := by
  refine ⟨H, inferInstance, ?_⟩
  simpa using exists_purification_on_self (ρ := ρ)

end PurificationExistence


section MeasurementPrimitives

/-- Two-outcome effects (`0 ≤ Λ ≤ I`) in abstract form. -/
def IsEffect {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Λ : Operator H) : Prop :=
  Λ.IsPositive ∧ ((LinearMap.id : Operator H) - Λ).IsPositive

/-- A measurement-isometry primitive for two-outcome projective measurements. -/
noncomputable def measurementIsometry {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P0 P1 : Operator H) :
    H →ₗ[ℂ] (Qubit ⊗[ℂ] H) :=
  {
    toFun := fun ψ => (ket0 ⊗ₜ[ℂ] (P0 ψ)) + (ket1 ⊗ₜ[ℂ] (P1 ψ))
    map_add' := by
      intro ψ φ
      simp [LinearMap.map_add, TensorProduct.tmul_add, add_assoc, add_left_comm]
    map_smul' := by
      intro c ψ
      simp [TensorProduct.smul_tmul', smul_add]
  }

end MeasurementPrimitives


end Quantum
