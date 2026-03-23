import Entropy_Bound.Infra
import Quantum.Bell

open scoped TensorProduct InnerProductSpace
open Quantum

namespace Entropy_Bound

/-- The two-qubit `AB` system used in the CHSH setup. -/
abbrev ABSystem : Type := Qubit ⊗[ℂ] Qubit

/-- The tripartite `ABE` system with qubit registers `A,B` and arbitrary `E`. -/
abbrev ABESystem (E : Type) [CpxFiniteHilbert E] : Type := ABSystem ⊗[ℂ] E

/-- Probability distribution on a finite alphabet `X`. -/
structure ProbDist (X : Type*) [Fintype X] where
  prob : X → Real
  nonneg : ∀ x, 0 ≤ prob x
  sum_eq_one : (∑ x : X, prob x) = 1

/--
Classical-quantum state
`ρ_XA = ∑_x p(x) |x⟩⟨x| ⊗ ρ_x`,
where `p` is a probability distribution on `X` and each `ρ_x` is a density operator on `A`.
-/
noncomputable def cqState
    {X A : Type*} [Fintype X] [CpxFiniteHilbert A]
    (p : ProbDist X) (ρ : X → DensityOperator A) :
    Operator ((EuclideanSpace ℂ X) ⊗[ℂ] A) :=
  ∑ x : X, (p.prob x : ℂ) •
    ((classicalProjector (X := X) x) ⊗ₗ ((ρ x : DensityOperator A) : Operator A))

/--
Reduced `AB` operator obtained from an operator on `ABE` by tracing out `E`.

This matches the setup definition `ρ_{AB} := Tr_E(ρ_{ABE})`.
-/
noncomputable def ρAB
    {E : Type} [CpxFiniteHilbert E]
    (ρABE : DensityOperator (ABESystem E)) : DensityOperator ABSystem :=
  DensityOperator.partialTraceRight (H := ABSystem) (K := E) ρABE

/--
Alice key-basis projector lifted to `ABE`.

`x = 0` uses `|0⟩⟨0|` and `x = 1` uses `|1⟩⟨1|` on Alice's qubit.
-/
noncomputable def keyProjector
    {E : Type} [CpxFiniteHilbert E]
    (x : Fin 2) : Operator (ABESystem E) :=
  let PX : Qubit →ₗ[ℂ] Qubit := if x = 0 then proj0 else proj1
  let idBE : Operator (Qubit ⊗[ℂ] E) := LinearMap.id
  let assocABEToA_BE : ABESystem E →ₗ[ℂ] (Qubit ⊗[ℂ] (Qubit ⊗[ℂ] E)) :=
    (TensorProduct.assoc ℂ Qubit Qubit E).toLinearMap
  let assocA_BEToABE : (Qubit ⊗[ℂ] (Qubit ⊗[ℂ] E)) →ₗ[ℂ] ABESystem E :=
    (TensorProduct.assoc ℂ Qubit Qubit E).symm.toLinearMap
  assocA_BEToABE ∘ₗ (PX ⊗ₗ idBE) ∘ₗ assocABEToA_BE

/-- `keyProjector x` on a pure tensor: acts as `proj_x` on Alice's qubit. -/
lemma keyProjector_tmul
    {E : Type} [CpxFiniteHilbert E] (x : Fin 2)
    (a b : Qubit) (e : E) :
    keyProjector (E := E) x ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] e) =
      (((if x = 0 then proj0 else proj1) a) ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] e := by
  simp only [keyProjector, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    TensorProduct.assoc_tmul, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
    TensorProduct.assoc_symm_tmul]

/-- `keyProjector x` is idempotent. -/
lemma keyProjector_idem
    {E : Type} [CpxFiniteHilbert E] (x : Fin 2) :
    keyProjector (E := E) x ∘ₗ keyProjector (E := E) x = keyProjector (E := E) x := by
  apply LinearMap.ext
  intro v
  refine TensorProduct.induction_on v ?_ ?_ ?_
  · simp
  · intro ab e
    refine TensorProduct.induction_on ab ?_ ?_ ?_
    · simp
    · intro a b
      simp only [LinearMap.comp_apply, keyProjector_tmul]
      have hkey : ∀ q : Qubit,
          (if x = 0 then proj0 else proj1) ((if x = 0 then proj0 else proj1) q) =
          (if x = 0 then proj0 else proj1) q := by
        intro q
        fin_cases x
        · exact LinearMap.congr_fun proj0_idem q
        · exact LinearMap.congr_fun proj1_idem q
      simp only [hkey]
    · intro v₁ v₂ h₁ h₂
      simp only [LinearMap.comp_apply] at h₁ h₂ ⊢
      simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
  · intro v₁ v₂ h₁ h₂
    simp only [map_add, h₁, h₂]

/-- `∑_x keyProjector x = id`. -/
lemma keyProjector_sum
    {E : Type} [CpxFiniteHilbert E] :
    ∑ x : Fin 2, keyProjector (E := E) x = LinearMap.id := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.id_apply]
  refine TensorProduct.induction_on v ?_ ?_ ?_
  · simp
  · intro ab e
    refine TensorProduct.induction_on ab ?_ ?_ ?_
    · simp
    · intro a b
      have h01 : (1 : Fin 2) ≠ 0 := Fin.zero_ne_one.symm
      simp only [Fin.sum_univ_two, LinearMap.add_apply, keyProjector_tmul, if_true, if_neg h01]
      have hsum : proj0 a + proj1 a = a := by
        have := LinearMap.congr_fun proj_sum a
        simp only [LinearMap.add_apply, LinearMap.id_apply] at this
        exact this
      rw [← TensorProduct.add_tmul, ← TensorProduct.add_tmul, hsum]
    · intro v₁ v₂ h₁ h₂
      simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
  · intro v₁ v₂ h₁ h₂
    simp only [map_add, h₁, h₂]

/-- `keyProjector x` is self-adjoint. -/
lemma keyProjector_sa
    {E : Type} [CpxFiniteHilbert E] (x : Fin 2) :
    LinearMap.adjoint (keyProjector (E := E) x) = keyProjector (E := E) x := by
  apply LinearMap.ext
  intro v
  apply ext_inner_right ℂ
  intro w
  rw [LinearMap.adjoint_inner_left]
  refine TensorProduct.induction_on v ?_ ?_ ?_
  · simp
  · intro ab e
    refine TensorProduct.induction_on ab ?_ ?_ ?_
    · simp
    · intro a b
      refine TensorProduct.induction_on w ?_ ?_ ?_
      · simp
      · intro ab' e'
        refine TensorProduct.induction_on ab' ?_ ?_ ?_
        · simp
        · intro a' b'
          simp only [keyProjector_tmul, TensorProduct.inner_tmul]
          split_ifs with hx
          · congr 1; congr 1
            have h := LinearMap.adjoint_inner_left proj0 a' a
            rw [proj0_sa] at h
            exact h.symm
          · congr 1; congr 1
            have h := LinearMap.adjoint_inner_left proj1 a' a
            rw [proj1_sa] at h
            exact h.symm
        · intro v₁ v₂ h₁ h₂
          simp only [TensorProduct.add_tmul, map_add, inner_add_right, h₁, h₂]
      · intro v₁ v₂ h₁ h₂
        simp only [map_add, inner_add_right, h₁, h₂]
    · intro v₁ v₂ h₁ h₂
      simp only [TensorProduct.add_tmul, map_add, inner_add_left, h₁, h₂]
  · intro v₁ v₂ h₁ h₂
    simp only [map_add, inner_add_left, h₁, h₂]

/--
Subnormalized conditional Eve operator `ρ_E^x` obtained by projecting Alice's key outcome `x`
and tracing out both qubits.
-/
noncomputable def rhoECond
    {E : Type} [CpxFiniteHilbert E]
    (ρABE : Operator (ABESystem E)) (x : Fin 2) : Operator E :=
  let PX : Operator (ABESystem E) := keyProjector (E := E) x
  partialTraceLeft (H := ABSystem) (K := E) (PX ∘ₗ ρABE ∘ₗ PX)

/--
Classical-quantum operator `ρ_XE = Σ_x |x⟩⟨x| ⊗ ρ_E^x` induced by Alice's key measurement.

We use the qubit space as the classical two-outcome register `X`.
-/
noncomputable def rhoXE_from_ABE
    {E : Type} [CpxFiniteHilbert E]
    (ρABE : Operator (ABESystem E)) : Operator (Qubit ⊗[ℂ] E) :=
  ∑ x : Fin 2, (classicalProjector (X := Fin 2) x) ⊗ₗ rhoECond (E := E) ρABE x

end Entropy_Bound
