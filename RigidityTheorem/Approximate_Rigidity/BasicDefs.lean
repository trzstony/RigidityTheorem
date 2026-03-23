import Quantum.Qubit

open scoped TensorProduct ComplexConjugate InnerProductSpace
open Quantum
/-!
Basic definitions and notational scaffolding for the CHSH rigidity library.

This file now keeps CHSH-specific scaffolding and re-exports reusable quantum
operator/register helpers from `Quantum`.
-/

namespace Approximate_Rigidity

-- Shared qubit and helper primitives are provided by `Quantum` and used via `open Quantum`.

section SemiInner
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

noncomputable def semi_inner (M N : H →ₗ[ℂ] H) (ψ : H) : ℂ :=
  ⟪ψ, (M.adjoint ∘ₗ N) ψ⟫_ℂ

noncomputable def semi_norm_sq (M : H →ₗ[ℂ] H) (ψ : H) : ℝ :=
  RCLike.re ⟪ψ, (M.adjoint ∘ₗ M) ψ⟫_ℂ

noncomputable def semi_norm (M : H →ₗ[ℂ] H) (ψ : H) : ℝ :=
  Real.sqrt (semi_norm_sq M ψ)

lemma semi_inner_eq_inner (M N : H →ₗ[ℂ] H) (ψ : H) :
    semi_inner M N ψ = ⟪M ψ, N ψ⟫_ℂ := by
  simp [semi_inner, LinearMap.adjoint_inner_right]

lemma semi_norm_sq_eq_norm_sq (M : H →ₗ[ℂ] H) (ψ : H) :
    semi_norm_sq M ψ = ‖M ψ‖ ^ 2 := by
  calc
    semi_norm_sq M ψ = (⟪M ψ, M ψ⟫_ℂ).re := by
      simp [semi_norm_sq, LinearMap.adjoint_inner_right]
    _ = ‖M ψ‖ ^ 2 := by
      simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (x := M ψ))

omit [FiniteDimensional ℂ H] in
lemma norm_eq_one_of_isometry (U : H →ₗ[ℂ] H) (ψ : H)
    (hψ : ‖ψ‖ = 1) (hU : Isometry U) :
      ‖U ψ‖ = 1 := by
  have hUψ : ‖U ψ‖ = ‖ψ‖ := by
    simpa [dist_eq_norm, LinearMap.map_zero] using (hU.dist_eq ψ 0)
  simpa [hψ] using hUψ

lemma semi_norm_sq_eq_semi_norm_sq (M : H →ₗ[ℂ] H) (ψ : H) :
    semi_norm M ψ ^ 2 = semi_norm_sq M ψ := by
  have hnonneg : 0 ≤ semi_norm_sq M ψ := by
    simp [semi_norm_sq_eq_norm_sq (M := M) (ψ := ψ)]
  simp [semi_norm, Real.sq_sqrt hnonneg]

theorem re_semi_inner_eq_one_sub_semi_norm_sq_div_two
    (U V : H →ₗ[ℂ] H) (ψ : H) (hψ : ‖ψ‖ = 1) (hU : Isometry U) (hV : Isometry V) :
    (semi_inner U V ψ).re = 1 - (semi_norm_sq (U - V) ψ) / 2 := by
  have hU_norm : ‖U ψ‖ = 1 := norm_eq_one_of_isometry (U := U) (ψ := ψ) hψ hU
  have hV_norm : ‖V ψ‖ = 1 := norm_eq_one_of_isometry (U := V) (ψ := ψ) hψ hV
  have hUV_mul : ‖U ψ - V ψ‖ * ‖U ψ - V ψ‖ = semi_norm_sq (U - V) ψ := by
    have hUV_sq : semi_norm_sq (U - V) ψ = ‖U ψ - V ψ‖ ^ 2 := by
      simpa [LinearMap.sub_apply] using (semi_norm_sq_eq_norm_sq (M := U - V) (ψ := ψ))
    simpa [pow_two] using hUV_sq.symm
  simpa [semi_inner_eq_inner, hU_norm, hV_norm, hUV_mul, one_add_one_eq_two, sub_div] using
    (re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two
      (𝕜 := ℂ) (x := U ψ) (y := V ψ))

end SemiInner

section RegisterSwap

variable {H_A H_B : Type*}
variable [NormedAddCommGroup H_A] [NormedAddCommGroup H_B]
variable [InnerProductSpace ℂ H_A] [InnerProductSpace ℂ H_B]

noncomputable def regSwap :
    ((Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B)) →ₗ[ℂ]
      ((Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B)) :=
by
  -- First reassociate so we can access the middle factors.
  let assoc₁ : ((Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B)) →ₗ[ℂ]
      (Qubit ⊗[ℂ] (H_A ⊗[ℂ] (Qubit ⊗[ℂ] H_B))) :=
    (TensorProduct.assoc ℂ Qubit H_A (Qubit ⊗[ℂ] H_B)).toLinearMap
  -- Rearrange `H_A ⊗ (Qubit ⊗ H_B)` into `Qubit ⊗ (H_A ⊗ H_B)`.
  let inner : (H_A ⊗[ℂ] (Qubit ⊗[ℂ] H_B)) →ₗ[ℂ]
      (Qubit ⊗[ℂ] (H_A ⊗[ℂ] H_B)) :=
    (TensorProduct.assoc ℂ Qubit H_A H_B).toLinearMap.comp
      ((TensorProduct.map (TensorProduct.comm ℂ H_A Qubit).toLinearMap
          (LinearMap.id : H_B →ₗ[ℂ] H_B)).comp
        (TensorProduct.assoc ℂ H_A Qubit H_B).symm.toLinearMap)
  -- Tensor the above rearrangement with `id` on the leading `Qubit`.
  let mapMid : (Qubit ⊗[ℂ] (H_A ⊗[ℂ] (Qubit ⊗[ℂ] H_B))) →ₗ[ℂ]
      (Qubit ⊗[ℂ] (Qubit ⊗[ℂ] (H_A ⊗[ℂ] H_B))) :=
    TensorProduct.map (LinearMap.id : Qubit →ₗ[ℂ] Qubit) inner
  -- Finally reassociate to get `(Qubit ⊗ Qubit) ⊗ (H_A ⊗ H_B)`.
  let assoc₂ : (Qubit ⊗[ℂ] (Qubit ⊗[ℂ] (H_A ⊗[ℂ] H_B))) →ₗ[ℂ]
      ((Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B)) :=
    (TensorProduct.assoc ℂ Qubit Qubit (H_A ⊗[ℂ] H_B)).symm.toLinearMap
  exact assoc₂.comp (mapMid.comp assoc₁)

lemma regSwap_norm (ψ : (Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B)) :
    ‖regSwap ψ‖ = ‖ψ‖ := by
  -- `regSwap` is a composition of associators/commutators, hence an isometry.
  let innerᵢ :
      (H_A ⊗[ℂ] (Qubit ⊗[ℂ] H_B)) →ₗᵢ[ℂ]
        (Qubit ⊗[ℂ] (H_A ⊗[ℂ] H_B)) :=
    (TensorProduct.assocIsometry ℂ Qubit H_A H_B).toLinearIsometry.comp
      ((TensorProduct.mapIsometry (TensorProduct.commIsometry ℂ H_A Qubit).toLinearIsometry
            (.id : H_B →ₗᵢ[ℂ] H_B)).comp
        (TensorProduct.assocIsometry ℂ H_A Qubit H_B).symm.toLinearIsometry)
  let regSwapᵢ :
      ((Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B)) →ₗᵢ[ℂ]
        ((Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B)) :=
    (TensorProduct.assocIsometry ℂ Qubit Qubit (H_A ⊗[ℂ] H_B)).symm.toLinearIsometry.comp
      ((TensorProduct.mapIsometry (.id : Qubit →ₗᵢ[ℂ] Qubit) innerᵢ).comp
        (TensorProduct.assocIsometry ℂ Qubit H_A (Qubit ⊗[ℂ] H_B)).toLinearIsometry)
  have hreg : regSwapᵢ.toLinearMap = (regSwap (H_A := H_A) (H_B := H_B)) := by
    ext x
    simp [regSwap, regSwapᵢ, innerᵢ]
  calc
    ‖regSwap ψ‖ = ‖regSwapᵢ ψ‖ := by
      have happ : regSwapᵢ ψ = regSwap ψ := by
        simpa using congrArg (fun f => f ψ) hreg
      simpa using (congrArg (fun v => ‖v‖) happ).symm
    _ = ‖ψ‖ := regSwapᵢ.norm_map ψ

lemma regSwap_norm_eq_one (ψ : (Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B)) (hψ : ‖ψ‖ = 1) :
    ‖regSwap ψ‖ = 1 := by
  rw [regSwap_norm (ψ := ψ), hψ]

lemma regSwap_map_norm_eq_one
    (V_A : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) (V_B : H_B →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))
    (hVA : Isometry V_A) (hVB : Isometry V_B) (ψ : H_A ⊗[ℂ] H_B) (hψ : ‖ψ‖ = 1) :
    ‖regSwap (H_A := H_A) (H_B := H_B) ((TensorProduct.map V_A V_B) ψ)‖ = 1 := by
  -- `V_A` and `V_B` preserve norms, hence so does their tensor product.
  -- Then apply `regSwap_norm_eq_one`.
  let VAᵢ : H_A →ₗᵢ[ℂ] (Qubit ⊗[ℂ] H_A) :=
    { toLinearMap := V_A
      norm_map' := (AddMonoidHomClass.isometry_iff_norm V_A).1 hVA }
  let VBᵢ : H_B →ₗᵢ[ℂ] (Qubit ⊗[ℂ] H_B) :=
    { toLinearMap := V_B
      norm_map' := (AddMonoidHomClass.isometry_iff_norm V_B).1 hVB }
  have hψ' : ‖(TensorProduct.map V_A V_B) ψ‖ = 1 := by
    calc
      ‖(TensorProduct.map V_A V_B) ψ‖ = ‖ψ‖ := by
        simpa [VAᵢ, VBᵢ] using
          (TensorProduct.norm_map (𝕜 := ℂ) (f := VAᵢ) (g := VBᵢ) (x := ψ))
      _ = 1 := hψ
  simpa using
    (regSwap_norm_eq_one (H_A := H_A) (H_B := H_B)
      (ψ := (TensorProduct.map V_A V_B) ψ) hψ')

lemma regSwap_inner (u v : (Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B)) :
    ⟪regSwap (H_A := H_A) (H_B := H_B) u,
        regSwap (H_A := H_A) (H_B := H_B) v⟫_ℂ = ⟪u, v⟫_ℂ := by
  -- `regSwap` is (definitionally) a composition of associators/commutators,
  -- hence a linear isometry.
  classical
  -- Avoid explicit type annotations here: nested tensor-product norm/inner instances can be
  -- difficult for typeclass search, but these are already determined by the constructors used.
  let assoc₁ᵢ :=
    (TensorProduct.assocIsometry ℂ Qubit H_A (Qubit ⊗[ℂ] H_B)).toLinearIsometry
  let innerᵢ :=
    (TensorProduct.assocIsometry ℂ Qubit H_A H_B).toLinearIsometry.comp
      ((TensorProduct.mapIsometry (TensorProduct.commIsometry ℂ H_A Qubit).toLinearIsometry
            (.id : H_B →ₗᵢ[ℂ] H_B)).comp
        (TensorProduct.assocIsometry ℂ H_A Qubit H_B).symm.toLinearIsometry)
  let mapMidᵢ :=
    TensorProduct.mapIsometry (.id : Qubit →ₗᵢ[ℂ] Qubit) innerᵢ
  let assoc₂ᵢ :=
    (TensorProduct.assocIsometry ℂ Qubit Qubit (H_A ⊗[ℂ] H_B)).symm.toLinearIsometry
  let regSwapᵢ :=
    assoc₂ᵢ.comp (mapMidᵢ.comp assoc₁ᵢ)
  have hreg : regSwapᵢ.toLinearMap = (regSwap (H_A := H_A) (H_B := H_B)) := by
    ext x
    simp [regSwap, regSwapᵢ, assoc₁ᵢ, mapMidᵢ, assoc₂ᵢ, innerᵢ]
  -- Prove inner-product preservation by peeling off the constituent isometries.
  have hregInner : ⟪regSwapᵢ u, regSwapᵢ v⟫_ℂ = ⟪u, v⟫_ℂ := by
    calc
      ⟪regSwapᵢ u, regSwapᵢ v⟫_ℂ
          = ⟪assoc₂ᵢ (mapMidᵢ (assoc₁ᵢ u)), assoc₂ᵢ (mapMidᵢ (assoc₁ᵢ v))⟫_ℂ := by
              simp [regSwapᵢ]
      _ = ⟪mapMidᵢ (assoc₁ᵢ u), mapMidᵢ (assoc₁ᵢ v)⟫_ℂ := by
              exact
                assoc₂ᵢ.inner_map_map (mapMidᵢ (assoc₁ᵢ u)) (mapMidᵢ (assoc₁ᵢ v))
      _ = ⟪assoc₁ᵢ u, assoc₁ᵢ v⟫_ℂ := by
              exact mapMidᵢ.inner_map_map (assoc₁ᵢ u) (assoc₁ᵢ v)
      _ = ⟪u, v⟫_ℂ := by
              exact assoc₁ᵢ.inner_map_map u v
  -- Rewrite `regSwap` via `hreg`.
  have hu : regSwap (H_A := H_A) (H_B := H_B) u = regSwapᵢ u := by
    simpa using congrArg (fun f => f u) hreg.symm
  have hv : regSwap (H_A := H_A) (H_B := H_B) v = regSwapᵢ v := by
    simpa using congrArg (fun f => f v) hreg.symm
  -- Avoid `simp` here: it can rewrite `⟪regSwapᵢ u, regSwapᵢ v⟫` further via
  -- `LinearIsometry.inner_map_map`, making the goal and the provided proof simplify differently.
  rw [hu, hv]
  exact hregInner

end RegisterSwap

section BinaryObservables

/-- Binary observable = self-adjoint involution. -/
class IsBinaryObservable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ[ℂ] H) : Prop where
  symm : A.IsSymmetric
  sq_one : A ∘ₗ A = LinearMap.id

lemma isometry_of_isBinaryObservable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ[ℂ] H) [hA : IsBinaryObservable A] : Isometry A := by
  classical
  refine (AddMonoidHomClass.isometry_iff_norm A).2 ?_
  intro x
  have hAAx : A (A x) = x := by
    simpa [LinearMap.comp_apply] using congrArg (fun f => f x) (IsBinaryObservable.sq_one (A := A))
  have hinner : ⟪A x, A x⟫_ℂ = ⟪x, x⟫_ℂ := by
    -- `⟪A x, A x⟫ = ⟪x, A (A x)⟫ = ⟪x,x⟫`.
    simpa [hAAx] using (IsBinaryObservable.symm (A := A) x (A x))
  -- Convert inner-product equality to a norm equality.
  -- `‖x‖ = √(re ⟪x,x⟫)` holds in any (complex) inner product space.
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (x := A x), norm_eq_sqrt_re_inner (𝕜 := ℂ) (x := x)]
  exact congrArg Real.sqrt (congrArg Complex.re hinner)

end BinaryObservables

section IsometryHelpers

variable {E F G K : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [NormedAddCommGroup G] [NormedAddCommGroup K]
variable [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
variable [InnerProductSpace ℂ G] [InnerProductSpace ℂ K]

/-- Package a linear-map isometry as a `LinearIsometry`. -/
noncomputable def linearIsometryOfIsometry
    (f : E →ₗ[ℂ] F) (hf : Isometry f) : E →ₗᵢ[ℂ] F :=
  { toLinearMap := f
    norm_map' := (AddMonoidHomClass.isometry_iff_norm f).1 hf }

@[simp] lemma linearIsometryOfIsometry_toLinearMap
    (f : E →ₗ[ℂ] F) (hf : Isometry f) :
    (linearIsometryOfIsometry (f := f) hf).toLinearMap = f := rfl

lemma linearMap_id_isometry : Isometry (LinearMap.id : E →ₗ[ℂ] E) := by
  simpa using (LinearIsometry.id : E →ₗᵢ[ℂ] E).isometry

lemma tensor_map_norm_eq
    (f : E →ₗ[ℂ] F) (g : G →ₗ[ℂ] K)
    (hf : Isometry f) (hg : Isometry g) (x : E ⊗[ℂ] G) :
    ‖TensorProduct.map f g x‖ = ‖x‖ := by
  let fᵢ : E →ₗᵢ[ℂ] F := linearIsometryOfIsometry (f := f) hf
  let gᵢ : G →ₗᵢ[ℂ] K := linearIsometryOfIsometry (f := g) hg
  simpa [fᵢ, gᵢ] using
    (TensorProduct.norm_map (𝕜 := ℂ) (f := fᵢ) (g := gᵢ) (x := x))

lemma tensor_map_inner_map_map_eq
    (f : E →ₗ[ℂ] F) (g : G →ₗ[ℂ] K)
    (hf : Isometry f) (hg : Isometry g) (u v : E ⊗[ℂ] G) :
    ⟪TensorProduct.map f g u, TensorProduct.map f g v⟫_ℂ = ⟪u, v⟫_ℂ := by
  let fᵢ : E →ₗᵢ[ℂ] F := linearIsometryOfIsometry (f := f) hf
  let gᵢ : G →ₗᵢ[ℂ] K := linearIsometryOfIsometry (f := g) hg
  simpa [fᵢ, gᵢ] using
    (TensorProduct.inner_map_map (𝕜 := ℂ) fᵢ gᵢ u v)

lemma tensor_map_isometry
    (f : E →ₗ[ℂ] F) (g : G →ₗ[ℂ] K)
    (hf : Isometry f) (hg : Isometry g) :
    Isometry (TensorProduct.map f g) := by
  refine (AddMonoidHomClass.isometry_iff_norm (TensorProduct.map f g)).2 ?_
  intro x
  simpa using tensor_map_norm_eq (f := f) (g := g) hf hg x

lemma isometry_of_adjoint_eq_self_and_sq_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (A : H →ₗ[ℂ] H) (hAdj : A.adjoint = A) (hSq : A ∘ₗ A = LinearMap.id) :
    Isometry A := by
  classical
  letI : IsBinaryObservable A :=
    { symm := (LinearMap.isSymmetric_iff_isSelfAdjoint (A := A)).2
        ((LinearMap.isSelfAdjoint_iff' (A := A)).2 hAdj)
      sq_one := hSq }
  exact isometry_of_isBinaryObservable (H := H) (A := A)

end IsometryHelpers

/-! ## CHSH strategy scaffolding -/

structure CHSHStrategy (H_A H_B : Type*)
    [NormedAddCommGroup H_A] [NormedAddCommGroup H_B]
    [InnerProductSpace ℂ H_A] [InnerProductSpace ℂ H_B] where
  psi : H_A ⊗[ℂ] H_B
  psi_norm : ‖psi‖ = 1
  A0 : H_A →ₗ[ℂ] H_A
  A1 : H_A →ₗ[ℂ] H_A
  B0 : H_B →ₗ[ℂ] H_B
  B1 : H_B →ₗ[ℂ] H_B
  A0_bin : IsBinaryObservable A0
  A1_bin : IsBinaryObservable A1
  B0_bin : IsBinaryObservable B0
  B1_bin : IsBinaryObservable B1

attribute [instance] CHSHStrategy.A0_bin CHSHStrategy.A1_bin CHSHStrategy.B0_bin CHSHStrategy.B1_bin

section CHSHOp
variable {H_A H_B : Type*}
variable [AddCommGroup H_A] [AddCommGroup H_B]
variable [Module ℂ H_A] [Module ℂ H_B]
variable (A0 A1 : H_A →ₗ[ℂ] H_A) (B0 B1 : H_B →ₗ[ℂ] H_B)

/-- General CHSH operator. -/
def CHSH_op : H_A ⊗[ℂ] H_B →ₗ[ℂ] H_A ⊗[ℂ] H_B :=
  (A0 ⊗ₗ B0) + (A0 ⊗ₗ B1) + (A1 ⊗ₗ B0) - (A1 ⊗ₗ B1)
end CHSHOp

noncomputable def chshBias {H_A H_B : Type*}
    [NormedAddCommGroup H_A] [NormedAddCommGroup H_B]
    [InnerProductSpace ℂ H_A] [InnerProductSpace ℂ H_B] (S : CHSHStrategy H_A H_B) : Real :=
  Complex.re ⟪S.psi, (CHSH_op (H_A := H_A) (H_B := H_B) S.A0 S.A1 S.B0 S.B1) S.psi⟫_ℂ

end Approximate_Rigidity
