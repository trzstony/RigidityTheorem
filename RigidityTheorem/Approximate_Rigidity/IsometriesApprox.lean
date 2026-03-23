import Approximate_Rigidity.Isometries

import Mathlib.Tactic.NoncommRing

open scoped TensorProduct Pauli InnerProductSpace ComplexConjugate
open Quantum

namespace Approximate_Rigidity

/-!
Approximate extracted-operator relations (Eqs. (218) and (220) in the notes).

These are kept in a separate file because their proofs are comparatively long and
bookkeeping-heavy.
-/

section CHSHSquare

variable {H_A H_B : Type*}
variable [NormedAddCommGroup H_A] [NormedAddCommGroup H_B]
variable [InnerProductSpace ℂ H_A] [InnerProductSpace ℂ H_B]

variable (A0 A1 : H_A →ₗ[ℂ] H_A) (B0 B1 : H_B →ₗ[ℂ] H_B)
variable [IsBinaryObservable A0] [IsBinaryObservable A1]
variable [IsBinaryObservable B0] [IsBinaryObservable B1]


lemma map_neg_left (f : H_A →ₗ[ℂ] H_A) (g : H_B →ₗ[ℂ] H_B) :
      TensorProduct.map (-f) g = -(TensorProduct.map f g) := by
    calc
      TensorProduct.map (-f) g = TensorProduct.map ((-1 : ℂ) • f) g := by
        simp only [neg_smul, one_smul]
      _ = (-1 : ℂ) • TensorProduct.map f g := by
        simpa using (TensorProduct.map_smul_left (r := (-1 : ℂ)) (f := f) (g := g))
      _ = -(TensorProduct.map f g) := by
        exact (neg_one_smul ℂ (TensorProduct.map f g))

lemma map_neg_right (f : H_A →ₗ[ℂ] H_A) (g : H_B →ₗ[ℂ] H_B) :
      TensorProduct.map f (-g) = -(TensorProduct.map f g) := by
    calc
      TensorProduct.map f (-g) = TensorProduct.map f ((-1 : ℂ) • g) := by
        simp only [neg_smul, one_smul]
      _ = (-1 : ℂ) • TensorProduct.map f g := by
        simpa using (TensorProduct.map_smul_right (r := (-1 : ℂ)) (f := f) (g := g))
      _ = -(TensorProduct.map f g) := by
        exact (neg_one_smul ℂ (TensorProduct.map f g))

lemma tensor_mul (f₁ f₂ : H_A →ₗ[ℂ] H_A) (g₁ g₂ : H_B →ₗ[ℂ] H_B) :
      (f₁ ⊗ₗ g₁) * (f₂ ⊗ₗ g₂) = (f₁ * f₂) ⊗ₗ (g₁ * g₂) := by
    simpa using
      (TensorProduct.map_mul (f₁ := f₁) (f₂ := f₂) (g₁ := g₁) (g₂ := g₂)).symm

/-!
CHSH square identity:

If `A0,A1,B0,B1` are binary observables (self-adjoint involutions), then
`(CHSH_op A0 A1 B0 B1)^2 = 4 I - [A0,A1] ⊗ [B0,B1]`.

Here commutators are written using the `Pauli` notation `⟦A,B⟧ = A*B - B*A`, where `*` is
composition of endomorphisms (`Module.End`).
-/
theorem CHSH_op_sq :
    (CHSH_op (H_A := H_A) (H_B := H_B) A0 A1 B0 B1) ^ 2
      =
        (4 : (H_A ⊗[ℂ] H_B →ₗ[ℂ] H_A ⊗[ℂ] H_B)) - (⟦A0, A1⟧ ⊗ₗ ⟦B0, B1⟧) := by
  classical
  have hA0 : A0 * A0 = (1 : H_A →ₗ[ℂ] H_A) := by
    simpa [Module.End.mul_eq_comp, Module.End.one_eq_id] using
      (IsBinaryObservable.sq_one (A := A0))
  have hA1 : A1 * A1 = (1 : H_A →ₗ[ℂ] H_A) := by
    simpa [Module.End.mul_eq_comp, Module.End.one_eq_id] using
      (IsBinaryObservable.sq_one (A := A1))
  have hB0 : B0 * B0 = (1 : H_B →ₗ[ℂ] H_B) := by
    simpa [Module.End.mul_eq_comp, Module.End.one_eq_id] using
      (IsBinaryObservable.sq_one (A := B0))
  have hB1 : B1 * B1 = (1 : H_B →ₗ[ℂ] H_B) := by
    simpa [Module.End.mul_eq_comp, Module.End.one_eq_id] using
      (IsBinaryObservable.sq_one (A := B1))
  set X : (H_A ⊗[ℂ] H_B →ₗ[ℂ] H_A ⊗[ℂ] H_B) := A0 ⊗ₗ (B0 + B1)
  set Y : (H_A ⊗[ℂ] H_B →ₗ[ℂ] H_A ⊗[ℂ] H_B) := A1 ⊗ₗ (B0 - B1)
  have hCHSH :
      CHSH_op (H_A := H_A) (H_B := H_B) A0 A1 B0 B1 = X + Y := by
    subst X Y
    simp [CHSH_op, sub_eq_add_neg, TensorProduct.map_add_right, map_neg_right, add_assoc]
  have hB_cross₁ : (B0 + B1) * (B0 - B1) = -⟦B0, B1⟧ := by
    noncomm_ring [hB0, hB1]
  have hB_cross₂ : (B0 - B1) * (B0 + B1) = ⟦B0, B1⟧ := by
    noncomm_ring [hB0, hB1]
  have hB_sq_sum :
      (B0 + B1) * (B0 + B1) + (B0 - B1) * (B0 - B1) = (4 : (H_B →ₗ[ℂ] H_B)) := by
    noncomm_ring [hB0, hB1]; simp
  have one_tensor_natCast_four :
      ((1 : H_A →ₗ[ℂ] H_A) ⊗ₗ (4 : (H_B →ₗ[ℂ] H_B))) =
        (4 : (H_A ⊗[ℂ] H_B →ₗ[ℂ] H_A ⊗[ℂ] H_B)) := by
    refine TensorProduct.ext' (R := ℂ)
      (g := ((1 : H_A →ₗ[ℂ] H_A) ⊗ₗ (4 : (H_B →ₗ[ℂ] H_B))))
      (h := (4 : (H_A ⊗[ℂ] H_B →ₗ[ℂ] H_A ⊗[ℂ] H_B))) ?_
    intro x y
    simp [TensorProduct.map_tmul, TensorProduct.tmul_smul]
  have hXX :
      X * X = (A0 * A0) ⊗ₗ ((B0 + B1) * (B0 + B1)) := by
    simp [X, tensor_mul]
  have hYY :
      Y * Y = (A1 * A1) ⊗ₗ ((B0 - B1) * (B0 - B1)) := by
    simp [Y, tensor_mul]
  have hXY :
      X * Y = (A0 * A1) ⊗ₗ ((B0 + B1) * (B0 - B1)) := by
    simp [X, Y, tensor_mul]
  have hYX :
      Y * X = (A1 * A0) ⊗ₗ ((B0 - B1) * (B0 + B1)) := by
    simp [X, Y, tensor_mul]
  have hSq : X * X + Y * Y = (4 : (H_A ⊗[ℂ] H_B →ₗ[ℂ] H_A ⊗[ℂ] H_B)) := by
    calc
      X * X + Y * Y
          = ((A0 * A0) ⊗ₗ ((B0 + B1) * (B0 + B1))) +
              ((A1 * A1) ⊗ₗ ((B0 - B1) * (B0 - B1))) := by
              simp [hXX, hYY]
      _ = ((1 : H_A →ₗ[ℂ] H_A) ⊗ₗ ((B0 + B1) * (B0 + B1))) +
            ((1 : H_A →ₗ[ℂ] H_A) ⊗ₗ ((B0 - B1) * (B0 - B1))) := by
              simp [hA0, hA1]
      _ = (1 : H_A →ₗ[ℂ] H_A) ⊗ₗ
            (((B0 + B1) * (B0 + B1)) + ((B0 - B1) * (B0 - B1))) := by
              simpa using
                (TensorProduct.map_add_right (f := (1 : H_A →ₗ[ℂ] H_A))
                  (g₁ := ((B0 + B1) * (B0 + B1)))
                  (g₂ := ((B0 - B1) * (B0 - B1)))).symm
      _ = (1 : H_A →ₗ[ℂ] H_A) ⊗ₗ (4 : (H_B →ₗ[ℂ] H_B)) := by
              simp [hB_sq_sum]
      _ = (4 : (H_A ⊗[ℂ] H_B →ₗ[ℂ] H_A ⊗[ℂ] H_B)) := by
              simpa using one_tensor_natCast_four
  have hCross : X * Y + Y * X = -(⟦A0, A1⟧ ⊗ₗ ⟦B0, B1⟧) := by
    set C : (H_B →ₗ[ℂ] H_B) := ⟦B0, B1⟧
    have hA_comm : (A1 * A0 - A0 * A1) = -⟦A0, A1⟧ := by
      noncomm_ring
    calc
      X * Y + Y * X
          = ((A0 * A1) ⊗ₗ ((B0 + B1) * (B0 - B1))) +
              ((A1 * A0) ⊗ₗ ((B0 - B1) * (B0 + B1))) := by
              simp [hXY, hYX]
      _ = ((A0 * A1) ⊗ₗ (-C)) + ((A1 * A0) ⊗ₗ C) := by
              simp [C, hB_cross₁, hB_cross₂]
      _ = (-((A0 * A1) ⊗ₗ C)) + ((A1 * A0) ⊗ₗ C) := by
              simp [map_neg_right]
      _ = ((A1 * A0) ⊗ₗ C) + (-((A0 * A1) ⊗ₗ C)) := by
              abel
      _ = ((A1 * A0) ⊗ₗ C) + ((-(A0 * A1)) ⊗ₗ C) := by
              have hneg : -((A0 * A1) ⊗ₗ C) = ((-(A0 * A1)) ⊗ₗ C) := by
                simpa using (map_neg_left (f := (A0 * A1)) (g := C)).symm
              simp [hneg]
      _ = (A1 * A0 + (-(A0 * A1))) ⊗ₗ C := by
              simpa using
                (TensorProduct.map_add_left (g := C)
                  (f₁ := (A1 * A0)) (f₂ := (-(A0 * A1)))).symm
      _ = (A1 * A0 - A0 * A1) ⊗ₗ C := by
              simp [sub_eq_add_neg]
      _ = (-⟦A0, A1⟧) ⊗ₗ C := by
              exact congrArg (fun t => (t ⊗ₗ C)) hA_comm
      _ = -(⟦A0, A1⟧ ⊗ₗ C) := by
              simpa using (map_neg_left (f := ⟦A0, A1⟧) (g := C))
      _ = -(⟦A0, A1⟧ ⊗ₗ ⟦B0, B1⟧) := by
              simp [C]
  calc
    (CHSH_op (H_A := H_A) (H_B := H_B) A0 A1 B0 B1) ^ 2
        = (X + Y) ^ 2 := by simp [hCHSH]
    _ = X * X + X * Y + (Y * X + Y * Y) := by
          simp [pow_two, mul_add, add_mul, add_assoc, add_left_comm]
    _ = (X * X + Y * Y) + (X * Y + Y * X) := by
          abel
    _ = (4 : (H_A ⊗[ℂ] H_B →ₗ[ℂ] H_A ⊗[ℂ] H_B)) + (-(⟦A0, A1⟧ ⊗ₗ ⟦B0, B1⟧)) := by
          simp [hSq, hCross]
    _ = (4 : (H_A ⊗[ℂ] H_B →ₗ[ℂ] H_A ⊗[ℂ] H_B)) - (⟦A0, A1⟧ ⊗ₗ ⟦B0, B1⟧) := by
          simp [sub_eq_add_neg]

end CHSHSquare


noncomputable def cConst : Real := 128 * Real.sqrt 2

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

private lemma comm_map_map
    (A : H_A →ₗ[ℂ] H_A) (B : H_B →ₗ[ℂ] H_B) :
    ((B ⊗ₗ A) ∘ₗ (TensorProduct.comm ℂ H_A H_B).toLinearMap)
      =
    ((TensorProduct.comm ℂ H_A H_B).toLinearMap ∘ₗ (A ⊗ₗ B)) := by
  ext x y
  simp [LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.comm_tmul]

private lemma inner_comm_eq
    (x y : H_A ⊗[ℂ] H_B) :
    ⟪(TensorProduct.comm ℂ H_A H_B) x, (TensorProduct.comm ℂ H_A H_B) y⟫_ℂ
      = ⟪x, y⟫_ℂ := by
  let commLI : (H_A ⊗[ℂ] H_B) →ₗᵢ[ℂ] (H_B ⊗[ℂ] H_A) :=
    { toLinearMap := (TensorProduct.comm ℂ H_A H_B).toLinearMap
      norm_map' := TensorProduct.norm_comm }
  simpa [commLI] using (LinearIsometry.inner_map_map commLI x y)

private lemma term_swap
    (S : CHSHStrategy H_A H_B)
    (A : H_A →ₗ[ℂ] H_A) (B : H_B →ₗ[ℂ] H_B) :
    ⟪(TensorProduct.comm ℂ H_A H_B) S.psi,
        (B ⊗ₗ A) ((TensorProduct.comm ℂ H_A H_B) S.psi)⟫_ℂ
      =
    ⟪S.psi, (A ⊗ₗ B) S.psi⟫_ℂ := by
  have hmap := congrArg (fun F => F S.psi) (comm_map_map (A := A) (B := B))
  calc
    ⟪(TensorProduct.comm ℂ H_A H_B) S.psi,
        (B ⊗ₗ A) ((TensorProduct.comm ℂ H_A H_B) S.psi)⟫_ℂ
        =
      ⟪(TensorProduct.comm ℂ H_A H_B) S.psi,
          (TensorProduct.comm ℂ H_A H_B) ((A ⊗ₗ B) S.psi)⟫_ℂ := by
            simpa [LinearMap.comp_apply] using
              congrArg (fun z => ⟪(TensorProduct.comm ℂ H_A H_B) S.psi, z⟫_ℂ) hmap
    _ = ⟪S.psi, (A ⊗ₗ B) S.psi⟫_ℂ := by
          simpa using inner_comm_eq (x := S.psi) (y := ((A ⊗ₗ B) S.psi))

private noncomputable def swapStrategy (S : CHSHStrategy H_A H_B) : CHSHStrategy H_B H_A where
  psi := (TensorProduct.comm ℂ H_A H_B) S.psi
  psi_norm := by simpa [TensorProduct.norm_comm (x := S.psi)] using S.psi_norm
  A0 := S.B0
  A1 := S.B1
  B0 := S.A0
  B1 := S.A1
  A0_bin := S.B0_bin
  A1_bin := S.B1_bin
  B0_bin := S.A0_bin
  B1_bin := S.A1_bin

private lemma chsh_commute_map (S : CHSHStrategy H_A H_B) :
    ((CHSH_op (H_A := H_B) (H_B := H_A) S.B0 S.B1 S.A0 S.A1) ∘ₗ
        (TensorProduct.comm ℂ H_A H_B).toLinearMap)
      =
    ((TensorProduct.comm ℂ H_A H_B).toLinearMap ∘ₗ
      (CHSH_op (H_A := H_A) (H_B := H_B) S.A0 S.A1 S.B0 S.B1)) := by
  ext x y
  simp [CHSH_op, LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.comm_tmul,
    sub_eq_add_neg, add_assoc, add_left_comm]

private lemma chshBias_swap (S : CHSHStrategy H_A H_B) :
    chshBias (swapStrategy (H_A := H_A) (H_B := H_B) S) = chshBias S := by
  let c : (H_A ⊗[ℂ] H_B) →ₗ[ℂ] (H_B ⊗[ℂ] H_A) := (TensorProduct.comm ℂ H_A H_B).toLinearMap
  have hmap := congrArg (fun F => F S.psi) (chsh_commute_map (S := S))
  calc
    chshBias (swapStrategy (H_A := H_A) (H_B := H_B) S)
        =
      (⟪c S.psi,
          (CHSH_op (H_A := H_B) (H_B := H_A) S.B0 S.B1 S.A0 S.A1) (c S.psi)⟫_ℂ).re := by
          simp [chshBias, swapStrategy, c]
    _ =
      (⟪c S.psi, c ((CHSH_op (H_A := H_A) (H_B := H_B) S.A0 S.A1 S.B0 S.B1) S.psi)⟫_ℂ).re := by
          simpa [c, LinearMap.comp_apply] using
            congrArg (fun z => (⟪c S.psi, z⟫_ℂ).re) hmap
    _ =
      (⟪S.psi, (CHSH_op (H_A := H_A) (H_B := H_B) S.A0 S.A1 S.B0 S.B1) S.psi⟫_ℂ).re := by
          exact congrArg Complex.re
            (inner_comm_eq (x := S.psi)
              (y := ((CHSH_op (H_A := H_A) (H_B := H_B) S.A0 S.A1 S.B0 S.B1) S.psi)))
    _ = chshBias S := by
          simp [chshBias]

private lemma adjoint_mul_tensor_id_eq_sq
    (C : H_A →ₗ[ℂ] H_A) (hC_adj : C.adjoint = C) :
    ((C ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)).adjoint ∘ₗ
      (C ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)))
      =
    (C ^ 2) ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B) := by
  let idB : H_B →ₗ[ℂ] H_B := LinearMap.id
  calc
    ((C ⊗ₗ idB).adjoint ∘ₗ (C ⊗ₗ idB))
        = ((C.adjoint ⊗ₗ idB.adjoint) ∘ₗ (C ⊗ₗ idB)) := by simp
    _ = ((C.adjoint ∘ₗ C) ⊗ₗ (idB.adjoint ∘ₗ idB)) := by
          simpa using (TensorProduct.map_comp (C.adjoint) idB.adjoint C idB).symm
    _ = ((C ∘ₗ C) ⊗ₗ idB) := by simp [hC_adj, idB]
    _ = ((C * C) ⊗ₗ idB) := rfl
    _ = (C ^ 2) ⊗ₗ idB := by simp [pow_two]

private lemma inner_sq_tensor_id_eq_norm_sq
    (C : H_A →ₗ[ℂ] H_A) (ψ : H_A ⊗[ℂ] H_B) (hC_adj : C.adjoint = C) :
    (⟪ψ, (((C ^ 2) ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψ)⟫_ℂ).re
      =
    ‖((C ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψ)‖ ^ 2 := by
  let idB : H_B →ₗ[ℂ] H_B := LinearMap.id
  calc
    (⟪ψ, (((C ^ 2) ⊗ₗ idB) ψ)⟫_ℂ).re
        = (⟪ψ, (((C ⊗ₗ idB).adjoint ∘ₗ (C ⊗ₗ idB)) ψ)⟫_ℂ).re := by
            rw [← adjoint_mul_tensor_id_eq_sq (H_A := H_A) (H_B := H_B) (C := C) hC_adj]
    _ = semi_norm_sq (H := H_A ⊗[ℂ] H_B) (C ⊗ₗ idB) ψ := by
          simp [semi_norm_sq]
    _ = ‖((C ⊗ₗ idB) ψ)‖ ^ 2 := by
          simpa using
            (semi_norm_sq_eq_norm_sq (H := H_A ⊗[ℂ] H_B) (M := C ⊗ₗ idB) (ψ := ψ))

private lemma adjoint_eq_of_symm
    (A : H_A →ₗ[ℂ] H_A) (hA_symm : A.IsSymmetric) :
    A.adjoint = A := by
  exact
    (LinearMap.isSelfAdjoint_iff' (A := A)).1
      ((LinearMap.isSymmetric_iff_isSelfAdjoint (A := A)).1 hA_symm)

private lemma anticommutator_inner_sq_eq_norm_sq
    (A0 A1 : H_A →ₗ[ℂ] H_A) (ψ : H_A ⊗[ℂ] H_B)
    (hA0_adj : A0.adjoint = A0) (hA1_adj : A1.adjoint = A1) :
    (⟪ψ, ((((A1 ∘ₗ A0 + A0 ∘ₗ A1) ^ 2) ⊗ₗ
      (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψ)⟫_ℂ).re
      =
    ‖((((A1 ∘ₗ A0 + A0 ∘ₗ A1) ⊗ₗ
      (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψ))‖ ^ 2 := by
  let C : H_A →ₗ[ℂ] H_A := (A1 ∘ₗ A0) + (A0 ∘ₗ A1)
  have hC_adj : C.adjoint = C := by
    simp [C, hA0_adj, hA1_adj, add_comm]
  simpa [C] using
    (inner_sq_tensor_id_eq_norm_sq
      (H_A := H_A) (H_B := H_B) (C := C) (ψ := ψ) hC_adj)

private lemma tensor_map_sub_left
    (f g : H_A →ₗ[ℂ] H_A) (h : H_B →ₗ[ℂ] H_B) :
    ((f - g) ⊗ₗ h) = (f ⊗ₗ h) - (g ⊗ₗ h) := by
  ext x y
  simp [TensorProduct.map_tmul, sub_eq_add_neg, TensorProduct.add_tmul, TensorProduct.neg_tmul]

private lemma tensor_map_sub_right
    (f : H_A →ₗ[ℂ] H_A) (g h : H_B →ₗ[ℂ] H_B) :
    (f ⊗ₗ (g - h)) = (f ⊗ₗ g) - (f ⊗ₗ h) := by
  ext x y
  simp [TensorProduct.map_tmul, sub_eq_add_neg, TensorProduct.tmul_add, TensorProduct.tmul_neg]

private lemma inner_four_apply_re
    (ψ : H_A ⊗[ℂ] H_B) (hψ : ‖ψ‖ = 1) :
    (⟪ψ, ((4 : (H_A ⊗[ℂ] H_B →ₗ[ℂ] H_A ⊗[ℂ] H_B)) ψ)⟫_ℂ).re = 4 := by
  have h4smulC : (⟪ψ, ((4 : ℂ) • ψ)⟫_ℂ).re = 4 := by
    have hsmul_re :
        (⟪ψ, ((4 : ℂ) • ψ)⟫_ℂ).re
          = (4 : ℝ) * ((((‖ψ‖ ^ 2 : ℝ) : ℂ)).re) := by
      calc
        (⟪ψ, ((4 : ℂ) • ψ)⟫_ℂ).re
            = (((4 : ℂ) * (((‖ψ‖ ^ 2 : ℝ) : ℂ))).re) := by
                simpa using congrArg Complex.re
                  (inner_smul_right (𝕜 := ℂ) ψ ψ (4 : ℂ))
        _ = (4 : ℝ) * ((((‖ψ‖ ^ 2 : ℝ) : ℂ)).re) := by
              simp [Complex.mul_re]
    have hinner : ((((‖ψ‖ ^ 2 : ℝ) : ℂ)).re) = ‖ψ‖ ^ 2 := by
      exact Complex.ofReal_re (‖ψ‖ ^ 2)
    calc
      (⟪ψ, ((4 : ℂ) • ψ)⟫_ℂ).re
          = (4 : ℝ) * ‖ψ‖ ^ 2 := by
            rw [hsmul_re, hinner]
      _ = 4 := by
            nlinarith [hψ]
  have happly : ((4 : (H_A ⊗[ℂ] H_B →ₗ[ℂ] H_A ⊗[ℂ] H_B)) ψ) = (4 : ℂ) • ψ := by
    change ((4 : ℕ) • ψ) = (4 : ℂ) • ψ
    symm
    exact Nat.cast_smul_eq_nsmul (R := ℂ) (n := 4) (b := ψ)
  calc
    (⟪ψ, ((4 : (H_A ⊗[ℂ] H_B →ₗ[ℂ] H_A ⊗[ℂ] H_B)) ψ)⟫_ℂ).re
        = (⟪ψ, ((4 : ℂ) • ψ)⟫_ℂ).re := by
            rw [happly]
    _ = 4 := h4smulC

set_option maxHeartbeats 1200000 in
private lemma approx_anticomm_A_small_branch
    (S : CHSHStrategy H_A H_B) (epsilon : Real)
    (U V : H_A →ₗ[ℂ] H_A) (idB : H_B →ₗ[ℂ] H_B)
    (hsmall : epsilon ≤ 2 * Real.sqrt 2 - 2)
    (hε_nonneg : 0 ≤ epsilon)
    (hComm_lb :
      ((2 * Real.sqrt 2) - epsilon) ^ 2 - 4
        ≤ 2 * ‖(((U - V) ⊗ₗ idB) S.psi)‖)
    (hNorm_U_id : ∀ z : H_A ⊗[ℂ] H_B, ‖((U ⊗ₗ idB) z)‖ = ‖z‖)
    (hNorm_V_id : ∀ z : H_A ⊗[ℂ] H_B, ‖((V ⊗ₗ idB) z)‖ = ‖z‖) :
    ‖(((U + V) ⊗ₗ idB) S.psi)‖ ^ 2 ≤ cConst * epsilon := by
  let u : H_A ⊗[ℂ] H_B := ((U ⊗ₗ idB) S.psi)
  let v : H_A ⊗[ℂ] H_B := ((V ⊗ₗ idB) S.psi)
  have hu_norm : ‖u‖ = 1 := by
    have hu : ‖((U ⊗ₗ idB) S.psi)‖ = ‖S.psi‖ := hNorm_U_id S.psi
    simpa [u, S.psi_norm] using hu
  have hv_norm : ‖v‖ = 1 := by
    have hv : ‖((V ⊗ₗ idB) S.psi)‖ = ‖S.psi‖ := hNorm_V_id S.psi
    simpa [v, S.psi_norm] using hv
  have hCu : (((U + V) ⊗ₗ idB) S.psi) = u + v := by
    simp [u, v, TensorProduct.map_add_left, LinearMap.add_apply]
  have hKv : (((U - V) ⊗ₗ idB) S.psi) = u - v := by
    rw [tensor_map_sub_left (H_A := H_A) (H_B := H_B) (f := U) (g := V) (h := idB)]
    simp [u, v, LinearMap.sub_apply]
  have hPar : ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 4 := by
    calc
      ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2
          = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
              simpa [pow_two] using (parallelogram_law_with_norm (𝕜 := ℂ) u v)
      _ = 4 := by nlinarith [hu_norm, hv_norm]
  have hAnti_norm : ‖u + v‖ ^ 2 = 4 - ‖u - v‖ ^ 2 := by
    nlinarith [hPar]
  have hhalf :
      (((2 * Real.sqrt 2) - epsilon) ^ 2 - 4) / 2 ≤ ‖u - v‖ := by
    have hComm_lb' :
        ((2 * Real.sqrt 2) - epsilon) ^ 2 - 4 ≤ 2 * ‖u - v‖ := by
      simpa [hKv] using hComm_lb
    nlinarith [hComm_lb']
  have hComm_sq :
      ((((2 * Real.sqrt 2) - epsilon) ^ 2 - 4) / 2) ^ 2 ≤ ‖u - v‖ ^ 2 := by
    have hhalf_nonneg : 0 ≤ (((2 * Real.sqrt 2) - epsilon) ^ 2 - 4) / 2 := by
      nlinarith [hsmall, Real.sqrt_nonneg (2 : Real)]
    nlinarith [hhalf, hhalf_nonneg, sq_nonneg ‖u - v‖]
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq2 : (Real.sqrt 2) ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : Real) ≤ 2 by norm_num)]
  have h0 : ‖u + v‖ ^ 2 ≤ 4 - ((((2 * Real.sqrt 2) - epsilon) ^ 2 - 4) / 2) ^ 2 := by
    nlinarith [hAnti_norm, hComm_sq]
  have h1 :
      4 - ((((2 * Real.sqrt 2) - epsilon) ^ 2 - 4) / 2) ^ 2 ≤ cConst * epsilon := by
    let t : Real := (2 * Real.sqrt 2) - epsilon
    have ht_nonneg : 0 ≤ t := by
      have : 0 ≤ (2 * Real.sqrt 2) - epsilon := by
        nlinarith [hsmall, hsqrt_nonneg]
      simpa [t] using this
    have ht_le : t ≤ 2 * Real.sqrt 2 := by
      have : (2 * Real.sqrt 2) - epsilon ≤ 2 * Real.sqrt 2 := by
        nlinarith [hε_nonneg]
      simpa [t] using this
    have ht_sq_le8 : t ^ 2 ≤ 8 := by
      nlinarith [ht_nonneg, ht_le, hsq2]
    have h8_sub_le : 8 - t ^ 2 ≤ 4 * Real.sqrt 2 * epsilon := by
      have : 8 - ((2 * Real.sqrt 2 - epsilon) ^ 2) ≤ 4 * Real.sqrt 2 * epsilon := by
        nlinarith [hsq2]
      simpa [t] using this
    have hfac_nonneg : 0 ≤ 4 * Real.sqrt 2 * epsilon := by
      nlinarith [hsqrt_nonneg, hε_nonneg]
    have hmul1 : t ^ 2 * (8 - t ^ 2) ≤ t ^ 2 * (4 * Real.sqrt 2 * epsilon) := by
      exact mul_le_mul_of_nonneg_left h8_sub_le (sq_nonneg t)
    have hmul2 : t ^ 2 * (4 * Real.sqrt 2 * epsilon) ≤ 8 * (4 * Real.sqrt 2 * epsilon) := by
      exact mul_le_mul_of_nonneg_right ht_sq_le8 hfac_nonneg
    have hmain :
        4 - ((((2 * Real.sqrt 2) - epsilon) ^ 2 - 4) / 2) ^ 2
          ≤ 8 * Real.sqrt 2 * epsilon := by
      have hEq : 4 - (((t ^ 2 - 4) / 2) ^ 2) = t ^ 2 * (8 - t ^ 2) / 4 := by
        ring
      have hle_num : t ^ 2 * (8 - t ^ 2) / 4 ≤ (8 * (4 * Real.sqrt 2 * epsilon)) / 4 := by
        nlinarith [hmul1, hmul2]
      calc
        4 - ((((2 * Real.sqrt 2) - epsilon) ^ 2 - 4) / 2) ^ 2
            = 4 - (((t ^ 2 - 4) / 2) ^ 2) := by simp [t]
        _ = t ^ 2 * (8 - t ^ 2) / 4 := hEq
        _ ≤ (8 * (4 * Real.sqrt 2 * epsilon)) / 4 := hle_num
        _ = 8 * Real.sqrt 2 * epsilon := by ring
    have hconst : 8 * Real.sqrt 2 * epsilon ≤ cConst * epsilon := by
      unfold cConst
      nlinarith [hsqrt_nonneg, hε_nonneg]
    exact le_trans hmain hconst
  have hbound : ‖u + v‖ ^ 2 ≤ cConst * epsilon := le_trans h0 h1
  simpa [hCu] using hbound

private lemma approx_anticomm_A_large_branch
    (S : CHSHStrategy H_A H_B) (epsilon : Real)
    (U V : H_A →ₗ[ℂ] H_A) (idB : H_B →ₗ[ℂ] H_B)
    (hlarge : 2 * Real.sqrt 2 - 2 < epsilon)
    (hNorm_U_id : ∀ z : H_A ⊗[ℂ] H_B, ‖((U ⊗ₗ idB) z)‖ = ‖z‖)
    (hNorm_V_id : ∀ z : H_A ⊗[ℂ] H_B, ‖((V ⊗ₗ idB) z)‖ = ‖z‖) :
    ‖(((U + V) ⊗ₗ idB) S.psi)‖ ^ 2 ≤ cConst * epsilon := by
  have hRHS_big : 4 ≤ cConst * epsilon := by
    have hc : 0 < cConst := by
      unfold cConst
      nlinarith [Real.sqrt_pos.2 (by norm_num : (0 : Real) < 2)]
    have hbase : 4 ≤ cConst * (2 * Real.sqrt 2 - 2) := by
      have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      have hsq2 : (Real.sqrt 2) ^ 2 = 2 := by
        nlinarith [Real.sq_sqrt (show (0 : Real) ≤ 2 by norm_num)]
      have hsqrt_ge : (4 / 3 : Real) ≤ Real.sqrt 2 := by
        nlinarith
      unfold cConst
      nlinarith [hsqrt_ge, hsqrt_nonneg, hsq2]
    have hmul : cConst * (2 * Real.sqrt 2 - 2) < cConst * epsilon := by
      exact mul_lt_mul_of_pos_left hlarge hc
    exact le_trans hbase (le_of_lt hmul)
  have hAnti_norm_le4 : ‖(((U + V) ⊗ₗ idB) S.psi)‖ ^ 2 ≤ 4 := by
    calc
      ‖(((U + V) ⊗ₗ idB) S.psi)‖ ^ 2
          = ‖((U ⊗ₗ idB) S.psi + (V ⊗ₗ idB) S.psi)‖ ^ 2 := by
              simp [TensorProduct.map_add_left, LinearMap.add_apply]
      _ ≤ (‖((U ⊗ₗ idB) S.psi)‖ + ‖((V ⊗ₗ idB) S.psi)‖) ^ 2 := by
            gcongr
            exact norm_add_le _ _
      _ = (‖S.psi‖ + ‖S.psi‖) ^ 2 := by rw [hNorm_U_id, hNorm_V_id]
      _ = 4 := by nlinarith [S.psi_norm]
  exact le_trans hAnti_norm_le4 hRHS_big

set_option maxHeartbeats 1200000 in
private lemma approx_anticomm_A_m_sq_expansions
    (S : CHSHStrategy H_A H_B) :
    let U : H_A →ₗ[ℂ] H_A := S.A1 ∘ₗ S.A0
    let V : H_A →ₗ[ℂ] H_A := S.A0 ∘ₗ S.A1
    let K_A : H_A →ₗ[ℂ] H_A := U - V
    let K_B : H_B →ₗ[ℂ] H_B := (S.B0 ∘ₗ S.B1) - (S.B1 ∘ₗ S.B0)
    let M : (H_A ⊗[ℂ] H_B) →ₗ[ℂ] (H_A ⊗[ℂ] H_B) :=
      CHSH_op (H_A := H_A) (H_B := H_B) S.A0 S.A1 S.B0 S.B1
    (‖M S.psi‖ ^ 2 = (⟪S.psi, (M ^ 2) S.psi⟫_ℂ).re) ∧
      ((⟪S.psi, (M ^ 2) S.psi⟫_ℂ).re
        = 4 + (⟪S.psi, ((K_A ⊗ₗ K_B) S.psi)⟫_ℂ).re) := by
  let U : H_A →ₗ[ℂ] H_A := S.A1 ∘ₗ S.A0
  let V : H_A →ₗ[ℂ] H_A := S.A0 ∘ₗ S.A1
  let K_A : H_A →ₗ[ℂ] H_A := U - V
  let K_B : H_B →ₗ[ℂ] H_B := (S.B0 ∘ₗ S.B1) - (S.B1 ∘ₗ S.B0)
  let M : (H_A ⊗[ℂ] H_B) →ₗ[ℂ] (H_A ⊗[ℂ] H_B) :=
    CHSH_op (H_A := H_A) (H_B := H_B) S.A0 S.A1 S.B0 S.B1
  have hA0_adj : S.A0.adjoint = S.A0 := by
    exact adjoint_eq_of_symm (A := S.A0) (IsBinaryObservable.symm (A := S.A0))
  have hA1_adj : S.A1.adjoint = S.A1 := by
    exact adjoint_eq_of_symm (A := S.A1) (IsBinaryObservable.symm (A := S.A1))
  have hB0_adj : S.B0.adjoint = S.B0 := by
    exact adjoint_eq_of_symm (A := S.B0) (IsBinaryObservable.symm (A := S.B0))
  have hB1_adj : S.B1.adjoint = S.B1 := by
    exact adjoint_eq_of_symm (A := S.B1) (IsBinaryObservable.symm (A := S.B1))
  have hM_adj : M.adjoint = M := by
    simp [M, CHSH_op, hA0_adj, hA1_adj, hB0_adj, hB1_adj, sub_eq_add_neg]
  have hM_sq :
      M ^ 2 = (4 : (H_A ⊗[ℂ] H_B →ₗ[ℂ] H_A ⊗[ℂ] H_B)) + (K_A ⊗ₗ K_B) := by
    have hCommA : ⟦S.A0, S.A1⟧ = -K_A := by
      ext x
      simp [K_A, U, V, sub_eq_add_neg, Module.End.mul_eq_comp]
    have hCommB : ⟦S.B0, S.B1⟧ = K_B := by
      ext x
      simp [K_B, sub_eq_add_neg, Module.End.mul_eq_comp]
    calc
      M ^ 2
          = (4 : (H_A ⊗[ℂ] H_B →ₗ[ℂ] H_A ⊗[ℂ] H_B))
              - (⟦S.A0, S.A1⟧ ⊗ₗ ⟦S.B0, S.B1⟧) := by
                simpa [M] using
                  (CHSH_op_sq (H_A := H_A) (H_B := H_B) S.A0 S.A1 S.B0 S.B1)
      _ = (4 : (H_A ⊗[ℂ] H_B →ₗ[ℂ] H_A ⊗[ℂ] H_B))
            + (K_A ⊗ₗ K_B) := by
              rw [hCommA, hCommB]
              simp [sub_eq_add_neg, map_neg_left]
  have hMnorm_sq :
      ‖M S.psi‖ ^ 2 = (⟪S.psi, (M ^ 2) S.psi⟫_ℂ).re := by
    calc
      ‖M S.psi‖ ^ 2
          = semi_norm_sq (H := H_A ⊗[ℂ] H_B) M S.psi := by
              symm
              simpa using
                (semi_norm_sq_eq_norm_sq (H := H_A ⊗[ℂ] H_B) (M := M) (ψ := S.psi))
      _ = (⟪S.psi, ((M.adjoint ∘ₗ M) S.psi)⟫_ℂ).re := by
              simp [semi_norm_sq]
      _ = (⟪S.psi, (M ^ 2) S.psi⟫_ℂ).re := by
              simp [hM_adj, pow_two]
  have hM2_expand :
      (⟪S.psi, (M ^ 2) S.psi⟫_ℂ).re
        = 4 + (⟪S.psi, ((K_A ⊗ₗ K_B) S.psi)⟫_ℂ).re := by
    rw [hM_sq]
    calc
      (⟪S.psi, (((4 : (H_A ⊗[ℂ] H_B →ₗ[ℂ] H_A ⊗[ℂ] H_B)) + (K_A ⊗ₗ K_B)) S.psi)⟫_ℂ).re
          = (⟪S.psi, ((4 : (H_A ⊗[ℂ] H_B →ₗ[ℂ] H_A ⊗[ℂ] H_B)) S.psi)⟫_ℂ).re
              + (⟪S.psi, ((K_A ⊗ₗ K_B) S.psi)⟫_ℂ).re := by
                simp [LinearMap.add_apply, inner_add_right, add_left_comm, add_assoc]
      _ = 4 + (⟪S.psi, ((K_A ⊗ₗ K_B) S.psi)⟫_ℂ).re := by
            have h4 :
                (⟪S.psi, ((4 : (H_A ⊗[ℂ] H_B →ₗ[ℂ] H_A ⊗[ℂ] H_B)) S.psi)⟫_ℂ).re = 4 := by
              exact inner_four_apply_re (H_A := H_A) (H_B := H_B) (ψ := S.psi) S.psi_norm
            simpa [h4]
  exact ⟨hMnorm_sq, hM2_expand⟩

private lemma approx_anticomm_A_tensor_estimates
    (S : CHSHStrategy H_A H_B) :
    let idB : H_B →ₗ[ℂ] H_B := LinearMap.id
    let U : H_A →ₗ[ℂ] H_A := S.A1 ∘ₗ S.A0
    let V : H_A →ₗ[ℂ] H_A := S.A0 ∘ₗ S.A1
    let K_A : H_A →ₗ[ℂ] H_A := U - V
    let K_B : H_B →ₗ[ℂ] H_B := (S.B0 ∘ₗ S.B1) - (S.B1 ∘ₗ S.B0)
    (∀ z : H_A ⊗[ℂ] H_B, ‖((U ⊗ₗ idB) z)‖ = ‖z‖) ∧
      (∀ z : H_A ⊗[ℂ] H_B, ‖((V ⊗ₗ idB) z)‖ = ‖z‖) ∧
      (‖((K_A ⊗ₗ K_B) S.psi)‖ ≤ 2 * ‖((K_A ⊗ₗ idB) S.psi)‖) ∧
      (‖((K_A ⊗ₗ K_B) S.psi)‖ ≤ 4) ∧
      ((⟪S.psi, ((K_A ⊗ₗ K_B) S.psi)⟫_ℂ).re ≤ ‖((K_A ⊗ₗ K_B) S.psi)‖) := by
  let idA : H_A →ₗ[ℂ] H_A := LinearMap.id
  let idB : H_B →ₗ[ℂ] H_B := LinearMap.id
  let U : H_A →ₗ[ℂ] H_A := S.A1 ∘ₗ S.A0
  let V : H_A →ₗ[ℂ] H_A := S.A0 ∘ₗ S.A1
  let K_A : H_A →ₗ[ℂ] H_A := U - V
  let K_B : H_B →ₗ[ℂ] H_B := (S.B0 ∘ₗ S.B1) - (S.B1 ∘ₗ S.B0)
  have hMap_sub_left (f g : H_A →ₗ[ℂ] H_A) :
      ((f - g) ⊗ₗ idB) = (f ⊗ₗ idB) - (g ⊗ₗ idB) := by
    exact tensor_map_sub_left (H_A := H_A) (H_B := H_B) (f := f) (g := g) (h := idB)
  have hMap_sub_right (f g : H_B →ₗ[ℂ] H_B) :
      (idA ⊗ₗ (f - g)) = (idA ⊗ₗ f) - (idA ⊗ₗ g) := by
    exact tensor_map_sub_right (H_A := H_A) (H_B := H_B) (f := idA) (g := f) (h := g)
  have hA0_iso : Isometry S.A0 := isometry_of_isBinaryObservable (H := H_A) (A := S.A0)
  have hA1_iso : Isometry S.A1 := isometry_of_isBinaryObservable (H := H_A) (A := S.A1)
  have hB0_iso : Isometry S.B0 := isometry_of_isBinaryObservable (H := H_B) (A := S.B0)
  have hB1_iso : Isometry S.B1 := isometry_of_isBinaryObservable (H := H_B) (A := S.B1)
  have hU_iso : Isometry U := by simpa [U] using hA1_iso.comp hA0_iso
  have hV_iso : Isometry V := by simpa [V] using hA0_iso.comp hA1_iso
  have hB01_iso : Isometry (S.B0 ∘ₗ S.B1) := by simpa using hB0_iso.comp hB1_iso
  have hB10_iso : Isometry (S.B1 ∘ₗ S.B0) := by simpa using hB1_iso.comp hB0_iso
  have hIdA_iso : Isometry idA := by simpa [idA] using (linearMap_id_isometry (E := H_A))
  have hIdB_iso : Isometry idB := by simpa [idB] using (linearMap_id_isometry (E := H_B))
  have hNorm_U_id (z : H_A ⊗[ℂ] H_B) : ‖((U ⊗ₗ idB) z)‖ = ‖z‖ := by
    simpa [idB] using (tensor_map_norm_eq (f := U) (g := idB) hU_iso hIdB_iso z)
  have hNorm_V_id (z : H_A ⊗[ℂ] H_B) : ‖((V ⊗ₗ idB) z)‖ = ‖z‖ := by
    simpa [idB] using (tensor_map_norm_eq (f := V) (g := idB) hV_iso hIdB_iso z)
  have hNorm_id_B01 (z : H_A ⊗[ℂ] H_B) :
      ‖((idA ⊗ₗ (S.B0 ∘ₗ S.B1)) z)‖ = ‖z‖ := by
    simpa [idA] using (tensor_map_norm_eq (f := idA) (g := (S.B0 ∘ₗ S.B1)) hIdA_iso hB01_iso z)
  have hNorm_id_B10 (z : H_A ⊗[ℂ] H_B) :
      ‖((idA ⊗ₗ (S.B1 ∘ₗ S.B0)) z)‖ = ‖z‖ := by
    simpa [idA] using (tensor_map_norm_eq (f := idA) (g := (S.B1 ∘ₗ S.B0)) hIdA_iso hB10_iso z)
  have hKA_bound (z : H_A ⊗[ℂ] H_B) : ‖((K_A ⊗ₗ idB) z)‖ ≤ 2 * ‖z‖ := by
    have hmapK : (K_A ⊗ₗ idB) = (U ⊗ₗ idB) - (V ⊗ₗ idB) := by
      simpa [K_A] using hMap_sub_left (f := U) (g := V)
    calc
      ‖((K_A ⊗ₗ idB) z)‖
          = ‖((U ⊗ₗ idB) z) - ((V ⊗ₗ idB) z)‖ := by rw [hmapK, LinearMap.sub_apply]
      _ ≤ ‖((U ⊗ₗ idB) z)‖ + ‖((V ⊗ₗ idB) z)‖ := norm_sub_le _ _
      _ = ‖z‖ + ‖z‖ := by rw [hNorm_U_id, hNorm_V_id]
      _ = 2 * ‖z‖ := by ring
  have hKB_bound (z : H_A ⊗[ℂ] H_B) : ‖((idA ⊗ₗ K_B) z)‖ ≤ 2 * ‖z‖ := by
    have hmapK : (idA ⊗ₗ K_B) = (idA ⊗ₗ (S.B0 ∘ₗ S.B1)) - (idA ⊗ₗ (S.B1 ∘ₗ S.B0)) := by
      simpa [K_B] using hMap_sub_right (f := (S.B0 ∘ₗ S.B1)) (g := (S.B1 ∘ₗ S.B0))
    calc
      ‖((idA ⊗ₗ K_B) z)‖
          = ‖((idA ⊗ₗ (S.B0 ∘ₗ S.B1)) z) - ((idA ⊗ₗ (S.B1 ∘ₗ S.B0)) z)‖ := by
              rw [hmapK, LinearMap.sub_apply]
      _ ≤ ‖((idA ⊗ₗ (S.B0 ∘ₗ S.B1)) z)‖ + ‖((idA ⊗ₗ (S.B1 ∘ₗ S.B0)) z)‖ := norm_sub_le _ _
      _ = ‖z‖ + ‖z‖ := by rw [hNorm_id_B01, hNorm_id_B10]
      _ = 2 * ‖z‖ := by ring
  have hKAKB_comp : (K_A ⊗ₗ K_B) = ((idA ⊗ₗ K_B) ∘ₗ (K_A ⊗ₗ idB)) := by
    ext x y
    simp [LinearMap.comp_apply, TensorProduct.map_tmul, idA, idB]
  have hKAKB_norm_le : ‖((K_A ⊗ₗ K_B) S.psi)‖ ≤ 2 * ‖((K_A ⊗ₗ idB) S.psi)‖ := by
    have happ := congrArg (fun F => F S.psi) hKAKB_comp
    calc
      ‖((K_A ⊗ₗ K_B) S.psi)‖
          = ‖((idA ⊗ₗ K_B) (((K_A ⊗ₗ idB) S.psi)))‖ := by
              simpa [LinearMap.comp_apply] using congrArg (fun z => ‖z‖) happ
      _ ≤ 2 * ‖((K_A ⊗ₗ idB) S.psi)‖ := hKB_bound _
  have hKAKB_norm_le4 : ‖((K_A ⊗ₗ K_B) S.psi)‖ ≤ 4 := by
    calc
      ‖((K_A ⊗ₗ K_B) S.psi)‖ ≤ 2 * ‖((K_A ⊗ₗ idB) S.psi)‖ := hKAKB_norm_le
      _ ≤ 2 * (2 * ‖S.psi‖) := by gcongr; exact hKA_bound S.psi
      _ = 4 := by norm_num [S.psi_norm]
  have hRe_prod_le_norm :
      (⟪S.psi, ((K_A ⊗ₗ K_B) S.psi)⟫_ℂ).re ≤ ‖((K_A ⊗ₗ K_B) S.psi)‖ := by
    calc
      (⟪S.psi, ((K_A ⊗ₗ K_B) S.psi)⟫_ℂ).re ≤ ‖⟪S.psi, ((K_A ⊗ₗ K_B) S.psi)⟫_ℂ‖ := by
        exact Complex.re_le_norm _
      _ ≤ ‖S.psi‖ * ‖((K_A ⊗ₗ K_B) S.psi)‖ := by
            simpa using (norm_inner_le_norm S.psi ((K_A ⊗ₗ K_B) S.psi))
      _ = ‖((K_A ⊗ₗ K_B) S.psi)‖ := by simp [S.psi_norm]
  exact ⟨hNorm_U_id, hNorm_V_id, hKAKB_norm_le, hKAKB_norm_le4, hRe_prod_le_norm⟩

private lemma approx_anticomm_A_norm_sq_bound
    (hBias : chshBias S ≥ (2 * Real.sqrt 2) - epsilon) :
    ‖((((S.A1 ∘ₗ S.A0 + S.A0 ∘ₗ S.A1) ⊗ₗ
      (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi))‖ ^ 2
      ≤ (cConst) * epsilon := by
  let idB : H_B →ₗ[ℂ] H_B := LinearMap.id
  let U : H_A →ₗ[ℂ] H_A := S.A1 ∘ₗ S.A0
  let V : H_A →ₗ[ℂ] H_A := S.A0 ∘ₗ S.A1
  let C_A : H_A →ₗ[ℂ] H_A := U + V
  let K_A : H_A →ₗ[ℂ] H_A := U - V
  let K_B : H_B →ₗ[ℂ] H_B := (S.B0 ∘ₗ S.B1) - (S.B1 ∘ₗ S.B0)
  let M : (H_A ⊗[ℂ] H_B) →ₗ[ℂ] (H_A ⊗[ℂ] H_B) :=
    CHSH_op (H_A := H_A) (H_B := H_B) S.A0 S.A1 S.B0 S.B1
  rcases (approx_anticomm_A_m_sq_expansions (H_A := H_A) (H_B := H_B) S) with
    ⟨hMnorm_sq, hM2_expand⟩
  rcases (approx_anticomm_A_tensor_estimates (H_A := H_A) (H_B := H_B) S) with
    ⟨hNorm_U_id, hNorm_V_id, hKAKB_norm_le, hKAKB_norm_le4, hRe_prod_le_norm⟩
  have hMnorm_sq_le8 : ‖M S.psi‖ ^ 2 ≤ 8 := by
    calc
      ‖M S.psi‖ ^ 2
          = (⟪S.psi, (M ^ 2) S.psi⟫_ℂ).re := by simpa [M, K_A, K_B] using hMnorm_sq
      _ = 4 + (⟪S.psi, ((K_A ⊗ₗ K_B) S.psi)⟫_ℂ).re := by
            simpa [M, K_A, K_B] using hM2_expand
      _ ≤ 4 + ‖((K_A ⊗ₗ K_B) S.psi)‖ := by gcongr
      _ ≤ 4 + 4 := by
            nlinarith [(by simpa [K_A, K_B] using hKAKB_norm_le4)]
      _ = 8 := by ring
  have hMnorm_le_2sqrt2 : ‖M S.psi‖ ≤ 2 * Real.sqrt 2 := by
    have hsq : ‖M S.psi‖ ^ 2 ≤ (2 * Real.sqrt 2) ^ 2 := by
      have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := by
        nlinarith [Real.sq_sqrt (show (0 : Real) ≤ 2 by norm_num)]
      nlinarith [hMnorm_sq_le8, hsqrt2]
    have habs : |‖M S.psi‖| ≤ |2 * Real.sqrt 2| := (sq_le_sq).1 hsq
    have hnonneg' : 0 ≤ 2 * Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg (2 : Real)]
    simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hnonneg'] using habs
  have hMexp : (2 * Real.sqrt 2) - epsilon ≤ (⟪S.psi, M S.psi⟫_ℂ).re := by
    simpa [chshBias, M] using hBias
  have hMexp_upper : (⟪S.psi, M S.psi⟫_ℂ).re ≤ 2 * Real.sqrt 2 := by
    calc
      (⟪S.psi, M S.psi⟫_ℂ).re ≤ ‖⟪S.psi, M S.psi⟫_ℂ‖ := by exact Complex.re_le_norm _
      _ ≤ ‖S.psi‖ * ‖M S.psi‖ := by simpa using (norm_inner_le_norm S.psi (M S.psi))
      _ = ‖M S.psi‖ := by simp [S.psi_norm]
      _ ≤ 2 * Real.sqrt 2 := hMnorm_le_2sqrt2
  have hε_nonneg : 0 ≤ epsilon := by
    nlinarith [hMexp, hMexp_upper]
  by_cases hsmall : epsilon ≤ 2 * Real.sqrt 2 - 2
  · have hleft_nonneg : 0 ≤ (2 * Real.sqrt 2) - epsilon := by
      nlinarith [hsmall, Real.sqrt_nonneg (2 : Real)]
    have hleft_le_norm : (2 * Real.sqrt 2) - epsilon ≤ ‖M S.psi‖ := by
      have hRe_le_norm : (⟪S.psi, M S.psi⟫_ℂ).re ≤ ‖M S.psi‖ := by
        calc
          (⟪S.psi, M S.psi⟫_ℂ).re ≤ ‖⟪S.psi, M S.psi⟫_ℂ‖ := by exact Complex.re_le_norm _
          _ ≤ ‖S.psi‖ * ‖M S.psi‖ := by simpa using (norm_inner_le_norm S.psi (M S.psi))
          _ = ‖M S.psi‖ := by simp [S.psi_norm]
      exact le_trans hMexp hRe_le_norm
    have hM2_lower : ((2 * Real.sqrt 2) - epsilon) ^ 2 ≤ (⟪S.psi, (M ^ 2) S.psi⟫_ℂ).re := by
      have hsq : ((2 * Real.sqrt 2) - epsilon) ^ 2 ≤ ‖M S.psi‖ ^ 2 := by
        nlinarith [hleft_le_norm, hleft_nonneg]
      exact le_trans hsq (by simpa [M, K_A, K_B] using (le_of_eq hMnorm_sq))
    have hProd_lb :
        ((2 * Real.sqrt 2) - epsilon) ^ 2 - 4
          ≤ (⟪S.psi, ((K_A ⊗ₗ K_B) S.psi)⟫_ℂ).re := by
      nlinarith [hM2_lower, (by simpa [M, K_A, K_B] using hM2_expand)]
    have hComm_lb :
        ((2 * Real.sqrt 2) - epsilon) ^ 2 - 4 ≤ 2 * ‖((K_A ⊗ₗ idB) S.psi)‖ := by
      exact le_trans hProd_lb (le_trans (by simpa [K_A, K_B] using hRe_prod_le_norm)
        (by simpa [K_A, K_B] using hKAKB_norm_le))
    have hComm_lb_uv :
        ((2 * Real.sqrt 2) - epsilon) ^ 2 - 4 ≤ 2 * ‖(((U - V) ⊗ₗ idB) S.psi)‖ := by
      simpa [K_A] using hComm_lb
    have hbound :
        ‖(((U + V) ⊗ₗ idB) S.psi)‖ ^ 2 ≤ cConst * epsilon := by
      exact approx_anticomm_A_small_branch
        (H_A := H_A) (H_B := H_B)
        (S := S) (epsilon := epsilon)
        (U := U) (V := V) (idB := idB)
        hsmall hε_nonneg hComm_lb_uv
        (by simpa [U, idB] using hNorm_U_id)
        (by simpa [V, idB] using hNorm_V_id)
    simpa [C_A, U, V] using hbound
  · have hlarge : 2 * Real.sqrt 2 - 2 < epsilon := lt_of_not_ge hsmall
    have hbound :
        ‖(((U + V) ⊗ₗ idB) S.psi)‖ ^ 2 ≤ cConst * epsilon := by
      exact approx_anticomm_A_large_branch
        (H_A := H_A) (H_B := H_B)
        (S := S) (epsilon := epsilon)
        (U := U) (V := V) (idB := idB)
        hlarge
        (by simpa [U, idB] using hNorm_U_id)
        (by simpa [V, idB] using hNorm_V_id)
    simpa [C_A, U, V] using hbound

theorem approx_anticomm_A
    (hBias : chshBias S ≥ (2 * Real.sqrt 2) - epsilon) :
    (⟪S.psi, (((S.A1 ∘ₗ S.A0 + S.A0 ∘ₗ S.A1) ^ 2) ⊗ₗ (LinearMap.id)) (S.psi)⟫_ℂ).re
      ≤ (cConst) * epsilon := by
  have hA0_adj : S.A0.adjoint = S.A0 := by
    exact adjoint_eq_of_symm (A := S.A0) (IsBinaryObservable.symm (A := S.A0))
  have hA1_adj : S.A1.adjoint = S.A1 := by
    exact adjoint_eq_of_symm (A := S.A1) (IsBinaryObservable.symm (A := S.A1))
  have hNorm :
      ‖((((S.A1 ∘ₗ S.A0 + S.A0 ∘ₗ S.A1) ⊗ₗ
        (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi))‖ ^ 2
        ≤ cConst * epsilon := by
    exact approx_anticomm_A_norm_sq_bound (S := S) (epsilon := epsilon) hBias
  have hInner_eq_norm :
      (⟪S.psi, (((S.A1 ∘ₗ S.A0 + S.A0 ∘ₗ S.A1) ^ 2) ⊗ₗ
        (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi⟫_ℂ).re
        =
      ‖((((S.A1 ∘ₗ S.A0 + S.A0 ∘ₗ S.A1) ⊗ₗ
        (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi))‖ ^ 2 := by
    simpa using
      (anticommutator_inner_sq_eq_norm_sq
        (H_A := H_A) (H_B := H_B)
        (A0 := S.A0) (A1 := S.A1) (ψ := S.psi) hA0_adj hA1_adj)
  rw [hInner_eq_norm]
  exact hNorm

theorem approx_anticomm_B
    (hBias : chshBias S ≥ (2 * Real.sqrt 2) - epsilon) :
    (⟪S.psi, ((LinearMap.id) ⊗ₗ ((S.B0 ∘ₗ S.B1 + S.B1 ∘ₗ S.B0) ^ 2)) (S.psi)⟫_ℂ).re
      ≤ (cConst) * epsilon := by
  let T : CHSHStrategy H_B H_A := swapStrategy (H_A := H_A) (H_B := H_B) S
  have hBiasT : chshBias T ≥ (2 * Real.sqrt 2) - epsilon := by
    simpa [T] using (show chshBias (swapStrategy (H_A := H_A) (H_B := H_B) S)
      ≥ (2 * Real.sqrt 2) - epsilon by
        simpa [chshBias_swap (H_A := H_A) (H_B := H_B) (S := S)] using hBias)
  have hA :
      (⟪T.psi, (((T.A1 ∘ₗ T.A0 + T.A0 ∘ₗ T.A1) ^ 2) ⊗ₗ (LinearMap.id)) T.psi⟫_ℂ).re
        ≤ cConst * epsilon := by
    exact approx_anticomm_A (S := T) (epsilon := epsilon) hBiasT
  have hswap :
      (⟪(TensorProduct.comm ℂ H_A H_B) S.psi,
          (((S.B1 ∘ₗ S.B0 + S.B0 ∘ₗ S.B1) ^ 2) ⊗ₗ
            (LinearMap.id : H_A →ₗ[ℂ] H_A)) ((TensorProduct.comm ℂ H_A H_B) S.psi)⟫_ℂ).re
        =
      (⟪S.psi,
          ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ
            ((S.B1 ∘ₗ S.B0 + S.B0 ∘ₗ S.B1) ^ 2)) S.psi⟫_ℂ).re := by
    exact congrArg Complex.re
      (term_swap (S := S)
        (A := (LinearMap.id : H_A →ₗ[ℂ] H_A))
        (B := ((S.B1 ∘ₗ S.B0 + S.B0 ∘ₗ S.B1) ^ 2)))
  calc
    (⟪S.psi, ((LinearMap.id) ⊗ₗ ((S.B0 ∘ₗ S.B1 + S.B1 ∘ₗ S.B0) ^ 2)) (S.psi)⟫_ℂ).re
        =
      (⟪(TensorProduct.comm ℂ H_A H_B) S.psi,
          (((S.B1 ∘ₗ S.B0 + S.B0 ∘ₗ S.B1) ^ 2) ⊗ₗ
            (LinearMap.id : H_A →ₗ[ℂ] H_A)) ((TensorProduct.comm ℂ H_A H_B) S.psi)⟫_ℂ).re := by
          simpa [add_comm] using hswap.symm
    _ = (⟪T.psi, (((T.A1 ∘ₗ T.A0 + T.A0 ∘ₗ T.A1) ^ 2) ⊗ₗ (LinearMap.id)) T.psi⟫_ℂ).re := by
          simpa [T, swapStrategy, add_comm]
    _ ≤ cConst * epsilon := hA



set_option maxHeartbeats 1200000 in
lemma eq216
    (hBias : chshBias S ≥ (2 * Real.sqrt 2) - epsilon) :
    ‖(((((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ∘ₗ
            (VA (H := H_A) S.A0 S.A1)) -
          ((VA (H := H_A) S.A0 S.A1) ∘ₗ S.A1)) ⊗ₗ
        (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi)‖ ^ 2
      ≤ cConst * epsilon := by
  let idA : H_A →ₗ[ℂ] H_A := LinearMap.id
  let idB : H_B →ₗ[ℂ] H_B := LinearMap.id
  let V_A : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) := VA (H := H_A) S.A0 S.A1
  let C : H_A →ₗ[ℂ] H_A := (S.A1 ∘ₗ S.A0) + (S.A0 ∘ₗ S.A1)
  let Δ : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) :=
    ((pauliX ⊗ₗ idA) ∘ₗ V_A) - (V_A ∘ₗ S.A1)

  have hAnti :
      (⟪S.psi, (((C ^ 2) ⊗ₗ idB) S.psi)⟫_ℂ).re ≤ cConst * epsilon := by
    simpa [C, idB, pow_two, add_comm, add_left_comm, add_assoc] using
      (approx_anticomm_A (S := S) (epsilon := epsilon) hBias)

  have hA0_adj : S.A0.adjoint = S.A0 := by
    exact adjoint_eq_of_symm (A := S.A0) (IsBinaryObservable.symm (A := S.A0))
  have hA1_adj : S.A1.adjoint = S.A1 := by
    exact adjoint_eq_of_symm (A := S.A1) (IsBinaryObservable.symm (A := S.A1))
  have hC_eq_norm :
      ‖((C ⊗ₗ idB) S.psi)‖ ^ 2
        = (⟪S.psi, (((C ^ 2) ⊗ₗ idB) S.psi)⟫_ℂ).re := by
    simpa [C, idB] using
      (anticommutator_inner_sq_eq_norm_sq
        (H_A := H_A) (H_B := H_B)
        (A0 := S.A0) (A1 := S.A1) (ψ := S.psi) hA0_adj hA1_adj).symm

  have hCbound : ‖((C ⊗ₗ idB) S.psi)‖ ^ 2 ≤ cConst * epsilon := by
    rw [hC_eq_norm]
    exact hAnti

  -- Core geometric step (Eq. (216) from the derivation):
  -- `‖((Δ ⊗ I) ψ)‖² ≤ ‖((C ⊗ I) ψ)‖²`.
  -- This follows by expanding `VA`, rewriting `Δ` in terms of `C`,
  -- then transporting norms through the isometries `A1`, `|0⟩⊗I`, `|1⟩⊗I`.
  have hDelta_le_C :
      ‖((Δ ⊗ₗ idB) S.psi)‖ ^ 2 ≤ ‖((C ⊗ₗ idB) S.psi)‖ ^ 2 := by
    let F0 : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) := (embed (H := H_A) ket0) ∘ₗ C
    let F1 : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) := (embed (H := H_A) ket1) ∘ₗ (S.A1 ∘ₗ C)
    -- Explicit expansion of `Δ` in terms of the anticommutator map `C`.
    have hDelta_formula : Δ = ((1 / 2 : ℂ) • (F1 - F0)) := by
      let s : ℂ := (Real.sqrt 2 : ℂ)⁻¹
      have hV (y : H_A) :
          V_A y =
            (s * s) • ((ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] (S.A1 y)) +
              (ket0 ⊗ₜ[ℂ] (S.A0 y) - ket1 ⊗ₜ[ℂ] (S.A1 (S.A0 y)))) := by
        let hadT : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) := Hadamard ⊗ₗ idA
        have hadT_ket0 (u : H_A) :
            hadT (ket0 ⊗ₜ[ℂ] u) = s • (ket0 ⊗ₜ[ℂ] u + ket1 ⊗ₜ[ℂ] u) := by
          simp [hadT, idA, Hadamard, s, TensorProduct.map_tmul, TensorProduct.smul_tmul,
            TensorProduct.add_tmul, smul_add]
        have hadT_ket1 (u : H_A) :
            hadT (ket1 ⊗ₜ[ℂ] u) = s • (ket0 ⊗ₜ[ℂ] u - ket1 ⊗ₜ[ℂ] u) := by
          simp [sub_eq_add_neg, hadT, idA, Hadamard, s, TensorProduct.map_tmul,
            TensorProduct.smul_tmul, TensorProduct.add_tmul, TensorProduct.neg_tmul, smul_add,
            add_comm]
        have ctrl_ket0 (A : H_A →ₗ[ℂ] H_A) (u : H_A) :
            control (H := H_A) A (ket0 ⊗ₜ[ℂ] u) = ket0 ⊗ₜ[ℂ] u := by
          simp [control, TensorProduct.map_tmul, LinearMap.id_apply,
            proj0_ket0, proj1_ket0]
        have ctrl_ket1 (A : H_A →ₗ[ℂ] H_A) (u : H_A) :
            control (H := H_A) A (ket1 ⊗ₜ[ℂ] u) = ket1 ⊗ₜ[ℂ] (A u) := by
          simp [control, TensorProduct.map_tmul, LinearMap.id_apply,
            proj0_ket1, proj1_ket1]
        have hHadEmbed :
            hadT ((embed (H := H_A) ket0) y) = s • (ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] y) := by
          simpa [embed] using (hadT_ket0 y)
        have hCtrl0 :
            control (H := H_A) S.A0 (hadT ((embed (H := H_A) ket0) y)) =
              s • (ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] (S.A0 y)) := by
          simp [hHadEmbed, LinearMap.map_add, ctrl_ket0, ctrl_ket1]
        have hPre :
            hadT (control (H := H_A) S.A0 (hadT ((embed (H := H_A) ket0) y))) =
              (s * s) • ((ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] y) +
                (ket0 ⊗ₜ[ℂ] (S.A0 y) - ket1 ⊗ₜ[ℂ] (S.A0 y))) := by
          calc
            hadT (control (H := H_A) S.A0 (hadT ((embed (H := H_A) ket0) y)))
                = hadT (s • (ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] (S.A0 y))) := by
                    simp [hCtrl0]
            _ = s • hadT (ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] (S.A0 y)) := by simp
            _ = s • (hadT (ket0 ⊗ₜ[ℂ] y) + hadT (ket1 ⊗ₜ[ℂ] (S.A0 y))) := by
                    simp [LinearMap.map_add]
            _ = s • (s • (ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] y) +
                  s • (ket0 ⊗ₜ[ℂ] (S.A0 y) - ket1 ⊗ₜ[ℂ] (S.A0 y))) := by
                    simp [hadT_ket0, hadT_ket1]
            _ = (s * s) • ((ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] y) +
                  (ket0 ⊗ₜ[ℂ] (S.A0 y) - ket1 ⊗ₜ[ℂ] (S.A0 y))) := by
                    simp [smul_add, smul_sub, smul_smul, add_assoc]
        have hCtrl1 :
            control (H := H_A) S.A1 (hadT (control (H := H_A) S.A0 (hadT ((embed (H := H_A) ket0) y))))
              =
              (s * s) • ((ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] (S.A1 y)) +
                (ket0 ⊗ₜ[ℂ] (S.A0 y) - ket1 ⊗ₜ[ℂ] (S.A1 (S.A0 y)))) := by
          calc
            control (H := H_A) S.A1
                (hadT (control (H := H_A) S.A0 (hadT ((embed (H := H_A) ket0) y))))
                =
                control (H := H_A) S.A1
                  ((s * s) • ((ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] y) +
                    (ket0 ⊗ₜ[ℂ] (S.A0 y) - ket1 ⊗ₜ[ℂ] (S.A0 y)))) := by
                  simp [hPre]
            _ =
                (s * s) •
                  control (H := H_A) S.A1
                    ((ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] y) +
                      (ket0 ⊗ₜ[ℂ] (S.A0 y) - ket1 ⊗ₜ[ℂ] (S.A0 y))) := by simp
            _ =
                (s * s) • ((ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] (S.A1 y)) +
                  (ket0 ⊗ₜ[ℂ] (S.A0 y) - ket1 ⊗ₜ[ℂ] (S.A1 (S.A0 y)))) := by
                  simp [LinearMap.map_add, ctrl_ket0, ctrl_ket1, sub_eq_add_neg,
                    add_assoc, add_left_comm]
        simpa [V_A, VA, unitaryUA, hadT, idA, LinearMap.comp_apply] using hCtrl1

      ext x
      have hA1sq : S.A1 (S.A1 x) = x := by
        simpa [LinearMap.comp_apply] using congrArg (fun f => f x) (IsBinaryObservable.sq_one (A := S.A1))
      have hA1sqA0 : S.A1 (S.A1 (S.A0 x)) = S.A0 x := by
        simpa [LinearMap.comp_apply] using
          congrArg (fun f => f (S.A0 x)) (IsBinaryObservable.sq_one (A := S.A1))
      have hs : (s * s) = (1 / 2 : ℂ) := by
        have hsqrt_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
          exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
        have hsq2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = (2 : ℂ) := by
          exact_mod_cast (by nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)])
        dsimp [s]
        field_simp [hsqrt_ne]
        simpa [pow_two] using hsq2.symm
      simp [Δ, F0, F1, hV, hs, hA1sq, sub_eq_add_neg,
        smul_add, add_assoc, add_left_comm, add_comm, embed]
      simp [C, idA, LinearMap.id_apply, hA1sqA0, TensorProduct.tmul_add, smul_add,
        add_assoc, add_left_comm, add_comm]

    have hA1Iso : Isometry S.A1 := isometry_of_isBinaryObservable (H := H_A) (A := S.A1)
    have hEmbed0 : Isometry (embed (H := H_A) ket0) :=
      embed_is_isometry (H := H_A) ket0 (by simp [ket0])
    have hEmbed1 : Isometry (embed (H := H_A) ket1) :=
      embed_is_isometry (H := H_A) ket1 (by simp [ket1])
    have hIdB_iso : Isometry idB := by
      simpa [idB] using (linearMap_id_isometry (E := H_B))
    have hNormE0 (z : H_A ⊗[ℂ] H_B) : ‖(((embed (H := H_A) ket0) ⊗ₗ idB) z)‖ = ‖z‖ := by
      simpa [idB] using
        (tensor_map_norm_eq (f := (embed (H := H_A) ket0)) (g := idB) hEmbed0 hIdB_iso z)
    have hNormE1 (z : H_A ⊗[ℂ] H_B) : ‖(((embed (H := H_A) ket1) ⊗ₗ idB) z)‖ = ‖z‖ := by
      simpa [idB] using
        (tensor_map_norm_eq (f := (embed (H := H_A) ket1)) (g := idB) hEmbed1 hIdB_iso z)
    have hNormA1 (z : H_A ⊗[ℂ] H_B) : ‖((S.A1 ⊗ₗ idB) z)‖ = ‖z‖ := by
      simpa [idB] using
        (tensor_map_norm_eq (f := S.A1) (g := idB) hA1Iso hIdB_iso z)

    have hF0comp :
        (F0 ⊗ₗ idB) = (((embed (H := H_A) ket0) ⊗ₗ idB) ∘ₗ (C ⊗ₗ idB)) := by
      have hmap :
          ((embed (H := H_A) ket0 ∘ₗ C) ⊗ₗ (idB ∘ₗ idB))
            = (((embed (H := H_A) ket0) ⊗ₗ idB) ∘ₗ (C ⊗ₗ idB)) := by
        simpa using (TensorProduct.map_comp (embed (H := H_A) ket0) idB C idB)
      simpa [F0, idB] using hmap
    have hF1comp :
        (F1 ⊗ₗ idB) =
          (((embed (H := H_A) ket1) ⊗ₗ idB) ∘ₗ
            (((S.A1 ⊗ₗ idB) ∘ₗ (C ⊗ₗ idB)))) := by
      have hmap1 :
          ((embed (H := H_A) ket1 ∘ₗ (S.A1 ∘ₗ C)) ⊗ₗ (idB ∘ₗ idB))
            = (((embed (H := H_A) ket1) ⊗ₗ idB) ∘ₗ (((S.A1 ∘ₗ C) ⊗ₗ idB))) := by
        simpa using (TensorProduct.map_comp (embed (H := H_A) ket1) idB (S.A1 ∘ₗ C) idB)
      have hmap2 :
          ((S.A1 ∘ₗ C) ⊗ₗ idB) = ((S.A1 ⊗ₗ idB) ∘ₗ (C ⊗ₗ idB)) := by
        have : ((S.A1 ∘ₗ C) ⊗ₗ (idB ∘ₗ idB)) = ((S.A1 ⊗ₗ idB) ∘ₗ (C ⊗ₗ idB)) := by
          simpa using (TensorProduct.map_comp S.A1 idB C idB)
        simpa [idB] using this
      calc
        (F1 ⊗ₗ idB)
            = ((embed (H := H_A) ket1 ∘ₗ (S.A1 ∘ₗ C)) ⊗ₗ idB) := by
                rfl
        _ = ((embed (H := H_A) ket1 ⊗ₗ idB) ∘ₗ (((S.A1 ∘ₗ C) ⊗ₗ idB))) := by
                simpa [idB] using hmap1
        _ = (((embed (H := H_A) ket1) ⊗ₗ idB) ∘ₗ
              (((S.A1 ⊗ₗ idB) ∘ₗ (C ⊗ₗ idB)))) := by
                rw [hmap2]

    have hF0norm :
        ‖((F0 ⊗ₗ idB) S.psi)‖ = ‖((C ⊗ₗ idB) S.psi)‖ := by
      have happ := congrArg (fun F => F S.psi) hF0comp
      calc
        ‖((F0 ⊗ₗ idB) S.psi)‖
            = ‖(((embed (H := H_A) ket0) ⊗ₗ idB) ((C ⊗ₗ idB) S.psi))‖ := by
                simpa [LinearMap.comp_apply] using congrArg (fun z => ‖z‖) happ
        _ = ‖((C ⊗ₗ idB) S.psi)‖ := hNormE0 _
    have hF1norm :
        ‖((F1 ⊗ₗ idB) S.psi)‖ = ‖((C ⊗ₗ idB) S.psi)‖ := by
      have happ := congrArg (fun F => F S.psi) hF1comp
      calc
        ‖((F1 ⊗ₗ idB) S.psi)‖
            = ‖(((embed (H := H_A) ket1) ⊗ₗ idB)
                (((S.A1 ⊗ₗ idB) ((C ⊗ₗ idB) S.psi))))‖ := by
                  simpa [LinearMap.comp_apply] using congrArg (fun z => ‖z‖) happ
        _ = ‖((S.A1 ⊗ₗ idB) (((C ⊗ₗ idB) S.psi)))‖ := hNormE1 _
        _ = ‖((C ⊗ₗ idB) S.psi)‖ := hNormA1 _

    have hSq : ‖((Δ ⊗ₗ idB) S.psi)‖ ^ 2 ≤ ‖((C ⊗ₗ idB) S.psi)‖ ^ 2 := by
      letI : NormedAddCommGroup ((Qubit ⊗[ℂ] H_A) ⊗[ℂ] H_B) := TensorProduct.instNormedAddCommGroup
      letI : InnerProductSpace ℂ ((Qubit ⊗[ℂ] H_A) ⊗[ℂ] H_B) := TensorProduct.instInnerProductSpace
      have hMapSmul :
          (((1 / 2 : ℂ) • (F1 - F0)) ⊗ₗ idB) = (1 / 2 : ℂ) • (((F1 - F0) ⊗ₗ idB)) := by
        simpa using
          (TensorProduct.map_smul_left (r := (1 / 2 : ℂ)) (f := (F1 - F0)) (g := idB))
      have hEq :
          ((Δ ⊗ₗ idB) S.psi) = (1 / 2 : ℂ) • (((F1 - F0) ⊗ₗ idB) S.psi) := by
        calc
          ((Δ ⊗ₗ idB) S.psi)
              = ((((1 / 2 : ℂ) • (F1 - F0)) ⊗ₗ idB) S.psi) := by
                  simp [hDelta_formula]
          _ = (((1 / 2 : ℂ) • (((F1 - F0) ⊗ₗ idB)) ) S.psi) := by
                  simpa using congrArg (fun F => F S.psi) hMapSmul
          _ = (1 / 2 : ℂ) • (((F1 - F0) ⊗ₗ idB) S.psi) := by
                  simp
      have hMapSub :
          ((F1 - F0) ⊗ₗ idB) = (F1 ⊗ₗ idB) - (F0 ⊗ₗ idB) := by
        ext x y
        simp [sub_eq_add_neg, TensorProduct.map_tmul, TensorProduct.add_tmul, TensorProduct.neg_tmul]
      have hMapSubApply :
          (((F1 - F0) ⊗ₗ idB) S.psi)
            = ((F1 ⊗ₗ idB) S.psi) - ((F0 ⊗ₗ idB) S.psi) := by
        simp [hMapSub]
      have hDeltaNorm :
          ‖((Δ ⊗ₗ idB) S.psi)‖ ≤ ‖((C ⊗ₗ idB) S.psi)‖ := by
        calc
          ‖((Δ ⊗ₗ idB) S.psi)‖
              = ‖((1 / 2 : ℂ) • (((F1 - F0) ⊗ₗ idB) S.psi))‖ := by
                    simpa using congrArg (fun z => ‖z‖) hEq
          _ = ‖(1 / 2 : ℂ)‖ * ‖(((F1 - F0) ⊗ₗ idB) S.psi)‖ := by
                rw [norm_smul]
          _ = (1 / 2 : ℝ) * ‖(((F1 - F0) ⊗ₗ idB) S.psi)‖ := by
                norm_num
          _ = (1 / 2 : ℝ) * ‖((F1 ⊗ₗ idB) S.psi - (F0 ⊗ₗ idB) S.psi)‖ := by
                rw [hMapSubApply]
          _ ≤ (1 / 2 : ℝ) * (‖((F1 ⊗ₗ idB) S.psi)‖ + ‖((F0 ⊗ₗ idB) S.psi)‖) := by
                gcongr
                exact norm_sub_le _ _
          _ = ‖((C ⊗ₗ idB) S.psi)‖ := by
                rw [hF1norm, hF0norm]
                ring
      have habs : |‖((Δ ⊗ₗ idB) S.psi)‖| ≤ |‖((C ⊗ₗ idB) S.psi)‖| := by
        simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using hDeltaNorm
      exact (sq_le_sq).2 habs
    exact hSq

  have hGoalRewritten :
      ‖(((((pauliX ⊗ₗ idA) ∘ₗ V_A) - (V_A ∘ₗ S.A1)) ⊗ₗ idB) S.psi)‖ ^ 2
        ≤ cConst * epsilon := by
    exact le_trans hDelta_le_C hCbound

  simpa [Δ, V_A, idA, idB] using hGoalRewritten


end ApproximateAnticomm

section PauliRelations

variable {H_A H_B : Type*}
variable [NormedAddCommGroup H_A] [NormedAddCommGroup H_B]
variable [InnerProductSpace ℂ H_A] [InnerProductSpace ℂ H_B]
variable [FiniteDimensional ℂ H_A] [FiniteDimensional ℂ H_B]
variable (S : CHSHStrategy H_A H_B)
variable (epsilon : Real)

-- Notation matching `Approximate_Rigidity/Isometries.lean`.
local notation "V_A" => VA (H := H_A) S.A0 S.A1
local notation "V_B" => VB (H := H_B) S.B0 S.B1

private lemma norm_le_sqrt_of_sq_le
    {E : Type*} [NormedAddCommGroup E]
    {x : E} {r : Real} (h : ‖x‖ ^ 2 ≤ r) :
    ‖x‖ ≤ Real.sqrt r := by
  have hr : 0 ≤ r := le_trans (sq_nonneg ‖x‖) h
  have hsqrt : Real.sqrt (‖x‖ ^ 2) ≤ Real.sqrt r := Real.sqrt_le_sqrt h
  have hx : Real.sqrt (‖x‖ ^ 2) = ‖x‖ := by
    simpa using (Real.sqrt_sq_eq_abs ‖x‖)
  simpa [hx] using hsqrt

set_option maxHeartbeats 800000 in
theorem eq218_A1_approx
    (hBias : chshBias S ≥ (2 * Real.sqrt 2) - epsilon) :
    ‖(((V_A ⊗ₗ V_B) ∘ₗ (S.A1 ⊗ₗ LinearMap.id)) S.psi)
        - ((((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
              (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))) ∘ₗ
            (V_A ⊗ₗ V_B)) S.psi)‖ ≤ Real.sqrt (cConst * epsilon) := by
  let Δ : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) :=
    ((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ∘ₗ V_A) - (V_A ∘ₗ S.A1)
  have hΔsq : ‖((Δ ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi)‖ ^ 2 ≤ cConst * epsilon := by
    simpa [Δ] using (eq216 (S := S) (epsilon := epsilon) hBias)
  have hΔnorm : ‖((Δ ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi)‖ ≤ Real.sqrt (cConst * epsilon) :=
    norm_le_sqrt_of_sq_le hΔsq

  have hLeftMap :
      (V_A ⊗ₗ V_B) ∘ₗ (S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))
        = ((V_A ∘ₗ S.A1) ⊗ₗ V_B) := by
    ext x y
    simp [LinearMap.comp_apply, TensorProduct.map_tmul]
  have hRightMap :
      (((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
          (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))) ∘ₗ
        (V_A ⊗ₗ V_B))
        = ((((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ∘ₗ V_A) ⊗ₗ V_B)) := by
    ext x y
    simp [LinearMap.comp_apply, TensorProduct.map_tmul]
  have hDiff :
      (((V_A ⊗ₗ V_B) ∘ₗ (S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))) S.psi)
        - ((((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
              (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))) ∘ₗ
            (V_A ⊗ₗ V_B)) S.psi)
        = -((Δ ⊗ₗ V_B) S.psi) := by
    let P : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) :=
      ((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ∘ₗ V_A)
    let Q : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) := (V_A ∘ₗ S.A1)
    let a : (Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B) :=
      ((Q ⊗ₗ V_B) S.psi)
    let b : (Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B) :=
      ((P ⊗ₗ V_B) S.psi)
    have hmain :
        (((V_A ⊗ₗ V_B) ∘ₗ (S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))) S.psi)
          - ((((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
                (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))) ∘ₗ
              (V_A ⊗ₗ V_B)) S.psi)
          = a - b := by
      rw [hLeftMap, hRightMap]
    have hΔapply : (Δ ⊗ₗ V_B) S.psi = b - a := by
      have hmap_sub : (Δ ⊗ₗ V_B) = (P ⊗ₗ V_B) - (Q ⊗ₗ V_B) := by
        ext x y
        simp [Δ, P, Q, sub_eq_add_neg, TensorProduct.map_tmul,
          TensorProduct.add_tmul, TensorProduct.neg_tmul]
      calc
        (Δ ⊗ₗ V_B) S.psi = ((P ⊗ₗ V_B) - (Q ⊗ₗ V_B)) S.psi := by rw [hmap_sub]
        _ = b - a := by simp [a, b]
    have hab : a - b = -(b - a) := by
      simp [sub_eq_add_neg, add_comm]
    calc
      (((V_A ⊗ₗ V_B) ∘ₗ (S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))) S.psi)
          - ((((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
                (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))) ∘ₗ
              (V_A ⊗ₗ V_B)) S.psi)
          = a - b := hmain
      _ = -(b - a) := hab
      _ = -((Δ ⊗ₗ V_B) S.psi) := by rw [hΔapply]

  have hVB : Isometry V_B := by
    simpa using (VB_is_isometry (H := H_B) S.B0 S.B1)
  let VBᵢ : H_B →ₗᵢ[ℂ] (Qubit ⊗[ℂ] H_B) :=
    { toLinearMap := V_B
      norm_map' := (AddMonoidHomClass.isometry_iff_norm V_B).1 hVB }
  let idQAᵢ : (Qubit ⊗[ℂ] H_A) →ₗᵢ[ℂ] (Qubit ⊗[ℂ] H_A) := LinearIsometry.id
  have hNorm_idVB (x : (Qubit ⊗[ℂ] H_A) ⊗[ℂ] H_B) :
      ‖(((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ V_B) x)‖ = ‖x‖ := by
    simpa [idQAᵢ, VBᵢ] using
      (TensorProduct.norm_map (𝕜 := ℂ) (f := idQAᵢ) (g := VBᵢ) (x := x))
  have hCompDelta :
      (Δ ⊗ₗ V_B)
        = (((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ V_B) ∘ₗ
            (Δ ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))) := by
    ext x y
    simp [LinearMap.comp_apply, TensorProduct.map_tmul]
  have hNormTransport :
      ‖(Δ ⊗ₗ V_B) S.psi‖ = ‖((Δ ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi)‖ := by
    have happ := congrArg (fun F => F S.psi) hCompDelta
    calc
      ‖(Δ ⊗ₗ V_B) S.psi‖
          =
            ‖(((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ V_B)
              (((Δ ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi)))‖ := by
                simpa [LinearMap.comp_apply] using congrArg (fun z => ‖z‖) happ
      _ = ‖((Δ ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi)‖ := hNorm_idVB _

  calc
    ‖(((V_A ⊗ₗ V_B) ∘ₗ (S.A1 ⊗ₗ LinearMap.id)) S.psi)
        - ((((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
              (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))) ∘ₗ
            (V_A ⊗ₗ V_B)) S.psi)‖
        = ‖-((Δ ⊗ₗ V_B) S.psi)‖ := by
            simpa [LinearMap.id] using congrArg (fun z => ‖z‖) hDiff
    _ = ‖(Δ ⊗ₗ V_B) S.psi‖ := by
          exact norm_neg ((Δ ⊗ₗ V_B) S.psi)
    _ = ‖((Δ ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi)‖ := hNormTransport
    _ ≤ Real.sqrt (cConst * epsilon) := hΔnorm

set_option maxHeartbeats 1200000 in
-- Tensor normalization and map-composition rewrites for Bob's rotated extractor are heartbeat-heavy.
theorem eq220_B1_approx
    (hBias : chshBias S ≥ (2 * Real.sqrt 2) - epsilon)
    :
    ‖(((V_A ⊗ₗ V_B) ∘ₗ ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B1)) S.psi)
        - ((((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ
              (pauliZHZ ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))) ∘ₗ
            (V_A ⊗ₗ V_B)) S.psi)‖ ≤ Real.sqrt (cConst * epsilon) := by
  let idA : H_A →ₗ[ℂ] H_A := LinearMap.id
  let idB : H_B →ₗ[ℂ] H_B := LinearMap.id
  let idQA : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) := LinearMap.id
  let idQB : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B) := LinearMap.id
  let V0 : H_B →ₗ[ℂ] (Qubit ⊗[ℂ] H_B) := VA (H := H_B) S.B0 S.B1
  let RotB : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B) := Rotation ⊗ₗ idB
  let Δ0 : H_B →ₗ[ℂ] (Qubit ⊗[ℂ] H_B) := ((pauliX ⊗ₗ idB) ∘ₗ V0) - (V0 ∘ₗ S.B1)
  let ΔB : H_B →ₗ[ℂ] (Qubit ⊗[ℂ] H_B) := ((pauliZHZ ⊗ₗ idB) ∘ₗ V_B) - (V_B ∘ₗ S.B1)

  let T : CHSHStrategy H_B H_A := swapStrategy (H_A := H_A) (H_B := H_B) S
  have hBiasT : chshBias T ≥ (2 * Real.sqrt 2) - epsilon := by
    simpa [T] using (show chshBias (swapStrategy (H_A := H_A) (H_B := H_B) S)
      ≥ (2 * Real.sqrt 2) - epsilon by
        simpa [chshBias_swap (H_A := H_A) (H_B := H_B) (S := S)] using hBias)

  have hTΔsq :
      ‖((Δ0 ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ((TensorProduct.comm ℂ H_A H_B) S.psi))‖ ^ 2
        ≤ cConst * epsilon := by
    simpa [T, swapStrategy, Δ0, V0] using
      (eq216 (S := T) (epsilon := epsilon) hBiasT)

  have hSwapMap :
      ((Δ0 ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ∘ₗ
          (TensorProduct.comm ℂ H_A H_B).toLinearMap)
        =
      ((TensorProduct.comm ℂ H_A (Qubit ⊗[ℂ] H_B)).toLinearMap ∘ₗ
          ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ Δ0)) := by
    ext x y
    simp [LinearMap.comp_apply, TensorProduct.map_tmul, TensorProduct.comm_tmul]

  have hSwapNorm :
      ‖((Δ0 ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ((TensorProduct.comm ℂ H_A H_B) S.psi))‖
        = ‖(((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ Δ0) S.psi)‖ := by
    have happ := congrArg (fun F => F S.psi) hSwapMap
    calc
      ‖((Δ0 ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ((TensorProduct.comm ℂ H_A H_B) S.psi))‖
          = ‖((TensorProduct.comm ℂ H_A (Qubit ⊗[ℂ] H_B))
              (((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ Δ0) S.psi))‖ := by
                simpa [LinearMap.comp_apply] using congrArg (fun z => ‖z‖) happ
      _ = ‖(((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ Δ0) S.psi)‖ := by
            simp [TensorProduct.norm_comm]

  have hΔ0sq : ‖(((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ Δ0) S.psi)‖ ^ 2 ≤ cConst * epsilon := by
    calc
      ‖(((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ Δ0) S.psi)‖ ^ 2
          = ‖((Δ0 ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ((TensorProduct.comm ℂ H_A H_B) S.psi))‖ ^ 2 := by
              rw [hSwapNorm]
      _ ≤ cConst * epsilon := hTΔsq

  have hAdj : (Rotation.adjoint : Qubit →ₗ[ℂ] Qubit) = Rotation :=
    (Rotation_adjoint : Rotation = Rotation.adjoint).symm
  have hRotAux : (Rotation.adjoint : Qubit →ₗ[ℂ] Qubit) auxState = ket0 := by
    dsimp [auxState]
    rw [hAdj]
    have h :=
      congrArg (fun f : Qubit →ₗ[ℂ] Qubit => f ket0) (Rotation_sq : Rotation ∘ₗ Rotation = LinearMap.id)
    dsimp at h
    exact h
  have hCancel :
      (Rotation.adjoint ⊗ₗ idB) ∘ₗ (embed (H := H_B) auxState)
        = embed (H := H_B) ket0 := by
    ext y
    simp only [embed, TensorProduct.mk_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
      LinearMap.id_apply, idB, hRotAux]
  have hVB : V_B = RotB ∘ₗ V0 := by
    ext y
    have hy0 := congrArg (fun f => f y) hCancel
    dsimp at hy0
    have hy :
        (Rotation.adjoint ⊗ₗ idB) ((embed (H := H_B) auxState) y)
          = (embed (H := H_B) ket0) y := hy0
    simp only [VB, unitaryUB, V0, VA, RotB, LinearMap.comp_apply]
    rw [hy]

  have hRotX :
      (pauliZHZ ⊗ₗ idB) ∘ₗ RotB = RotB ∘ₗ (pauliX ⊗ₗ idB) := by
    have hmap1 :
        (pauliZHZ ⊗ₗ idB) ∘ₗ RotB
          = ((pauliZHZ ∘ₗ Rotation) ⊗ₗ (idB ∘ₗ idB)) := by
      change (pauliZHZ ⊗ₗ idB) ∘ₗ (Rotation ⊗ₗ idB)
          = ((pauliZHZ ∘ₗ Rotation) ⊗ₗ (idB ∘ₗ idB))
      exact (TensorProduct.map_comp (pauliZHZ : Qubit →ₗ[ℂ] Qubit) idB Rotation idB).symm
    have hmap2 :
        RotB ∘ₗ (pauliX ⊗ₗ idB)
          = ((Rotation ∘ₗ pauliX) ⊗ₗ (idB ∘ₗ idB)) := by
      change (Rotation ⊗ₗ idB) ∘ₗ (pauliX ⊗ₗ idB)
          = ((Rotation ∘ₗ pauliX) ⊗ₗ (idB ∘ₗ idB))
      exact (TensorProduct.map_comp (Rotation : Qubit →ₗ[ℂ] Qubit) idB pauliX idB).symm
    have hid : idB ∘ₗ idB = idB := by
      ext z
      simp [idB]
    calc
      (pauliZHZ ⊗ₗ idB) ∘ₗ RotB
          = ((pauliZHZ ∘ₗ Rotation) ⊗ₗ idB) := by rw [hmap1, hid]
      _ = ((Rotation ∘ₗ pauliX) ⊗ₗ idB) := by
            simpa only [pauliZHZ] using congrArg (fun f => f ⊗ₗ idB) (Rotation_pauliX).symm
      _ = RotB ∘ₗ (pauliX ⊗ₗ idB) := by rw [hmap2, hid]

  have hDeltaB_formula : ΔB = RotB ∘ₗ Δ0 := by
    calc
      ΔB = ((pauliZHZ ⊗ₗ idB) ∘ₗ V_B) - (V_B ∘ₗ S.B1) := rfl
      _ = ((pauliZHZ ⊗ₗ idB) ∘ₗ (RotB ∘ₗ V0)) - ((RotB ∘ₗ V0) ∘ₗ S.B1) := by
            rw [hVB]
      _ = (((pauliZHZ ⊗ₗ idB) ∘ₗ RotB) ∘ₗ V0) - (RotB ∘ₗ (V0 ∘ₗ S.B1)) := by
            simp [LinearMap.comp_assoc]
      _ = ((RotB ∘ₗ (pauliX ⊗ₗ idB)) ∘ₗ V0) - (RotB ∘ₗ (V0 ∘ₗ S.B1)) := by
            rw [hRotX]
      _ = (RotB ∘ₗ (((pauliX ⊗ₗ idB) ∘ₗ V0))) - (RotB ∘ₗ (V0 ∘ₗ S.B1)) := by
            simp [LinearMap.comp_assoc]
      _ = RotB ∘ₗ ((((pauliX ⊗ₗ idB) ∘ₗ V0) - (V0 ∘ₗ S.B1))) := by
            simp [LinearMap.comp_sub]
      _ = RotB ∘ₗ Δ0 := by rfl

  have hSymmR : (Rotation : Qubit →ₗ[ℂ] Qubit).IsSymmetric := by
    have hSelfAdj : IsSelfAdjoint (Rotation : Qubit →ₗ[ℂ] Qubit) := by
      refine (LinearMap.isSelfAdjoint_iff' (A := (Rotation : Qubit →ₗ[ℂ] Qubit))).2 ?_
      exact (Rotation_adjoint : Rotation = Rotation.adjoint).symm
    exact (LinearMap.isSymmetric_iff_isSelfAdjoint (A := (Rotation : Qubit →ₗ[ℂ] Qubit))).2 hSelfAdj
  letI : IsBinaryObservable (Rotation : Qubit →ₗ[ℂ] Qubit) :=
    { symm := hSymmR
      sq_one := Rotation_sq }
  have hRotIso : Isometry (Rotation : Qubit →ₗ[ℂ] Qubit) :=
    isometry_of_isBinaryObservable (H := Qubit) (A := (Rotation : Qubit →ₗ[ℂ] Qubit))
  let rotLI : Qubit →ₗᵢ[ℂ] Qubit :=
    { toLinearMap := (Rotation : Qubit →ₗ[ℂ] Qubit)
      norm_map' := (AddMonoidHomClass.isometry_iff_norm (Rotation : Qubit →ₗ[ℂ] Qubit)).1 hRotIso }
  let idBᵢ : H_B →ₗᵢ[ℂ] H_B := LinearIsometry.id
  have hRotBIso : Isometry RotB := by
    have hIso :
        Isometry (fun x => TensorProduct.map rotLI.toLinearMap idBᵢ.toLinearMap x) := by
      simpa [TensorProduct.mapIsometry_apply] using (TensorProduct.mapIsometry rotLI idBᵢ).isometry
    change Isometry (fun x => TensorProduct.map rotLI.toLinearMap idBᵢ.toLinearMap x)
    exact hIso

  let idAᵢ : H_A →ₗᵢ[ℂ] H_A := LinearIsometry.id
  let RotBᵢ : (Qubit ⊗[ℂ] H_B) →ₗᵢ[ℂ] (Qubit ⊗[ℂ] H_B) :=
    { toLinearMap := RotB
      norm_map' := (AddMonoidHomClass.isometry_iff_norm RotB).1 hRotBIso }
  have hNorm_idRot (x : H_A ⊗[ℂ] (Qubit ⊗[ℂ] H_B)) :
      ‖(((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ RotB) x)‖ = ‖x‖ := by
    simpa [idAᵢ, RotBᵢ] using
      (TensorProduct.norm_map (𝕜 := ℂ) (f := idAᵢ) (g := RotBᵢ) (x := x))

  have hCompDeltaB :
      ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ ΔB)
        = (((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ RotB) ∘ₗ
            ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ Δ0)) := by
    have hmap :
        ((idA ∘ₗ idA) ⊗ₗ (RotB ∘ₗ Δ0))
          = ((idA ⊗ₗ RotB) ∘ₗ (idA ⊗ₗ Δ0)) := by
      simpa using (TensorProduct.map_comp idA RotB idA Δ0)
    simpa [idA, hDeltaB_formula] using hmap

  have hΔBsq : ‖(((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ ΔB) S.psi)‖ ^ 2 ≤ cConst * epsilon := by
    have happ := congrArg (fun F => F S.psi) hCompDeltaB
    have hnorm :
        ‖(((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ ΔB) S.psi)‖
          = ‖(((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ Δ0) S.psi)‖ := by
      calc
        ‖(((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ ΔB) S.psi)‖
            = ‖(((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ RotB)
                (((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ Δ0) S.psi))‖ := by
                  simpa [LinearMap.comp_apply] using congrArg (fun z => ‖z‖) happ
        _ = ‖(((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ Δ0) S.psi)‖ := hNorm_idRot _
    calc
      ‖(((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ ΔB) S.psi)‖ ^ 2
          = ‖(((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ Δ0) S.psi)‖ ^ 2 := by rw [hnorm]
      _ ≤ cConst * epsilon := hΔ0sq
  have hΔBnorm : ‖(((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ ΔB) S.psi)‖ ≤ Real.sqrt (cConst * epsilon) :=
    norm_le_sqrt_of_sq_le hΔBsq

  have hLeftMap :
      (V_A ⊗ₗ V_B) ∘ₗ ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B1)
        = (V_A ⊗ₗ (V_B ∘ₗ S.B1)) := by
    ext x y
    simp [LinearMap.comp_apply, TensorProduct.map_tmul]
  have hRightMap :
      (((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ
          (pauliZHZ ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))) ∘ₗ
          (V_A ⊗ₗ V_B))
        = (V_A ⊗ₗ ((pauliZHZ ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ∘ₗ V_B)) := by
    ext x y
    simp [LinearMap.comp_apply, TensorProduct.map_tmul]

  have hDiff :
      (((V_A ⊗ₗ V_B) ∘ₗ ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B1)) S.psi)
        - ((((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ
              (pauliZHZ ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))) ∘ₗ
            (V_A ⊗ₗ V_B)) S.psi)
        = -((V_A ⊗ₗ ΔB) S.psi) := by
    let P : H_B →ₗ[ℂ] (Qubit ⊗[ℂ] H_B) :=
      ((pauliZHZ ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ∘ₗ V_B)
    let Q : H_B →ₗ[ℂ] (Qubit ⊗[ℂ] H_B) := (V_B ∘ₗ S.B1)
    let a : (Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B) := ((V_A ⊗ₗ Q) S.psi)
    let b : (Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B) := ((V_A ⊗ₗ P) S.psi)
    have hmain :
        (((V_A ⊗ₗ V_B) ∘ₗ ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B1)) S.psi)
          - ((((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ
                (pauliZHZ ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))) ∘ₗ
              (V_A ⊗ₗ V_B)) S.psi)
          = a - b := by
      rw [hLeftMap, hRightMap]
    have hΔapply : (V_A ⊗ₗ ΔB) S.psi = b - a := by
      have hmap_sub : (V_A ⊗ₗ ΔB) = (V_A ⊗ₗ P) - (V_A ⊗ₗ Q) := by
        ext x y
        simp [ΔB, P, Q, idB, TensorProduct.map_tmul, TensorProduct.tmul_sub]
      calc
        (V_A ⊗ₗ ΔB) S.psi = ((V_A ⊗ₗ P) - (V_A ⊗ₗ Q)) S.psi := by rw [hmap_sub]
        _ = b - a := by simp [a, b]
    have hab : a - b = -(b - a) := by
      abel
    calc
      (((V_A ⊗ₗ V_B) ∘ₗ ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B1)) S.psi)
          - ((((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ
                (pauliZHZ ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))) ∘ₗ
              (V_A ⊗ₗ V_B)) S.psi)
          = a - b := hmain
      _ = -(b - a) := hab
      _ = -((V_A ⊗ₗ ΔB) S.psi) := by rw [hΔapply]

  have hVA : Isometry V_A := by
    simpa using (VA_is_isometry (H := H_A) S.A0 S.A1)
  let VAᵢ : H_A →ₗᵢ[ℂ] (Qubit ⊗[ℂ] H_A) :=
    { toLinearMap := V_A
      norm_map' := (AddMonoidHomClass.isometry_iff_norm V_A).1 hVA }
  let idQBᵢ : (Qubit ⊗[ℂ] H_B) →ₗᵢ[ℂ] (Qubit ⊗[ℂ] H_B) := LinearIsometry.id
  have hNormVA_id (x : H_A ⊗[ℂ] (Qubit ⊗[ℂ] H_B)) :
      ‖((V_A ⊗ₗ (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))) x)‖ = ‖x‖ := by
    simpa [VAᵢ, idQBᵢ] using
      (TensorProduct.norm_map (𝕜 := ℂ) (f := VAᵢ) (g := idQBᵢ) (x := x))
  have hCompVA :
      (V_A ⊗ₗ ΔB)
        = ((V_A ⊗ₗ (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))) ∘ₗ
            ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ ΔB)) := by
    ext x y
    simp [LinearMap.comp_apply, TensorProduct.map_tmul]
  have hNormTransport :
      ‖(V_A ⊗ₗ ΔB) S.psi‖ = ‖(((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ ΔB) S.psi)‖ := by
    have happ := congrArg (fun F => F S.psi) hCompVA
    calc
      ‖(V_A ⊗ₗ ΔB) S.psi‖
          = ‖((V_A ⊗ₗ (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B)))
              ((((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ ΔB) S.psi)))‖ := by
                simpa [LinearMap.comp_apply] using congrArg (fun z => ‖z‖) happ
      _ = ‖(((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ ΔB) S.psi)‖ := hNormVA_id _

  calc
    ‖(((V_A ⊗ₗ V_B) ∘ₗ ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B1)) S.psi)
        - ((((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ
              (pauliZHZ ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))) ∘ₗ
            (V_A ⊗ₗ V_B)) S.psi)‖
        = ‖-((V_A ⊗ₗ ΔB) S.psi)‖ := by
            simpa [LinearMap.id] using congrArg (fun z => ‖z‖) hDiff
    _ = ‖(V_A ⊗ₗ ΔB) S.psi‖ := by exact norm_neg ((V_A ⊗ₗ ΔB) S.psi)
    _ = ‖(((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ ΔB) S.psi)‖ := hNormTransport
    _ ≤ Real.sqrt (cConst * epsilon) := hΔBnorm

end PauliRelations

end

end Approximate_Rigidity
