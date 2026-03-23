import Quantum.Pauli
import Approximate_Rigidity.BasicDefs

import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.LinearAlgebra.Basis.Basic

open scoped TensorProduct Pauli InnerProductSpace ComplexConjugate
open Quantum

namespace Approximate_Rigidity

open Module


/-!
Construction of local isometries and extracted Pauli relations.

This file mirrors Sections 11.3.1-11.3.2 of the notes.
-/

section IsometryConstruction
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-!
Auxiliary ancilla state for Bob.

Following Part II of `theorem11_1_proof_modified_ub.md`, we use
`|aux⟩ := R |0⟩` where `R = sin(π/8) X + cos(π/8) Z` (implemented as `Rotation`).
-/

noncomputable def auxState : Qubit := Rotation ket0

-- Embedding `S_aux = |aux⟩ ⊗ I` (and in particular `S = |0⟩ ⊗ I` for Alice).
noncomputable def embed (aux : Qubit) : H →ₗ[ℂ] (Qubit ⊗[ℂ] H) :=
  (TensorProduct.mk ℂ Qubit H) aux


noncomputable def control (A : H →ₗ[ℂ] H) :
    (Qubit ⊗[ℂ] H) →ₗ[ℂ] (Qubit ⊗[ℂ] H) :=
  -- Projectors `|0⟩⟨0|` and `|1⟩⟨1|` on the control qubit.
  -- Controlled gate: `(|0⟩⟨0| ⊗ I) + (|1⟩⟨1| ⊗ A)`.
  (proj0 ⊗ₗ (LinearMap.id : H →ₗ[ℂ] H)) + (proj1 ⊗ₗ A)




/- Canonical form unitaries built from Alice/Bob observables.-/
noncomputable def unitaryUA (A0 A1 : H →ₗ[ℂ] H) :
    (Qubit ⊗[ℂ] H) →ₗ[ℂ] (Qubit ⊗[ℂ] H) :=
  (control A1) ∘ₗ (Hadamard ⊗ₗ LinearMap.id) ∘ₗ (control A0) ∘ₗ (Hadamard ⊗ₗ LinearMap.id)

noncomputable def VA (A0 A1 : H →ₗ[ℂ] H) :
    H →ₗ[ℂ] (Qubit ⊗[ℂ] H) :=
  (unitaryUA A0 A1).comp (embed ket0)


/-!
Bob's unitary in canonical form (rewritten to match the convention
`(B0,B1) = (H,H')` in the notes):

`U_B := (R ⊗ I) · U_A(B0, B1) · (R† ⊗ I)` where `R = sin(π/8) X + cos(π/8) Z`.

This choice ensures that, with the embedding `S_aux = |aux⟩ ⊗ I` where `|aux⟩ = R|0⟩`,
the extracted action on `B0` is exact.
-/
noncomputable def unitaryUB (B0 B1 : H →ₗ[ℂ] H) :
    (Qubit ⊗[ℂ] H) →ₗ[ℂ] (Qubit ⊗[ℂ] H) :=
  (Rotation ⊗ₗ (LinearMap.id : H →ₗ[ℂ] H)) ∘ₗ
    (unitaryUA B0 B1) ∘ₗ
    (Rotation.adjoint ⊗ₗ (LinearMap.id : H →ₗ[ℂ] H))

noncomputable def VB (B0 B1 : H →ₗ[ℂ] H) :
    H →ₗ[ℂ] (Qubit ⊗[ℂ] H) :=
  (unitaryUB B0 B1).comp (embed auxState)

section IsometryLemmas

theorem embed_is_isometry (aux : Qubit) (haux : ‖aux‖ = 1) :
    Isometry (embed (H := H) aux) := by
  refine (AddMonoidHomClass.isometry_iff_norm (embed (H := H) aux)).2 ?_
  intro x
  -- `‖aux ⊗ x‖ = ‖aux‖ * ‖x‖`.
  simp [embed, TensorProduct.norm_tmul, haux]

lemma PauliZ_is_isometry : Isometry (pauliZ : Qubit →ₗ[ℂ] Qubit) := by
  simpa using
    (isometry_of_adjoint_eq_self_and_sq_one
      (H := Qubit)
      (A := (pauliZ : Qubit →ₗ[ℂ] Qubit))
      (hAdj := pauliZ_adjoint)
      (hSq := pauliZ_sq))

lemma PauliX_is_isometry : Isometry (pauliX : Qubit →ₗ[ℂ] Qubit) := by
  simpa using
    (isometry_of_adjoint_eq_self_and_sq_one
      (H := Qubit)
      (A := (pauliX : Qubit →ₗ[ℂ] Qubit))
      (hAdj := pauliX_adjoint)
      (hSq := pauliX_sq))

private lemma Hadamard_is_isometry : Isometry (Hadamard : Qubit →ₗ[ℂ] Qubit) := by
  simpa using
    (isometry_of_adjoint_eq_self_and_sq_one
      (H := Qubit)
      (A := (Hadamard : Qubit →ₗ[ℂ] Qubit))
      (hAdj := Hadamard_adjoint)
      (hSq := Hadamard_sq))

private lemma Hadamard_tensor_is_isometry :
    Isometry (Hadamard ⊗ₗ (LinearMap.id : H →ₗ[ℂ] H) :
      (Qubit ⊗[ℂ] H) →ₗ[ℂ] (Qubit ⊗[ℂ] H)) := by
  simpa using
    (tensor_map_isometry
      (f := (Hadamard : Qubit →ₗ[ℂ] Qubit))
      (g := (LinearMap.id : H →ₗ[ℂ] H))
      Hadamard_is_isometry
      linearMap_id_isometry)

private lemma Rotation_is_isometry : Isometry (Rotation : Qubit →ₗ[ℂ] Qubit) := by
  exact
    (isometry_of_adjoint_eq_self_and_sq_one
      (H := Qubit)
      (A := (Rotation : Qubit →ₗ[ℂ] Qubit))
      (hAdj := (Rotation_adjoint : Rotation = Rotation.adjoint).symm)
      (hSq := Rotation_sq))

private lemma Rotation_tensor_is_isometry :
    Isometry (Rotation ⊗ₗ (LinearMap.id : H →ₗ[ℂ] H) :
      (Qubit ⊗[ℂ] H) →ₗ[ℂ] (Qubit ⊗[ℂ] H)) := by
  exact
    (tensor_map_isometry
      (f := (Rotation : Qubit →ₗ[ℂ] Qubit))
      (g := (LinearMap.id : H →ₗ[ℂ] H))
      Rotation_is_isometry
      linearMap_id_isometry)

private lemma control_is_isometry (A : H →ₗ[ℂ] H) (hA : Isometry A) :
    Isometry (control (H := H) A) := by
  classical
  refine (AddMonoidHomClass.isometry_iff_norm (control (H := H) A)).2 ?_
  intro x
  -- Decompose `x = |0⟩ ⊗ x0 + |1⟩ ⊗ x1`.
  let b : Basis (Fin 2) ℂ Qubit := (EuclideanSpace.basisFun (ι := Fin 2) (𝕜 := ℂ)).toBasis
  obtain ⟨ηF, hx⟩ := TensorProduct.eq_repr_basis_left (ℬ := b) (x := x)
  have hx' : (∑ i : Fin 2, (b i) ⊗ₜ[ℂ] (ηF i)) = x := by
    simpa [Finsupp.sum_fintype] using hx
  set x0 : H := ηF 0
  set x1 : H := ηF 1
  have hx2 : (ket0 ⊗ₜ[ℂ] x0 + ket1 ⊗ₜ[ℂ] x1) = x := by
    have hb0 : b 0 = ket0 := by simp [b, EuclideanSpace.basisFun_apply, ket0]
    have hb1 : b 1 = ket1 := by simp [b, EuclideanSpace.basisFun_apply, ket1]
    simpa [x0, x1, hb0, hb1, Fin.sum_univ_two, add_comm, add_left_comm, add_assoc] using hx'
  have hcontrol :
      control (H := H) A x = (ket0 ⊗ₜ[ℂ] x0 + ket1 ⊗ₜ[ℂ] (A x1)) := by
    calc
      control (H := H) A x
          = control (H := H) A (ket0 ⊗ₜ[ℂ] x0 + ket1 ⊗ₜ[ℂ] x1) := by simp [hx2]
      _ = (ket0 ⊗ₜ[ℂ] x0 + ket1 ⊗ₜ[ℂ] (A x1)) := by
            simp [control, LinearMap.map_add, TensorProduct.map_tmul, LinearMap.id_apply,
              proj0_ket0, proj1_ket0, proj0_ket1, proj1_ket1, LinearMap.add_apply, add_comm]
  have hpyth (u v : H) :
      ‖ket0 ⊗ₜ[ℂ] u + ket1 ⊗ₜ[ℂ] v‖ * ‖ket0 ⊗ₜ[ℂ] u + ket1 ⊗ₜ[ℂ] v‖ =
        ‖u‖ * ‖u‖ + ‖v‖ * ‖v‖ := by
    have horth : ⟪ket0 ⊗ₜ[ℂ] u, ket1 ⊗ₜ[ℂ] v⟫_ℂ = 0 := by simp [TensorProduct.inner_tmul]
    simpa [TensorProduct.norm_tmul, ket0, ket1] using
      (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
        (x := ket0 ⊗ₜ[ℂ] u) (y := ket1 ⊗ₜ[ℂ] v) horth)
  have hA_norm : ∀ z, ‖A z‖ = ‖z‖ := (AddMonoidHomClass.isometry_iff_norm A).1 hA
  have hmul : ‖control (H := H) A x‖ * ‖control (H := H) A x‖ = ‖x‖ * ‖x‖ := by
    have hx_mul : ‖x‖ * ‖x‖ = ‖x0‖ * ‖x0‖ + ‖x1‖ * ‖x1‖ := by
      simpa [hx2] using (hpyth x0 x1)
    calc
      ‖control (H := H) A x‖ * ‖control (H := H) A x‖
          = ‖x0‖ * ‖x0‖ + ‖A x1‖ * ‖A x1‖ := by simpa [hcontrol] using (hpyth x0 (A x1))
      _ = ‖x0‖ * ‖x0‖ + ‖x1‖ * ‖x1‖ := by simp [hA_norm]
      _ = ‖x‖ * ‖x‖ := hx_mul.symm
  have := congrArg Real.sqrt hmul
  simpa [Real.sqrt_mul_self (norm_nonneg _)] using this

theorem unitaryUA_is_isometry (A0 A1 : H →ₗ[ℂ] H) [IsBinaryObservable A0] [IsBinaryObservable A1] :
    Isometry (unitaryUA A0 A1) := by
  -- `unitaryU` is a composition of four isometries.
  have hA0 : Isometry A0 := isometry_of_isBinaryObservable (H := H) (A := A0)
  have hA1 : Isometry A1 := isometry_of_isBinaryObservable (H := H) (A := A1)
  have hCtrl0 : Isometry (control (H := H) A0) := control_is_isometry (H := H) (A := A0) hA0
  have hCtrl1 : Isometry (control (H := H) A1) := control_is_isometry (H := H) (A := A1) hA1
  have hHad : Isometry
      (Hadamard ⊗ₗ (LinearMap.id : H →ₗ[ℂ] H) :
        (Qubit ⊗[ℂ] H) →ₗ[ℂ] (Qubit ⊗[ℂ] H)) :=
    Hadamard_tensor_is_isometry (H := H)
  -- Compose in the same order as `unitaryUA`.
  simpa [unitaryUA, LinearMap.comp_apply] using (hCtrl1.comp (hHad.comp (hCtrl0.comp hHad)))

theorem VA_is_isometry (A0 A1 : H →ₗ[ℂ] H) [IsBinaryObservable A0] [IsBinaryObservable A1] :
    Isometry (VA (H := H) A0 A1) := by
  have hU : Isometry (unitaryUA A0 A1) := unitaryUA_is_isometry (H := H) A0 A1
  have hE : Isometry (embed (H := H) ket0) := embed_is_isometry (H := H) ket0 (by
    -- `ket0` is a unit vector in `EuclideanSpace`.
    simp [ket0])
  simpa [VA, LinearMap.comp_apply] using (hU.comp hE)

theorem unitaryUB_is_isometry (B0 B1 : H →ₗ[ℂ] H) [IsBinaryObservable B0] [IsBinaryObservable B1] :
    Isometry (unitaryUB B0 B1) := by
  have hU : Isometry (unitaryUA B0 B1) := unitaryUA_is_isometry (H := H) B0 B1
  have hRot : Isometry
      (Rotation ⊗ₗ (LinearMap.id : H →ₗ[ℂ] H) :
        (Qubit ⊗[ℂ] H) →ₗ[ℂ] (Qubit ⊗[ℂ] H)) :=
    Rotation_tensor_is_isometry (H := H)
  have hRotAdj : Isometry
      (Rotation.adjoint ⊗ₗ (LinearMap.id : H →ₗ[ℂ] H) :
        (Qubit ⊗[ℂ] H) →ₗ[ℂ] (Qubit ⊗[ℂ] H)) := by
    rw [← (Rotation_adjoint : Rotation = Rotation.adjoint)]
    exact hRot
  dsimp [unitaryUB]
  exact (hRot.comp (hU.comp hRotAdj))

theorem VB_is_isometry (B0 B1 : H →ₗ[ℂ] H) [IsBinaryObservable B0] [IsBinaryObservable B1] :
    Isometry (VB (H := H) B0 B1) := by
  have hU : Isometry (unitaryUB B0 B1) := unitaryUB_is_isometry (H := H) B0 B1
  have hRot : Isometry (Rotation : Qubit →ₗ[ℂ] Qubit) := Rotation_is_isometry
  have hAux : ‖(auxState : Qubit)‖ = 1 := by
    have hRotNorm : ∀ z : Qubit, ‖Rotation z‖ = ‖z‖ :=
      (AddMonoidHomClass.isometry_iff_norm (Rotation : Qubit →ₗ[ℂ] Qubit)).1 hRot
    dsimp [auxState]
    calc
      ‖Rotation ket0‖ = ‖ket0‖ := hRotNorm ket0
      _ = 1 := by simp [ket0]
  have hE : Isometry (embed (H := H) auxState) := embed_is_isometry (H := H) auxState hAux
  simpa [VB, LinearMap.comp_apply] using (hU.comp hE)

end IsometryLemmas

end IsometryConstruction

section PauliRelations

variable {H_A H_B : Type*}
variable [NormedAddCommGroup H_A] [NormedAddCommGroup H_B]
variable [InnerProductSpace ℂ H_A] [InnerProductSpace ℂ H_B]
variable (S : CHSHStrategy H_A H_B)
variable (epsilon : Real)

-- Notation matching the notes: the local isometries built from the strategy.
local notation "V_A" => VA (H := H_A) S.A0 S.A1
local notation "V_B" => VB (H := H_B) S.B0 S.B1

private lemma isometryVA_intertwine_A0 (A0 A1 : H_A →ₗ[ℂ] H_A)
    [IsBinaryObservable A0] [IsBinaryObservable A1] :
    ((VA (H := H_A) A0 A1) ∘ₗ A0) =
      (pauliZ ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ∘ₗ
        (VA (H := H_A) A0 A1) := by
  ext x
  let V : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) := VA (H := H_A) A0 A1
  let s : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  have hsq : A0 (A0 x) = x := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun f => f x) (IsBinaryObservable.sq_one (A := A0))
  have hV (y : H_A) :
      V y =
        (s * s) • ((ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] (A1 y)) +
          (ket0 ⊗ₜ[ℂ] (A0 y) - ket1 ⊗ₜ[ℂ] (A1 (A0 y)))) := by
    let idA : H_A →ₗ[ℂ] H_A := LinearMap.id
    let hadT : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) := Hadamard ⊗ₗ idA
    have hadT_ket0 (u : H_A) :
        hadT (ket0 ⊗ₜ[ℂ] u) = s • (ket0 ⊗ₜ[ℂ] u + ket1 ⊗ₜ[ℂ] u) := by
      simp [hadT, idA, Hadamard, s, TensorProduct.map_tmul, TensorProduct.smul_tmul,
        TensorProduct.add_tmul, smul_add]
    have hadT_ket1 (u : H_A) :
        hadT (ket1 ⊗ₜ[ℂ] u) = s • (ket0 ⊗ₜ[ℂ] u - ket1 ⊗ₜ[ℂ] u) := by
      simp [sub_eq_add_neg, hadT, idA, Hadamard, s, TensorProduct.map_tmul,
        TensorProduct.smul_tmul, TensorProduct.add_tmul, TensorProduct.neg_tmul,
        smul_add, add_comm]
    have hPre :
        hadT (control (H := H_A) A0 (hadT ((embed (H := H_A) ket0) y))) =
          (s * s) • ((ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] y) +
            (ket0 ⊗ₜ[ℂ] (A0 y) - ket1 ⊗ₜ[ℂ] (A0 y))) := by
      calc
        hadT (control (H := H_A) A0 (hadT ((embed (H := H_A) ket0) y)))
            = hadT (s • (ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] (A0 y))) := by
              simp [embed, hadT_ket0, LinearMap.map_add, control,
                TensorProduct.map_tmul, LinearMap.id_apply, proj0_ket0, proj1_ket0,
                proj0_ket1, proj1_ket1]
        _ = s • hadT (ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] (A0 y)) := by simp
        _ = s • (hadT (ket0 ⊗ₜ[ℂ] y) + hadT (ket1 ⊗ₜ[ℂ] (A0 y))) := by
              simp [LinearMap.map_add]
        _ = s • (s • (ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] y) +
              s • (ket0 ⊗ₜ[ℂ] (A0 y) - ket1 ⊗ₜ[ℂ] (A0 y))) := by
                simp [hadT_ket0, hadT_ket1]
        _ = (s * s) • ((ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] y) +
              (ket0 ⊗ₜ[ℂ] (A0 y) - ket1 ⊗ₜ[ℂ] (A0 y))) := by
                simp [smul_add, smul_sub, smul_smul, add_assoc]
    have hCtrl1 :
        control (H := H_A) A1 (hadT (control (H := H_A) A0 (hadT ((embed (H := H_A) ket0) y))))
          =
          (s * s) • ((ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] (A1 y)) +
            (ket0 ⊗ₜ[ℂ] (A0 y) - ket1 ⊗ₜ[ℂ] (A1 (A0 y)))) := by
      calc
        control (H := H_A) A1 (hadT (control (H := H_A) A0 (hadT ((embed (H := H_A) ket0) y))))
            =
            control (H := H_A) A1
              ((s * s) • ((ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] y) +
                (ket0 ⊗ₜ[ℂ] (A0 y) - ket1 ⊗ₜ[ℂ] (A0 y)))) := by
                simp [hPre]
        _ =
            (s * s) •
              control (H := H_A) A1
                ((ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] y) +
                  (ket0 ⊗ₜ[ℂ] (A0 y) - ket1 ⊗ₜ[ℂ] (A0 y))) := by
                simp
        _ =
            (s * s) • ((ket0 ⊗ₜ[ℂ] y + ket1 ⊗ₜ[ℂ] (A1 y)) +
              (ket0 ⊗ₜ[ℂ] (A0 y) - ket1 ⊗ₜ[ℂ] (A1 (A0 y)))) := by
                simp [LinearMap.map_add, control, TensorProduct.map_tmul,
                  LinearMap.id_apply, proj0_ket0, proj1_ket0, proj0_ket1,
                  proj1_ket1, sub_eq_add_neg, add_assoc, add_left_comm]
    simpa [V, VA, unitaryUA, hadT, idA, LinearMap.comp_apply] using hCtrl1

  calc
    V (A0 x)
        = (s * s) • ((ket0 ⊗ₜ[ℂ] (A0 x) + ket1 ⊗ₜ[ℂ] (A1 (A0 x))) +
            (ket0 ⊗ₜ[ℂ] x - ket1 ⊗ₜ[ℂ] (A1 x))) := by
          simp [hV, hsq]
    _ = (s * s) • ((ket0 ⊗ₜ[ℂ] x - ket1 ⊗ₜ[ℂ] (A1 x)) +
          (ket0 ⊗ₜ[ℂ] (A0 x) + ket1 ⊗ₜ[ℂ] (A1 (A0 x)))) := by
          refine congrArg (fun t => (s * s) • t) ?_
          simpa using
            (add_comm
              (ket0 ⊗ₜ[ℂ] (A0 x) + ket1 ⊗ₜ[ℂ] (A1 (A0 x)))
              (ket0 ⊗ₜ[ℂ] x - ket1 ⊗ₜ[ℂ] (A1 x)))
    _ = (pauliZ ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) (V x) := by
          have hmap :
              (pauliZ ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) (V x) =
                (s * s) • ((ket0 ⊗ₜ[ℂ] x - ket1 ⊗ₜ[ℂ] (A1 x)) +
                  (ket0 ⊗ₜ[ℂ] (A0 x) + ket1 ⊗ₜ[ℂ] (A1 (A0 x)))) := by
            rw [hV]
            simp [LinearMap.map_add, TensorProduct.map_tmul, TensorProduct.neg_tmul,
              LinearMap.id_apply, pauliZ_ket0, pauliZ_ket1, sub_eq_add_neg]
          simpa using hmap.symm


private lemma VA_intertwine_A0 :
    V_A ∘ₗ S.A0 =
      (pauliZ ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ∘ₗ V_A := by
  simpa [VA] using
    (isometryVA_intertwine_A0 (H_A := H_A) (A0 := S.A0) (A1 := S.A1))

private lemma VB_intertwine_B0 :
    V_B ∘ₗ S.B0 =
      (Hadamard ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ∘ₗ V_B := by
  classical
  let idB : H_B →ₗ[ℂ] H_B := LinearMap.id
  let V0 : H_B →ₗ[ℂ] (Qubit ⊗[ℂ] H_B) := VA (H := H_B) S.B0 S.B1
  have hV0 : V0 ∘ₗ S.B0 = (pauliZ ⊗ₗ idB) ∘ₗ V0 := by
    simpa [V0, idB] using
      (isometryVA_intertwine_A0 (H_A := H_B) (A0 := S.B0) (A1 := S.B1))
  have hRotAux : (Rotation.adjoint : Qubit →ₗ[ℂ] Qubit) auxState = ket0 := by
    dsimp [auxState]
    rw [(Rotation_adjoint : Rotation = Rotation.adjoint).symm]
    have h :=
      congrArg (fun f : Qubit →ₗ[ℂ] Qubit => f ket0)
        (Rotation_sq : Rotation ∘ₗ Rotation = LinearMap.id)
    dsimp at h
    exact h
  have hVB :
      V_B = (Rotation ⊗ₗ idB) ∘ₗ V0 := by
    ext y
    simp only [VB, unitaryUB, V0, VA, LinearMap.comp_apply, embed,
      TensorProduct.mk_apply, TensorProduct.map_tmul, LinearMap.id_apply, idB, hRotAux]
  have hid : idB ∘ₗ idB = idB := by
    ext z
    simp [idB]
  have hmapR :
      (Rotation ⊗ₗ idB) ∘ₗ (pauliZ ⊗ₗ idB) =
        ((Rotation ∘ₗ pauliZ) ⊗ₗ idB) := by
    have hmap :
        (Rotation ⊗ₗ idB) ∘ₗ (pauliZ ⊗ₗ idB) =
          ((Rotation ∘ₗ pauliZ) ⊗ₗ (idB ∘ₗ idB)) := by
      exact
        (TensorProduct.map_comp (Rotation : Qubit →ₗ[ℂ] Qubit) idB pauliZ idB).symm
    rw [hmap, hid]
  have hmapH :
      (Hadamard ⊗ₗ idB) ∘ₗ (Rotation ⊗ₗ idB) =
        ((Hadamard ∘ₗ Rotation) ⊗ₗ idB) := by
    have hmap :
        (Hadamard ⊗ₗ idB) ∘ₗ (Rotation ⊗ₗ idB) =
          ((Hadamard ∘ₗ Rotation) ⊗ₗ (idB ∘ₗ idB)) := by
      exact
        (TensorProduct.map_comp (Hadamard : Qubit →ₗ[ℂ] Qubit) idB Rotation idB).symm
    rw [hmap, hid]
  calc
    V_B ∘ₗ S.B0
        = (Rotation ⊗ₗ idB) ∘ₗ ((pauliZ ⊗ₗ idB) ∘ₗ V0) := by
            rw [hVB, LinearMap.comp_assoc, hV0]
    _ = (((Rotation ∘ₗ pauliZ) ⊗ₗ idB) ∘ₗ V0) := by
            rw [← LinearMap.comp_assoc, hmapR]
    _ = (((Hadamard ∘ₗ Rotation) ⊗ₗ idB) ∘ₗ V0) := by
            rw [Rotation_pauliZ]
    _ = (((Hadamard ⊗ₗ idB) ∘ₗ (Rotation ⊗ₗ idB)) ∘ₗ V0) := by
            rw [hmapH]
    _ = (Hadamard ⊗ₗ idB) ∘ₗ ((Rotation ⊗ₗ idB) ∘ₗ V0) := by
            rw [LinearMap.comp_assoc]
    _ = (Hadamard ⊗ₗ idB) ∘ₗ V_B := by
            rw [hVB]


lemma eq217_A0 :
    ((V_A ⊗ₗ V_B) ∘ₗ (S.A0 ⊗ₗ LinearMap.id)) =
      (((pauliZ ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
            (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))) ∘ₗ (V_A ⊗ₗ V_B)) := by
  classical
  ext x y
  -- Reduce to the `V_A` intertwining relation.
  have hVAx :
      V_A (S.A0 x) =
        (pauliZ ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) (V_A x) := by
    simpa [LinearMap.comp_apply] using congrArg (fun f => f x) (VA_intertwine_A0 (S := S))
  simp [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, hVAx]

theorem eq217_A0_exact (φ : H_A ⊗[ℂ] H_B) :
    ‖(((V_A ⊗ₗ V_B) ∘ₗ (S.A0 ⊗ₗ LinearMap.id)) φ)
        - ((((pauliZ ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
              (LinearMap.id)) ∘ₗ (V_A ⊗ₗ V_B)) φ)‖ = 0 := by
  simp [eq217_A0 (S := S)]

-- `eq218_A1_approx` moved to `Approximate_Rigidity/IsometriesApprox.lean`.

lemma eq219_B0 :
    ((V_A ⊗ₗ V_B) ∘ₗ ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B0)) =
      (((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ
            (Hadamard ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))) ∘ₗ (V_A ⊗ₗ V_B)) := by
  classical
  ext x y
  -- Reduce to the `V_B` intertwining relation.
  have hVBy :
      V_B (S.B0 y) =
        (Hadamard ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) (V_B y) := by
    simpa [LinearMap.comp_apply] using
      congrArg (fun f => f y) (VB_intertwine_B0 (S := S))
  simp [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, hVBy]


/-!
`eq219_B0` is a (state-dependent) extracted-operator identity from the notes.

Quantifying this as an exact equality for *all* `φ` is generally too strong: in the robustness proof
we only need it on the distinguished strategy state `S.psi`.
-/
theorem eq219_B0_exact :
    ‖(((V_A ⊗ₗ V_B) ∘ₗ ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B0)) S.psi)
        - ((((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ
              (Hadamard ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))) ∘ₗ (V_A ⊗ₗ V_B)) S.psi)‖ = 0 := by
  simp [eq219_B0 (S := S)]

-- `eq220_B1_approx` moved to `Approximate_Rigidity/IsometriesApprox.lean`.
end PauliRelations

end Approximate_Rigidity
