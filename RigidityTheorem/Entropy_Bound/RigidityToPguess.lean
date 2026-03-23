import Quantum.Density
import Quantum.Qubit
import Entropy_Bound.Infra
import Entropy_Bound.Setup

open scoped TensorProduct InnerProductSpace
open Quantum Entropy_Bound

namespace RigidityToPguess

-- /-! ## Lemma 13: partial trace is contractive for the trace norm -/

-- /--
-- **Blueprint lemma 13** (`lem:partial-trace-contractive`).

-- For any operator `H` on `R ⊗ S`, `‖Tr_S(H)‖₁ ≤ ‖H‖₁`.
-- By `trace_variational`, this equals `sup_{U_R} |Tr((U_R ⊗ I_S) H)| ≤ ‖H‖₁`.
-- -/
-- theorem partial_trace_contractive
--     {R S : Type*} [CpxFiniteHilbert R] [CpxFiniteHilbert S]
--     (H : Operator (R ⊗[ℂ] S)) :
--     traceNorm (Quantum.partialTraceRight (H := R) (K := S) H) ≤ traceNorm H := by
--   rw [trace_variational (Quantum.partialTraceRight H)]
--   apply csSup_le
--   · exact ⟨_, 1, rfl⟩
--   · rintro r ⟨u_R, rfl⟩
--     -- Key identity: Tr(u_R ∘ TrRight(H)) = Tr((u_R ⊗ id_S) ∘ H).
--     -- (This is the right-trace analog of trace_mul_partialTraceLeft.)
--     have hident : trace (((u_R : R →L[ℂ] R) : Operator R) ∘ₗ
--           Quantum.partialTraceRight (H := R) (K := S) H) =
--         trace ((((u_R : R →L[ℂ] R) : Operator R) ⊗ₗ (LinearMap.id : Operator S)) ∘ₗ H) := by
--       -- Right-trace analog of trace_mul_partialTraceLeft.
--       -- Tr(A ∘ TrRight(X)) = Tr((A ⊗ id) ∘ X)
--       let bR : OrthonormalBasis (Fin (Module.finrank ℂ R)) ℂ R := stdOrthonormalBasis ℂ R
--       let bS : OrthonormalBasis (Fin (Module.finrank ℂ S)) ℂ S := stdOrthonormalBasis ℂ S
--       let A := ((u_R : R →L[ℂ] R) : Operator R)
--       calc
--         trace (A ∘ₗ (Quantum.partialTraceRight (H := R) (K := S) H))
--             = trace ((Quantum.partialTraceRight (H := R) (K := S) H) ∘ₗ A) := by
--                 simpa [Module.End.mul_eq_comp] using
--                   (LinearMap.trace_mul_comm ℂ A (Quantum.partialTraceRight (H := R) (K := S) H))
--           _ = ∑ i : Fin (Module.finrank ℂ R),
--                 ⟪bR i, (Quantum.partialTraceRight (H := R) (K := S) H) (A (bR i))⟫_ℂ := by
--                 simpa [trace, bR] using
--                   (LinearMap.trace_eq_sum_inner
--                     (T := ((Quantum.partialTraceRight (H := R) (K := S) H) ∘ₗ A)) (b := bR))
--           _ = ∑ i : Fin (Module.finrank ℂ R),
--                 ∑ j : Fin (Module.finrank ℂ S),
--                   ⟪bR i ⊗ₜ[ℂ] bS j, H (A (bR i) ⊗ₜ[ℂ] bS j)⟫_ℂ := by
--                 refine Finset.sum_congr rfl ?_
--                 intro i _
--                 simp [Quantum.partialTraceRight, bS, inner_sum,
--                   inner_contractRight_eq_inner_tensorRight, tensorRight]
--           _ = ∑ p : (Fin (Module.finrank ℂ R)) × (Fin (Module.finrank ℂ S)),
--                 ⟪bR p.1 ⊗ₜ[ℂ] bS p.2, H (A (bR p.1) ⊗ₜ[ℂ] bS p.2)⟫_ℂ := by
--                 simpa using
--                   (Fintype.sum_prod_type
--                     (f := fun p : (Fin (Module.finrank ℂ R)) × (Fin (Module.finrank ℂ S)) =>
--                       ⟪bR p.1 ⊗ₜ[ℂ] bS p.2, H (A (bR p.1) ⊗ₜ[ℂ] bS p.2)⟫_ℂ)).symm
--           _ = ∑ p : (Fin (Module.finrank ℂ R)) × (Fin (Module.finrank ℂ S)),
--                 ⟪(bR.tensorProduct bS) p,
--                   (H ∘ₗ (A ⊗ₗ (LinearMap.id : Operator S))) ((bR.tensorProduct bS) p)⟫_ℂ := by
--                 refine Finset.sum_congr rfl ?_
--                 intro p _
--                 rcases p with ⟨i, j⟩
--                 simp [OrthonormalBasis.tensorProduct_apply, LinearMap.comp_apply]
--           _ = trace (H ∘ₗ (A ⊗ₗ (LinearMap.id : Operator S))) := by
--                 simpa [trace] using
--                   (LinearMap.trace_eq_sum_inner
--                     (T := (H ∘ₗ (A ⊗ₗ (LinearMap.id : Operator S))))
--                     (b := bR.tensorProduct bS)).symm
--           _ = trace ((A ⊗ₗ (LinearMap.id : Operator S)) ∘ₗ H) := by
--                 simpa [Module.End.mul_eq_comp] using
--                   (LinearMap.trace_mul_comm ℂ H ((A ⊗ₗ (LinearMap.id : Operator S))))
--     rw [hident]
--     -- ‖trace((u_R ⊗ id_S) ∘ H)‖ ≤ traceNorm H.
--     -- Use the eigenbasis argument: (u_R ⊗ id_S) is norm-preserving
--     -- because TensorProduct.norm_map applies.
--     have hT := isHermitian_operatorSqrt_adjoint_mul_self (X := H)
--     let b : OrthonormalBasis (Fin (Module.finrank ℂ (R ⊗[ℂ] S))) ℂ (R ⊗[ℂ] S) :=
--       hT.eigenvectorBasis rfl
--     have htrace :
--         trace ((((u_R : R →L[ℂ] R) : Operator R) ⊗ₗ (LinearMap.id : Operator S)) ∘ₗ H)
--           = ∑ i, ⟪b i,
--               ((((u_R : R →L[ℂ] R) : Operator R) ⊗ₗ (LinearMap.id : Operator S)) ∘ₗ H) (b i)⟫_ℂ := by
--       simp [trace, LinearMap.trace_eq_sum_inner _ b]
--     rw [htrace]
--     -- Package u_R as a linear isometry.
--     let fu : R →ₗᵢ[ℂ] R := {
--       toLinearMap := (u_R : R →L[ℂ] R).toLinearMap
--       norm_map' := fun x => Unitary.norm_map u_R x
--     }
--     -- Show (u_R ⊗ id) equals TensorProduct.map fu id as linear maps.
--     have hmap_eq : (((u_R : R →L[ℂ] R) : Operator R) ⊗ₗ (LinearMap.id : Operator S))
--         = TensorProduct.map fu.toLinearMap LinearIsometry.id.toLinearMap := by
--       simp [fu, LinearIsometry.id]
--     calc ‖∑ i, ⟪b i,
--               ((((u_R : R →L[ℂ] R) : Operator R) ⊗ₗ (LinearMap.id : Operator S)) ∘ₗ H) (b i)⟫_ℂ‖
--         ≤ ∑ i, ‖⟪b i,
--               ((((u_R : R →L[ℂ] R) : Operator R) ⊗ₗ (LinearMap.id : Operator S)) ∘ₗ H) (b i)⟫_ℂ‖ :=
--             norm_sum_le _ _
--       _ ≤ ∑ i, ‖((((u_R : R →L[ℂ] R) : Operator R) ⊗ₗ (LinearMap.id : Operator S)) ∘ₗ H) (b i)‖ := by
--             gcongr with i
--             have hb_norm : ‖b i‖ = 1 := b.orthonormal.1 i
--             have := norm_inner_le_norm (𝕜 := ℂ) (b i)
--               (((((u_R : R →L[ℂ] R) : Operator R) ⊗ₗ (LinearMap.id : Operator S)) ∘ₗ H) (b i))
--             rw [hb_norm, one_mul] at this
--             exact this
--       _ = ∑ i, ‖H (b i)‖ := by
--             congr 1; ext i
--             simp only [LinearMap.comp_apply]
--             -- (u_R ⊗ id)(v) = TensorProduct.map fu id (v), and ‖TensorProduct.map fu id v‖ = ‖v‖.
--             rw [hmap_eq]
--             exact TensorProduct.norm_map fu LinearIsometry.id (H (b i))
--       _ = ∑ i, singularValues H i := by
--             congr 1; ext i
--             exact norm_apply_eigvec_eq_singularValue H i
--       _ = traceNorm H := (traceNorm_eq_sum_singularValues H).symm

-- /--
-- Left-trace version of `partial_trace_contractive`: `‖Tr_R(H)‖₁ ≤ ‖H‖₁`.
-- -/
-- theorem partial_trace_contractive_left
--     {R S : Type*} [CpxFiniteHilbert R] [CpxFiniteHilbert S]
--     (H : Operator (R ⊗[ℂ] S)) :
--     traceNorm (Quantum.partialTraceLeft (H := R) (K := S) H) ≤ traceNorm H := by
--   rw [trace_variational (Quantum.partialTraceLeft H)]
--   apply csSup_le
--   · exact ⟨_, 1, rfl⟩
--   · rintro r ⟨u_S, rfl⟩
--     -- Step 1: Tr(u_S ∘ TrLeft(H)) = Tr((id_R ⊗ u_S) ∘ H) by trace_mul_partialTraceLeft.
--     rw [trace_mul_partialTraceLeft ((u_S : S →L[ℂ] S) : Operator S) H]
--     -- Step 2: ‖trace((id_R ⊗ u_S) ∘ H)‖ ≤ traceNorm H.
--     -- (id_R ⊗ u_S) is norm-preserving (product of isometries), eigenbasis argument.
--     have hT := isHermitian_operatorSqrt_adjoint_mul_self (X := H)
--     let b : OrthonormalBasis (Fin (Module.finrank ℂ (R ⊗[ℂ] S))) ℂ (R ⊗[ℂ] S) :=
--       hT.eigenvectorBasis rfl
--     have htrace :
--         trace (((LinearMap.id : Operator R) ⊗ₗ ((u_S : S →L[ℂ] S) : Operator S)) ∘ₗ H)
--           = ∑ i, ⟪b i,
--               (((LinearMap.id : Operator R) ⊗ₗ ((u_S : S →L[ℂ] S) : Operator S)) ∘ₗ H) (b i)⟫_ℂ := by
--       simp [trace, LinearMap.trace_eq_sum_inner _ b]
--     rw [htrace]
--     -- Package u_S as a linear isometry.
--     let gu : S →ₗᵢ[ℂ] S := {
--       toLinearMap := (u_S : S →L[ℂ] S).toLinearMap
--       norm_map' := fun x => Unitary.norm_map u_S x
--     }
--     -- Show (id ⊗ u_S) equals TensorProduct.map id gu as linear maps.
--     have hmap_eq : ((LinearMap.id : Operator R) ⊗ₗ ((u_S : S →L[ℂ] S) : Operator S))
--         = TensorProduct.map LinearIsometry.id.toLinearMap gu.toLinearMap := by
--       simp [gu, LinearIsometry.id]
--     calc ‖∑ i, ⟪b i,
--               (((LinearMap.id : Operator R) ⊗ₗ ((u_S : S →L[ℂ] S) : Operator S)) ∘ₗ H) (b i)⟫_ℂ‖
--         ≤ ∑ i, ‖⟪b i,
--               (((LinearMap.id : Operator R) ⊗ₗ ((u_S : S →L[ℂ] S) : Operator S)) ∘ₗ H) (b i)⟫_ℂ‖ :=
--             norm_sum_le _ _
--       _ ≤ ∑ i, ‖(((LinearMap.id : Operator R) ⊗ₗ ((u_S : S →L[ℂ] S) : Operator S)) ∘ₗ H) (b i)‖ := by
--             gcongr with i
--             have hb_norm : ‖b i‖ = 1 := b.orthonormal.1 i
--             have := norm_inner_le_norm (𝕜 := ℂ) (b i)
--               ((((LinearMap.id : Operator R) ⊗ₗ ((u_S : S →L[ℂ] S) : Operator S)) ∘ₗ H) (b i))
--             rw [hb_norm, one_mul] at this
--             exact this
--       _ = ∑ i, ‖H (b i)‖ := by
--             congr 1; ext i
--             simp only [LinearMap.comp_apply]
--             rw [hmap_eq]
--             exact TensorProduct.norm_map LinearIsometry.id gu (H (b i))
--       _ = ∑ i, singularValues H i := by
--             congr 1; ext i
--             exact norm_apply_eigvec_eq_singularValue H i
--       _ = traceNorm H := (traceNorm_eq_sum_singularValues H).symm

-- /-! ## Lemma 14: isometries preserve the trace norm -/

-- /--
-- **Blueprint lemma 14** (`lem:isometry-norm`).

-- Let `W : H →ₗ[ℂ] K` be an isometry (`W† ∘ W = id`).
-- Then `‖W ∘ X ∘ W†‖₁ = ‖X‖₁` for all operators `X`.

-- Proof outline:
-- - **Step A** (proved): Gram identity `(WXW†)†(WXW†) = W(X†X)W†`.
-- - **Step B** (proved): CFC commutativity `sqrt(WAW†) = W·sqrt(A)·W†` for `A ≥ 0`.
-- - **Step C** (proved): Trace cyclicity `Tr(W·B·W†) = Tr(B)` via rectangular `trace_comp_comm'`.
-- -/
-- theorem isometry_trace_norm
--     {H K : Type*} [CpxFiniteHilbert H] [CpxFiniteHilbert K]
--     (W : H →ₗ[ℂ] K)
--     (hW : LinearMap.adjoint W ∘ₗ W = LinearMap.id)
--     (X : Operator H) :
--     traceNorm (W ∘ₗ X ∘ₗ LinearMap.adjoint W) = traceNorm X := by
--   -- Step A: Gram identity — (WXW†)†(WXW†) = W(X†X)W†.
--   -- adj(WXW†) = adj(adj W) ∘ adj(X) ∘ adj(W) = W ∘ adj(X) ∘ W†,
--   -- then use W†W = id.
--   have hGram :
--       LinearMap.adjoint (W ∘ₗ X ∘ₗ LinearMap.adjoint W) ∘ₗ
--         (W ∘ₗ X ∘ₗ LinearMap.adjoint W)
--         = W ∘ₗ (LinearMap.adjoint X ∘ₗ X) ∘ₗ LinearMap.adjoint W := by
--     have hadj : LinearMap.adjoint (W ∘ₗ X ∘ₗ LinearMap.adjoint W)
--         = W ∘ₗ LinearMap.adjoint X ∘ₗ LinearMap.adjoint W := by
--       rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
--       simp [LinearMap.comp_assoc]
--     rw [hadj]
--     -- Point-wise: W(adj X (adj W (W (X (adj W v))))) = W(adj X (X (adj W v)));
--     -- the inner adj W (W ?) = ? step uses hW.
--     have hWW : ∀ u, LinearMap.adjoint W (W u) = u := fun u => by
--       have := LinearMap.congr_fun hW u
--       simpa [LinearMap.comp_apply] using this
--     ext v
--     simp only [LinearMap.comp_apply, hWW]
--   -- Step B: operatorSqrt intertwines with isometric conjugation.
--   -- For any A ≥ 0 on H and isometry W : H →ₗ K with W†W = id,
--   -- sqrt(W·A·W†) = W·sqrt(A)·W†.
--   have hSqrt :
--       operatorSqrt (LinearMap.adjoint (W ∘ₗ X ∘ₗ LinearMap.adjoint W) ∘ₗ
--         (W ∘ₗ X ∘ₗ LinearMap.adjoint W))
--         = W ∘ₗ operatorSqrt (LinearMap.adjoint X ∘ₗ X) ∘ₗ LinearMap.adjoint W := by
--     rw [hGram]
--     -- CFC commutativity: operatorSqrt (W ∘ A ∘ adj W) = W ∘ operatorSqrt A ∘ adj W.
--     -- Strategy: use CFC.sqrt_unique: if Tc * Tc = WAW† and 0 ≤ Tc, then sqrt(WAW†) = Tc.
--     let Wc : H →L[ℂ] K := W.toContinuousLinearMap
--     let Ac : H →L[ℂ] H :=
--       LinearMap.toContinuousLinearMap (LinearMap.adjoint X ∘ₗ X)
--     let Sc : H →L[ℂ] H := cfcₙ Real.sqrt Ac
--     let Tc : K →L[ℂ] K := Wc ∘L Sc ∘L Wc.adjoint
--     -- toCLM (adj W) = Wc.adjoint
--     have hAdj : LinearMap.toContinuousLinearMap (LinearMap.adjoint W) = Wc.adjoint :=
--       LinearMap.adjoint_toContinuousLinearMap W
--     -- Wc.adj ∘L Wc = 1 (from hW)
--     have hWcWc : Wc.adjoint ∘L Wc = 1 := by
--       ext v
--       simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]
--       have key : LinearMap.adjoint W (W v) = v := by
--         simpa using LinearMap.congr_fun hW v
--       calc Wc.adjoint (Wc v)
--           = (LinearMap.toContinuousLinearMap (LinearMap.adjoint W)) (W v) := by
--               rw [← hAdj]; rfl
--         _ = LinearMap.adjoint W (W v) := rfl
--         _ = v := key
--     -- Sc ∘L Sc = Ac (from operatorSqrt_comp_self_eq_adjoint_mul)
--     have hScSc : Sc ∘L Sc = Ac := by
--       apply ContinuousLinearMap.coe_inj.mp
--       simp only [ContinuousLinearMap.coe_comp]
--       have h := operatorSqrt_comp_self_eq_adjoint_mul X
--       simp only [operatorSqrt] at h
--       exact h
--     -- 0 ≤ Sc
--     have hSc_nn : (0 : H →L[ℂ] H) ≤ Sc :=
--       cfcₙ_nonneg (fun x _ => Real.sqrt_nonneg x)
--     -- 0 ≤ Tc by conj_adjoint
--     have hTc_nn : (0 : K →L[ℂ] K) ≤ Tc := by
--       rw [ContinuousLinearMap.nonneg_iff_isPositive]
--       exact ((ContinuousLinearMap.nonneg_iff_isPositive Sc).mp hSc_nn).conj_adjoint Wc
--     -- toCLM (W ∘ A ∘ adj W) = Wc ∘L Ac ∘L Wc.adj
--     have hWAW : LinearMap.toContinuousLinearMap
--         (W ∘ₗ (LinearMap.adjoint X ∘ₗ X) ∘ₗ LinearMap.adjoint W) =
--         Wc ∘L Ac ∘L Wc.adjoint := by
--       rw [← hAdj]; rfl
--     -- Tc * Tc = toCLM (W ∘ A ∘ adj W)
--     have hTcSq : Tc * Tc = LinearMap.toContinuousLinearMap
--         (W ∘ₗ (LinearMap.adjoint X ∘ₗ X) ∘ₗ LinearMap.adjoint W) := by
--       rw [hWAW]
--       ext v
--       simp only [Tc, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
--       have hWcWc_app : ∀ u, Wc.adjoint (Wc u) = u := fun u =>
--         DFunLike.congr_fun hWcWc u
--       have hScSc_app : ∀ u, Sc (Sc u) = Ac u := fun u =>
--         DFunLike.congr_fun hScSc u
--       rw [hWcWc_app, hScSc_app]
--     -- 0 ≤ toCLM (W ∘ A ∘ adj W)
--     have hnn : (0 : K →L[ℂ] K) ≤
--         LinearMap.toContinuousLinearMap
--           (W ∘ₗ (LinearMap.adjoint X ∘ₗ X) ∘ₗ LinearMap.adjoint W) := by
--       rw [← hTcSq]
--       have hsa : IsSelfAdjoint Tc :=
--         ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hTc_nn).isSelfAdjoint
--       calc (0 : K →L[ℂ] K) ≤ star Tc * Tc := star_mul_self_nonneg Tc
--         _ = Tc * Tc := by rw [hsa.star_eq]
--     -- CFC sqrt = Tc (via sqrt_unique + sqrt_eq_real_sqrt)
--     have hCFC : cfcₙ Real.sqrt (LinearMap.toContinuousLinearMap
--         (W ∘ₗ (LinearMap.adjoint X ∘ₗ X) ∘ₗ LinearMap.adjoint W)) = Tc := by
--       rw [← CFC.sqrt_eq_real_sqrt _ hnn]
--       exact CFC.sqrt_unique hTcSq hTc_nn
--     -- Convert back to LinearMap level
--     simp only [operatorSqrt]
--     have hRHS : W ∘ₗ (cfcₙ Real.sqrt Ac).toLinearMap ∘ₗ LinearMap.adjoint W =
--         Tc.toLinearMap := by
--       simp only [Tc, ContinuousLinearMap.coe_comp, ← hAdj, LinearMap.coe_toContinuousLinearMap]
--       rfl
--     rw [hRHS, ← hCFC]
--   -- Step C: Trace cyclicity — Tr(W · B · W†) = Tr(B).
--   -- trace_K(W ∘ (B ∘ W†)) = trace_H((B ∘ W†) ∘ W)  [trace_comp_comm']
--   --                        = trace_H(B ∘ (W† ∘ W)) = trace_H(B ∘ id) = trace_H(B).
--   have htrace :
--       trace (W ∘ₗ operatorSqrt (LinearMap.adjoint X ∘ₗ X) ∘ₗ LinearMap.adjoint W)
--         = trace (operatorSqrt (LinearMap.adjoint X ∘ₗ X)) := by
--     let B := operatorSqrt (LinearMap.adjoint X ∘ₗ X)
--     -- Re-associate W ∘ B ∘ W† = W ∘ (B ∘ W†) (definitionally equal via change),
--     -- then swap via trace_comp_comm', then use W†W = id.
--     change LinearMap.trace ℂ K (W ∘ₗ (B ∘ₗ LinearMap.adjoint W)) =
--         LinearMap.trace ℂ H B
--     rw [← LinearMap.trace_comp_comm', LinearMap.comp_assoc W, hW, LinearMap.comp_id]
--   -- Combine A + B + C: traceNorm(WXW†) = Re Tr(W·sqrt(X†X)·W†) = Re Tr(sqrt(X†X)) = traceNorm X.
--   unfold traceNorm
--   rw [hSqrt, htrace]

/-! ### Private helpers for `measure_contract` (Lemma 15) -/

/-- Trace-norm bound for operators with norm ≤ 1: `‖Tr(T ∘ A)‖ ≤ traceNorm A`.
Generalises `norm_trace_unitary_le_traceNorm` from unitaries to contractions. -/
private lemma mc_norm_trace_contraction_le
    {H : Type*} [CpxFiniteHilbert H]
    (T A : Operator H)
    (hT : ∀ v : H, ‖T v‖ ≤ ‖v‖) :
    ‖trace (T ∘ₗ A)‖ ≤ traceNorm A := by
  let hTA := isHermitian_operatorSqrt_adjoint_mul_self (X := A)
  let b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H := hTA.eigenvectorBasis rfl
  have htrace : trace (T ∘ₗ A) = ∑ i, ⟪b i, (T ∘ₗ A) (b i)⟫_ℂ := by
    simp [trace, LinearMap.trace_eq_sum_inner _ b]
  rw [htrace]
  calc ‖∑ i, ⟪b i, (T ∘ₗ A) (b i)⟫_ℂ‖
      ≤ ∑ i, ‖⟪b i, (T ∘ₗ A) (b i)⟫_ℂ‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖(T ∘ₗ A) (b i)‖ := by
          gcongr with i
          have hb : ‖b i‖ = 1 := b.orthonormal.1 i
          calc ‖⟪b i, (T ∘ₗ A) (b i)⟫_ℂ‖
              ≤ ‖b i‖ * ‖(T ∘ₗ A) (b i)‖ := norm_inner_le_norm _ _
            _ = ‖(T ∘ₗ A) (b i)‖ := by rw [hb, one_mul]
    _ ≤ ∑ i, ‖A (b i)‖ := by
          gcongr with i
          simp only [LinearMap.comp_apply]
          exact hT (A (b i))
    _ = ∑ i, singularValues A i := by
          congr 1; ext i; exact norm_apply_eigvec_eq_singularValue A i
    _ = traceNorm A := (traceNorm_eq_sum_singularValues A).symm




/-- `keyProjector x` is idempotent. -/
lemma mc_kP_idem {E : Type} [CpxFiniteHilbert E] (x : Fin 2) :
    keyProjector (E := E) x ∘ₗ keyProjector (E := E) x = keyProjector (E := E) x := by
  apply LinearMap.ext; intro v
  refine TensorProduct.induction_on v ?_ ?_ ?_
  · simp
  · intro ab e
    refine TensorProduct.induction_on ab ?_ ?_ ?_
    · simp
    · intro a b
      simp only [LinearMap.comp_apply, keyProjector_tmul]
      have key : ∀ q : Qubit,
          (if x = 0 then proj0 else proj1) ((if x = 0 then proj0 else proj1) q) =
          (if x = 0 then proj0 else proj1) q := by
        intro q; fin_cases x
        · exact LinearMap.congr_fun proj0_idem q
        · exact LinearMap.congr_fun proj1_idem q
      simp only [key]
    · intro v₁ v₂ h₁ h₂
      simp only [LinearMap.comp_apply] at h₁ h₂ ⊢
      simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
  · intro v₁ v₂ h₁ h₂; simp [map_add, h₁, h₂]

/-- `keyProjector 0 ∘ keyProjector 1 = 0`. -/
private lemma mc_kP_cross {E : Type} [CpxFiniteHilbert E] :
    keyProjector (E := E) 0 ∘ₗ keyProjector (E := E) 1 = 0 := by
  apply LinearMap.ext; intro v
  refine TensorProduct.induction_on v ?_ ?_ ?_
  · simp
  · intro ab e
    refine TensorProduct.induction_on ab ?_ ?_ ?_
    · simp
    · intro a b
      have h01 : (1 : Fin 2) ≠ 0 := Fin.zero_ne_one.symm
      have hpq : proj0 (proj1 a) = 0 := by
        have := LinearMap.congr_fun proj0_proj1_zero a
        simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
        exact this
      simp only [LinearMap.comp_apply, keyProjector_tmul, if_true, if_neg h01,
        LinearMap.zero_apply, hpq, TensorProduct.zero_tmul]
    · intro v₁ v₂ h₁ h₂
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h₁ h₂ ⊢
      simp only [TensorProduct.add_tmul, map_add, h₁, h₂, add_zero]
  · intro v₁ v₂ h₁ h₂
    simp only [LinearMap.zero_apply] at h₁ h₂ ⊢
    simp only [map_add, h₁, h₂, add_zero]

/-- `keyProjector 1 ∘ keyProjector 0 = 0`. -/
private lemma mc_kP_cross' {E : Type} [CpxFiniteHilbert E] :
    keyProjector (E := E) 1 ∘ₗ keyProjector (E := E) 0 = 0 := by
  apply LinearMap.ext; intro v
  refine TensorProduct.induction_on v ?_ ?_ ?_
  · simp
  · intro ab e
    refine TensorProduct.induction_on ab ?_ ?_ ?_
    · simp
    · intro a b
      have h01 : (1 : Fin 2) ≠ 0 := Fin.zero_ne_one.symm
      have hpq : proj1 (proj0 a) = 0 := by
        have := LinearMap.congr_fun proj1_proj0_zero a
        simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
        exact this
      simp only [LinearMap.comp_apply, keyProjector_tmul, if_true, if_neg h01,
        LinearMap.zero_apply, hpq, TensorProduct.zero_tmul]
    · intro v₁ v₂ h₁ h₂
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h₁ h₂ ⊢
      simp only [TensorProduct.add_tmul, map_add, h₁, h₂, add_zero]
  · intro v₁ v₂ h₁ h₂
    simp only [LinearMap.zero_apply] at h₁ h₂ ⊢
    simp only [map_add, h₁, h₂, add_zero]

/-- `∑_x keyProjector x = id`. -/
lemma mc_kP_sum {E : Type} [CpxFiniteHilbert E] :
    ∑ x : Fin 2, keyProjector (E := E) x = LinearMap.id := by
  apply LinearMap.ext; intro v
  simp only [LinearMap.id_apply]
  refine TensorProduct.induction_on v ?_ ?_ ?_
  · simp
  · intro ab e
    refine TensorProduct.induction_on ab ?_ ?_ ?_
    · simp
    · intro a b
      have h01 : (1 : Fin 2) ≠ 0 := Fin.zero_ne_one.symm
      -- Fin.sum_univ_two gives (kP 0 + kP 1) v; LinearMap.add_apply distributes it
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
lemma mc_kP_sa {E : Type} [CpxFiniteHilbert E] (x : Fin 2) :
    LinearMap.adjoint (keyProjector (E := E) x) = keyProjector (E := E) x := by
  apply LinearMap.ext; intro v
  apply ext_inner_right ℂ; intro w
  -- Goal after adjoint_inner_left: ⟪v, kP w⟫ = ⟪kP v, w⟫
  rw [LinearMap.adjoint_inner_left]
  -- Reduce to pure tensors
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
          -- split on the if-condition; split_ifs replaces both branches simultaneously
          split_ifs with hx
          · -- x = 0 branch: proj0
            congr 1; congr 1
            have h := LinearMap.adjoint_inner_left proj0 a' a
            rw [proj0_sa] at h
            exact h.symm
          · -- x ≠ 0 branch: proj1
            congr 1; congr 1
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

/-- `‖keyProjector x v‖ ≤ ‖v‖`. -/
private lemma mc_kP_norm_le {E : Type} [CpxFiniteHilbert E] (x : Fin 2) (v : ABESystem E) :
    ‖keyProjector (E := E) x v‖ ≤ ‖v‖ := by
  set kP := keyProjector (E := E) x
  have hidem : kP (kP v) = kP v := LinearMap.congr_fun (mc_kP_idem x) v
  have hsa : LinearMap.adjoint kP = kP := mc_kP_sa x
  -- adjoint_inner_left A x y : ⟪adjoint A y, x⟫ = ⟪y, A x⟫
  -- With A=kP, x=kP v, y=v: ⟪adjoint kP v, kP v⟫ = ⟪v, kP(kP v)⟫
  -- After hsa and hidem: ⟪kP v, kP v⟫ = ⟪v, kP v⟫
  have hkey : ⟪kP v, kP v⟫_ℂ = ⟪v, kP v⟫_ℂ := by
    have h := LinearMap.adjoint_inner_left kP (kP v) v
    rw [hsa, hidem] at h
    exact h
  have hle : ‖kP v‖ ^ 2 ≤ ‖v‖ * ‖kP v‖ :=
    calc ‖kP v‖ ^ 2
        = Complex.re ⟪kP v, kP v⟫_ℂ := (inner_self_eq_norm_sq (𝕜 := ℂ) (kP v)).symm
      _ = Complex.re ⟪v, kP v⟫_ℂ    := by rw [hkey]
      _ ≤ ‖⟪v, kP v⟫_ℂ‖             := Complex.re_le_norm _
      _ ≤ ‖v‖ * ‖kP v‖               := norm_inner_le_norm _ _
  nlinarith [norm_nonneg (kP v), norm_nonneg v, sq_nonneg (‖v‖ - ‖kP v‖)]

/-- Orthogonality: `⟪kP_x v, kP_y w⟫ = 0` for `x ≠ y`. -/
private lemma mc_kP_orth {E : Type} [CpxFiniteHilbert E] (x y : Fin 2) (v w : ABESystem E)
    (hxy : x ≠ y) :
    ⟪keyProjector (E := E) x v, keyProjector (E := E) y w⟫_ℂ = 0 := by
  have hcross : keyProjector (E := E) y (keyProjector (E := E) x v) = 0 := by
    have : x = 0 ∧ y = 1 ∨ x = 1 ∧ y = 0 := by
      fin_cases x <;> fin_cases y <;> simp_all
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact LinearMap.congr_fun mc_kP_cross' v
    · exact LinearMap.congr_fun mc_kP_cross v
  calc
    ⟪keyProjector (E := E) x v, keyProjector (E := E) y w⟫_ℂ
        = ⟪keyProjector (E := E) y (keyProjector (E := E) x v), w⟫_ℂ := by
            simpa [mc_kP_sa y] using
              (LinearMap.adjoint_inner_left (keyProjector (E := E) y) w
                (keyProjector (E := E) x v)).symm
    _ = ⟪0, w⟫_ℂ := by rw [hcross]
    _ = 0 := by simp

/-- Parseval for `keyProjector`: `∑_x ‖kP_x v‖² = ‖v‖²`. -/
private lemma mc_kP_parseval {E : Type} [CpxFiniteHilbert E] (v : ABESystem E) :
    ∑ x : Fin 2, ‖keyProjector (E := E) x v‖ ^ 2 = ‖v‖ ^ 2 := by
  have hsum := mc_kP_sum (E := E)
  have hdecomp : keyProjector (E := E) 0 v + keyProjector (E := E) 1 v = v := by
    have h := LinearMap.congr_fun hsum v
    simp only [LinearMap.id_apply, Fin.sum_univ_two, LinearMap.add_apply] at h
    exact h
  have horth : ⟪keyProjector (E := E) 0 v, keyProjector (E := E) 1 v⟫_ℂ = 0 :=
    mc_kP_orth 0 1 v v (by decide)
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (keyProjector (E := E) 0 v) (keyProjector (E := E) 1 v) horth
  rw [Fin.sum_univ_two]
  conv_rhs => rw [← hdecomp]
  simp only [sq]
  linarith

/-- `contractLeft (classicalKet x)` is a contraction: `‖cL(cKet_x) w‖ ≤ ‖w‖`. -/
private lemma mc_cL_norm_le {E : Type} [CpxFiniteHilbert E] (x : Fin 2)
    (w : Qubit ⊗[ℂ] E) :
    ‖Quantum.contractLeft (classicalKet (X := Fin 2) x) w‖ ≤ ‖w‖ := by
  set h := classicalKet (X := Fin 2) x
  have hhh : ‖h‖ = 1 := by
    simp [classicalKet, h, EuclideanSpace.norm_single]
  have htL : ∀ e : E, ‖Quantum.tensorLeft h e‖ = ‖e‖ := by
    intro e
    have : ‖Quantum.tensorLeft h e‖ ^ 2 = (‖h‖ ^ 2) * ‖e‖ ^ 2 := by
      simp [Quantum.tensorLeft]
      ring
    rw [hhh, one_pow, one_mul] at this
    nlinarith [norm_nonneg (Quantum.tensorLeft h e), norm_nonneg e,
               sq_nonneg (‖Quantum.tensorLeft h e‖ - ‖e‖)]
  have hadj_gen : ∀ (z : Qubit ⊗[ℂ] E) (ψ : E),
      ⟪Quantum.contractLeft h z, ψ⟫_ℂ =
      ⟪z, Quantum.tensorLeft h ψ⟫_ℂ := by
    intro z ψ
    have hright : ⟪ψ, Quantum.contractLeft h z⟫_ℂ =
        ⟪Quantum.tensorLeft h ψ, z⟫_ℂ := by
      refine TensorProduct.induction_on z ?_ ?_ ?_
      · simp [Quantum.contractLeft]
      · intro h' k
        simp [Quantum.contractLeft, Quantum.tensorLeft,
          TensorProduct.inner_tmul, inner_smul_right]
      · intro z₁ z₂ hz₁ hz₂
        simp only [map_add, inner_add_right, hz₁, hz₂]
    rw [← inner_conj_symm, hright, inner_conj_symm]
  have hinner : ‖Quantum.contractLeft h w‖ ^ 2 ≤
      ‖w‖ * ‖Quantum.contractLeft h w‖ := by
    have hadj := hadj_gen w (Quantum.contractLeft h w)
    calc ‖Quantum.contractLeft h w‖ ^ 2
        = Complex.re ⟪Quantum.contractLeft h w,
            Quantum.contractLeft h w⟫_ℂ :=
          (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = Complex.re ⟪w,
            Quantum.tensorLeft h (Quantum.contractLeft h w)⟫_ℂ := by
          rw [hadj]
      _ ≤ ‖⟪w, Quantum.tensorLeft h (Quantum.contractLeft h w)⟫_ℂ‖ :=
          Complex.re_le_norm _
      _ ≤ ‖w‖ * ‖Quantum.tensorLeft h (Quantum.contractLeft h w)‖ :=
          norm_inner_le_norm _ _
      _ = ‖w‖ * ‖Quantum.contractLeft h w‖ := by rw [htL]
  nlinarith [norm_nonneg (Quantum.contractLeft h w), norm_nonneg w]

/-- `(id_H ⊗ V)` is a contraction when `V` is a contraction. -/
private lemma mc_idtensor_contraction_le
    {H K : Type*} [CpxFiniteHilbert H] [CpxFiniteHilbert K]
    (V : K →ₗ[ℂ] K)
    (hV : ∀ e : K, ‖V e‖ ≤ ‖e‖)
    (w : H ⊗[ℂ] K) :
    ‖((LinearMap.id : H →ₗ[ℂ] H) ⊗ₗ V) w‖ ≤ ‖w‖ := by
  suffices hsq : ‖((LinearMap.id : H →ₗ[ℂ] H) ⊗ₗ V) w‖ ^ 2 ≤ ‖w‖ ^ 2 by
    nlinarith [norm_nonneg (((LinearMap.id : H →ₗ[ℂ] H) ⊗ₗ V) w),
               norm_nonneg w,
               sq_nonneg (‖w‖ - ‖((LinearMap.id : H →ₗ[ℂ] H) ⊗ₗ V) w‖)]
  let bH := stdOrthonormalBasis ℂ H
  let bK := stdOrthonormalBasis ℂ K
  let bHK := bH.tensorProduct bK
  have hadj : ∀ (h : H) (ψ : K) (z : H ⊗[ℂ] K),
      ⟪ψ, Quantum.contractLeft h z⟫_ℂ =
      ⟪Quantum.tensorLeft h ψ, z⟫_ℂ := by
    intro h ψ z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [Quantum.contractLeft]
    · intro h' k
      simp [Quantum.contractLeft, Quantum.tensorLeft,
        TensorProduct.inner_tmul, inner_smul_right]
    · intro z₁ z₂ hz₁ hz₂
      simp only [map_add, inner_add_right, hz₁, hz₂]
  have hcomm : ∀ (h : H) (z : H ⊗[ℂ] K),
      Quantum.contractLeft h (((LinearMap.id : H →ₗ[ℂ] H) ⊗ₗ V) z) =
      V (Quantum.contractLeft h z) := by
    intro h z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [Quantum.contractLeft]
    · intro h' k
      simp [Quantum.contractLeft, TensorProduct.map_tmul, map_smul]
    · intro z₁ z₂ hz₁ hz₂
      simp only [map_add, hz₁, hz₂]
  have hfactor : ∀ (i : Fin (Module.finrank ℂ H))
      (j : Fin (Module.finrank ℂ K)) (z : H ⊗[ℂ] K),
      ⟪(bHK (i, j) : H ⊗[ℂ] K), z⟫_ℂ =
      ⟪(bK j : K), Quantum.contractLeft (bH i) z⟫_ℂ := by
    intro i j z
    rw [OrthonormalBasis.tensorProduct_apply]
    exact (hadj (bH i) (bK j) z).symm
  have parseval_cL : ∀ (z : H ⊗[ℂ] K),
      ‖z‖ ^ 2 = ∑ i : Fin (Module.finrank ℂ H),
        ‖Quantum.contractLeft (bH i) z‖ ^ 2 := by
    intro z
    rw [← bHK.sum_sq_norm_inner_right z, Fintype.sum_prod_type]
    congr 1; ext i
    simp_rw [hfactor i _ z]
    exact bK.sum_sq_norm_inner_right _
  rw [parseval_cL w, parseval_cL (((LinearMap.id : H →ₗ[ℂ] H) ⊗ₗ V) w)]
  apply Finset.sum_le_sum; intro i _
  rw [hcomm (bH i) w]
  exact pow_le_pow_left₀ (norm_nonneg _) (hV _) 2

/-! ## Lemma 15: measurement and discarding does not increase trace norm -/

-- The trace identity proof involves heavy unification across tensor products
set_option maxHeartbeats 800000 in
/--
**Blueprint lemma 15** (`lem:measure-contract`).

For any two states `ρ_ABE`, `σ_ABE`, the classical–quantum states `ρ_XE`, `σ_XE` obtained by
measuring Alice's qubit in the computational basis and discarding `B` satisfy
`‖ρ_XE − σ_XE‖₁ ≤ ‖ρ_ABE − σ_ABE‖₁`.

Proof outline:
1. **Linearity** (proved): `Φ(ρ) − Φ(σ) = Φ(ρ − σ)` where `Φ = rhoXE_from_ABE`.
2. **Channel contractivity** (proved): The measurement+partial-trace channel `Φ` satisfies
   `‖Φ(Δ)‖₁ ≤ ‖Δ‖₁` for all Hermitian `Δ`. This follows from the isometry approach:
   `Φ(Δ) = TrLeft_AB((W_meas ⊗ I_BE) · Δ · (W_meas† ⊗ I_BE))`, applying
   `isometry_trace_norm` then `partial_trace_contractive_left`.
-/
theorem measure_contract
    {E : Type} [CpxFiniteHilbert E]
    (ρABE σABE : DensityOperator (ABESystem E)) :
    traceNorm
      (rhoXE_from_ABE (E := E) ((ρABE : Operator (ABESystem E)))
        - rhoXE_from_ABE (E := E) ((σABE : Operator (ABESystem E))))
    ≤ traceNorm
        ((ρABE : Operator (ABESystem E)) - (σABE : Operator (ABESystem E))) := by
  -- Step 1: rhoXE_from_ABE is linear in its argument, so Φ(ρ) − Φ(σ) = Φ(ρ − σ).
  -- This holds since rhoXE_from_ABE is a sum of compositions of linear maps.
  have hlin :
      rhoXE_from_ABE (E := E) ((ρABE : Operator (ABESystem E)))
        - rhoXE_from_ABE (E := E) ((σABE : Operator (ABESystem E)))
      = rhoXE_from_ABE (E := E)
          ((ρABE : Operator (ABESystem E)) - (σABE : Operator (ABESystem E))) := by
    -- partialTraceLeft is linear; classProj x ⊗ₗ (·) is linear.
    set ρ' : Operator (ABESystem E) := ↑ρABE
    set σ' : Operator (ABESystem E) := ↑σABE
    simp only [rhoXE_from_ABE, rhoECond, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    -- Goal (at operator level): cP_x ⊗ₗ ptL(kP_x ∘ ρ' ∘ kP_x) - cP_x ⊗ₗ ptL(kP_x ∘ σ' ∘ kP_x)
    --                         = cP_x ⊗ₗ ptL(kP_x ∘ (ρ' - σ') ∘ kP_x)
    have hptL :
        partialTraceLeft (H := ABSystem) (K := E)
          (keyProjector (E := E) x ∘ₗ (ρ' - σ') ∘ₗ keyProjector (E := E) x) =
        partialTraceLeft (H := ABSystem) (K := E)
          (keyProjector (E := E) x ∘ₗ ρ' ∘ₗ keyProjector (E := E) x) -
        partialTraceLeft (H := ABSystem) (K := E)
          (keyProjector (E := E) x ∘ₗ σ' ∘ₗ keyProjector (E := E) x) := by
      simp only [partialTraceLeft, ← Finset.sum_sub_distrib]
      congr 1; ext i
      simp only [LinearMap.comp_sub, LinearMap.sub_comp]
    -- Goal: (cP_x ⊗ₗ ptL(ρ')) - (cP_x ⊗ₗ ptL(σ')) = cP_x ⊗ₗ ptL(ρ' - σ')
    -- Rewrite RHS via hptL, then prove by ext + tensor induction.
    rw [hptL]
    apply LinearMap.ext; intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul q e =>
      simp only [LinearMap.sub_apply, TensorProduct.map_tmul, TensorProduct.tmul_sub]
    | add z₁ z₂ h₁ h₂ =>
      simp only [map_add, h₁, h₂]
  rw [hlin]
  -- Step 2: ‖Φ(Δ)‖₁ ≤ ‖Δ‖₁ via the variational characterisation + contraction bound.
  set Δ : Operator (ABESystem E) := ↑ρABE - ↑σABE with hΔ_def
  change traceNorm (rhoXE_from_ABE (E := E) Δ) ≤ traceNorm Δ
  rw [trace_variational (rhoXE_from_ABE (E := E) Δ)]
  apply csSup_le
  · exact ⟨_, 1, rfl⟩
  · rintro r ⟨u, rfl⟩
    set uc : Operator (Qubit ⊗[ℂ] E) :=
      ((u : (Qubit ⊗[ℂ] E) →L[ℂ] (Qubit ⊗[ℂ] E)) : Operator (Qubit ⊗[ℂ] E)) with huc_def
    -- Block operators V_x = contractLeft(ket_x) ∘ u ∘ tensorLeft(ket_x)
    let V : Fin 2 → Operator E := fun x =>
      Quantum.contractLeft (classicalKet (X := Fin 2) x) ∘ₗ uc ∘ₗ
        Quantum.tensorLeft (classicalKet (X := Fin 2) x)
    have hV : ∀ (x : Fin 2) (e : E), ‖V x e‖ ≤ ‖e‖ := by
      intro x e
      have htL : ‖Quantum.tensorLeft (classicalKet (X := Fin 2) x) e‖ = ‖e‖ := by
        have hh : ‖classicalKet (X := Fin 2) x‖ = 1 := by
          simp [classicalKet, EuclideanSpace.norm_single]
        have hsq : ‖Quantum.tensorLeft (classicalKet x) e‖ ^ 2 = ‖e‖ ^ 2 := by
          have : ‖Quantum.tensorLeft (classicalKet x) e‖ ^ 2 =
              (‖classicalKet (X := Fin 2) x‖ ^ 2) * ‖e‖ ^ 2 := by
            simp [Quantum.tensorLeft]; ring
          rw [hh, one_pow, one_mul] at this; exact this
        nlinarith [norm_nonneg (Quantum.tensorLeft (classicalKet x) e), norm_nonneg e,
                   sq_nonneg (‖Quantum.tensorLeft (classicalKet x) e‖ - ‖e‖)]
      have hunorm : ‖uc (Quantum.tensorLeft (classicalKet x) e)‖ =
          ‖Quantum.tensorLeft (classicalKet x) e‖ := by
        change ‖((u : (Qubit ⊗[ℂ] E) →L[ℂ] (Qubit ⊗[ℂ] E)) : Operator (Qubit ⊗[ℂ] E))
          (Quantum.tensorLeft (classicalKet x) e)‖ = _
        exact Unitary.norm_map u _
      calc ‖V x e‖
          ≤ ‖uc (Quantum.tensorLeft (classicalKet x) e)‖ := mc_cL_norm_le x _
        _ = ‖Quantum.tensorLeft (classicalKet x) e‖ := hunorm
        _ = ‖e‖ := htL
    -- Effective contraction W = ∑_x kP_x ∘ (id_AB ⊗ V_x) ∘ kP_x
    let W : Operator (ABESystem E) := ∑ x : Fin 2,
      keyProjector (E := E) x ∘ₗ
        ((LinearMap.id : ABSystem →ₗ[ℂ] ABSystem) ⊗ₗ V x) ∘ₗ
        keyProjector (E := E) x
    -- W is a contraction
    have hW : ∀ v : ABESystem E, ‖W v‖ ≤ ‖v‖ := by
      intro v
      suffices hsq : ‖W v‖ ^ 2 ≤ ‖v‖ ^ 2 by
        nlinarith [norm_nonneg (W v), norm_nonneg v, sq_nonneg (‖v‖ - ‖W v‖)]
      have hWv : W v =
          keyProjector (E := E) 0
            (((LinearMap.id : ABSystem →ₗ[ℂ] ABSystem) ⊗ₗ V 0) (keyProjector (E := E) 0 v)) +
          keyProjector (E := E) 1
            (((LinearMap.id : ABSystem →ₗ[ℂ] ABSystem) ⊗ₗ V 1) (keyProjector (E := E) 1 v)) := by
        simp [W, Fin.sum_univ_two, LinearMap.add_apply, LinearMap.comp_apply]
      have horth : ⟪keyProjector (E := E) 0
            (((LinearMap.id : ABSystem →ₗ[ℂ] ABSystem) ⊗ₗ V 0) (keyProjector (E := E) 0 v)),
          keyProjector (E := E) 1
            (((LinearMap.id : ABSystem →ₗ[ℂ] ABSystem) ⊗ₗ V 1)
              (keyProjector (E := E) 1 v))⟫_ℂ = 0 :=
        mc_kP_orth 0 1 _ _ (by decide)
      have h0 : ‖keyProjector (E := E) 0
            (((LinearMap.id : ABSystem →ₗ[ℂ] ABSystem) ⊗ₗ V 0)
              (keyProjector (E := E) 0 v))‖
          ≤ ‖keyProjector (E := E) 0 v‖ :=
        (mc_kP_norm_le 0 _).trans (mc_idtensor_contraction_le (V 0) (hV 0) _)
      have h1 : ‖keyProjector (E := E) 1
            (((LinearMap.id : ABSystem →ₗ[ℂ] ABSystem) ⊗ₗ V 1)
              (keyProjector (E := E) 1 v))‖
          ≤ ‖keyProjector (E := E) 1 v‖ :=
        (mc_kP_norm_le 1 _).trans (mc_idtensor_contraction_le (V 1) (hV 1) _)
      have hpars := mc_kP_parseval (E := E) v
      rw [Fin.sum_univ_two] at hpars
      have hpyth :=
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
      simp only [← sq] at hpyth
      rw [hWv]
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) h0 2,
                 pow_le_pow_left₀ (norm_nonneg _) h1 2]
    -- Trace identity: trace(u ∘ rhoXE_from_ABE Δ) = trace(W ∘ Δ)
    have htrace_eq :
        trace (uc ∘ₗ rhoXE_from_ABE (E := E) Δ) = trace (W ∘ₗ Δ) := by
      -- Key sub-identity: classicalProjector x ⊗ₗ A = tL(ket_x) ∘ A ∘ cL(ket_x)
      have h_cP_eq : ∀ (x : Fin 2) (A : Operator E),
          ((classicalProjector (X := Fin 2) x) ⊗ₗ A
            : Operator (EuclideanSpace ℂ (Fin 2) ⊗[ℂ] E)) =
          Quantum.tensorLeft (classicalKet (X := Fin 2) x) ∘ₗ A ∘ₗ
            Quantum.contractLeft (classicalKet (X := Fin 2) x) := by
        intro x B
        apply LinearMap.ext; intro z
        refine TensorProduct.induction_on z ?_ ?_ ?_
        · simp
        · intro q e
          simp [classicalProjector, pureOp, Quantum.tensorLeft,
            Quantum.contractLeft, TensorProduct.map_tmul,
            TensorProduct.smul_tmul']
        · intro z₁ z₂ hz₁ hz₂; simp [hz₁, hz₂]
      -- Per-term identity
      have hterm : ∀ (x : Fin 2),
          trace (uc ∘ₗ ((classicalProjector (X := Fin 2) x) ⊗ₗ
            (Quantum.partialTraceLeft (H := ABSystem) (K := E)
              (keyProjector (E := E) x ∘ₗ Δ ∘ₗ keyProjector (E := E) x))))
          = trace (keyProjector (E := E) x ∘ₗ
              ((LinearMap.id : ABSystem →ₗ[ℂ] ABSystem) ⊗ₗ V x) ∘ₗ
              keyProjector (E := E) x ∘ₗ Δ) := by
        intro x
        set Ax : Operator E := Quantum.partialTraceLeft (H := ABSystem) (K := E)
          (keyProjector (E := E) x ∘ₗ Δ ∘ₗ keyProjector (E := E) x)
        set ket := classicalKet (X := Fin 2) x
        set tL := Quantum.tensorLeft (H := Qubit) (K := E) ket
        set cL := Quantum.contractLeft (H := Qubit) (K := E) ket
        -- Step (a): cP_x ⊗ₗ Ax = tL ∘ Ax ∘ cL
        have hcP := h_cP_eq x Ax
        -- Step (b): trace(uc ∘ tL ∘ Ax ∘ cL) = trace(cL ∘ uc ∘ tL ∘ Ax) = trace(V_x ∘ Ax)
        --   Using trace_comp_comm': trace(f ∘ g) = trace(g ∘ f) for rectangular f, g
        have hcyc1 :
            LinearMap.trace ℂ (Qubit ⊗[ℂ] E) ((uc ∘ₗ tL ∘ₗ Ax) ∘ₗ cL) =
            LinearMap.trace ℂ E (cL ∘ₗ (uc ∘ₗ tL ∘ₗ Ax)) := by
          rw [← LinearMap.trace_comp_comm']
        have hVx_eq : cL ∘ₗ (uc ∘ₗ tL ∘ₗ Ax) = V x ∘ₗ Ax := by
          ext e; simp only [V, LinearMap.comp_apply]; rfl
        -- Step (c): trace(V_x ∘ Ax) = trace((id_AB ⊗ V_x) ∘ kP_x ∘ Δ ∘ kP_x)
        --   Using trace_mul_partialTraceLeft
        have hptL :
            LinearMap.trace ℂ E (V x ∘ₗ Ax) =
            trace (((LinearMap.id : ABSystem →ₗ[ℂ] ABSystem) ⊗ₗ V x) ∘ₗ
              (keyProjector (E := E) x ∘ₗ Δ ∘ₗ keyProjector (E := E) x)) := by
          exact trace_mul_partialTraceLeft (V x)
            (keyProjector (E := E) x ∘ₗ Δ ∘ₗ keyProjector (E := E) x)
        -- Step (d): cyclicity on ABESystem E
        have hcyc2 :
            trace (((LinearMap.id : ABSystem →ₗ[ℂ] ABSystem) ⊗ₗ V x) ∘ₗ
              (keyProjector (E := E) x ∘ₗ Δ ∘ₗ keyProjector (E := E) x))
            = trace (keyProjector (E := E) x ∘ₗ
                ((LinearMap.id : ABSystem →ₗ[ℂ] ABSystem) ⊗ₗ V x) ∘ₗ
                keyProjector (E := E) x ∘ₗ Δ) := by
          have : ((LinearMap.id : ABSystem →ₗ[ℂ] ABSystem) ⊗ₗ V x) ∘ₗ
              (keyProjector (E := E) x ∘ₗ Δ ∘ₗ keyProjector (E := E) x) =
              (((LinearMap.id : ABSystem →ₗ[ℂ] ABSystem) ⊗ₗ V x) ∘ₗ
                keyProjector (E := E) x ∘ₗ Δ) ∘ₗ
              keyProjector (E := E) x := by
            ext v; simp [LinearMap.comp_apply]
          rw [this]
          simpa [Module.End.mul_eq_comp] using
            (LinearMap.trace_mul_comm ℂ
              (((LinearMap.id : ABSystem →ₗ[ℂ] ABSystem) ⊗ₗ V x) ∘ₗ
                keyProjector (E := E) x ∘ₗ Δ)
              (keyProjector (E := E) x))
        -- Chain all steps
        calc trace (uc ∘ₗ ((classicalProjector x) ⊗ₗ Ax))
            = trace (uc ∘ₗ (tL ∘ₗ Ax ∘ₗ cL)) := by rw [hcP]
          _ = LinearMap.trace ℂ (Qubit ⊗[ℂ] E) ((uc ∘ₗ tL ∘ₗ Ax) ∘ₗ cL) := by
              congr 1
          _ = LinearMap.trace ℂ E (cL ∘ₗ (uc ∘ₗ tL ∘ₗ Ax)) := hcyc1
          _ = LinearMap.trace ℂ E (V x ∘ₗ Ax) := by rw [hVx_eq]
          _ = trace (((LinearMap.id : ABSystem →ₗ[ℂ] ABSystem) ⊗ₗ V x) ∘ₗ
                (keyProjector (E := E) x ∘ₗ Δ ∘ₗ keyProjector (E := E) x)) := hptL
          _ = trace (keyProjector (E := E) x ∘ₗ
                ((LinearMap.id : ABSystem →ₗ[ℂ] ABSystem) ⊗ₗ V x) ∘ₗ
                keyProjector (E := E) x ∘ₗ Δ) := hcyc2
      -- Combine: expand sums on both sides
      have hΦ : rhoXE_from_ABE (E := E) Δ =
          ((classicalProjector (X := Fin 2) 0) ⊗ₗ
            (Quantum.partialTraceLeft (H := ABSystem) (K := E)
              (keyProjector (E := E) 0 ∘ₗ Δ ∘ₗ
                keyProjector (E := E) 0))) +
          ((classicalProjector (X := Fin 2) 1) ⊗ₗ
            (Quantum.partialTraceLeft (H := ABSystem) (K := E)
              (keyProjector (E := E) 1 ∘ₗ Δ ∘ₗ
                keyProjector (E := E) 1))) := by
        simp [rhoXE_from_ABE, rhoECond, Fin.sum_univ_two]
      have hWexp : W =
          (keyProjector (E := E) 0 ∘ₗ
            ((LinearMap.id : ABSystem →ₗ[ℂ] ABSystem) ⊗ₗ V 0) ∘ₗ
            keyProjector (E := E) 0) +
          (keyProjector (E := E) 1 ∘ₗ
            ((LinearMap.id : ABSystem →ₗ[ℂ] ABSystem) ⊗ₗ V 1) ∘ₗ
            keyProjector (E := E) 1) :=
        Fin.sum_univ_two _
      rw [hΦ, hWexp, LinearMap.comp_add, LinearMap.add_comp]
      simp only [trace, map_add]
      congr 1
      · exact hterm 0
      · exact hterm 1
    rw [htrace_eq]
    exact mc_norm_trace_contraction_le W Δ hW

end RigidityToPguess
