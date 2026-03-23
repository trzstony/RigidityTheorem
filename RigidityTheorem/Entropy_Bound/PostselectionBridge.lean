import Entropy_Bound.CHSHBound

open scoped TensorProduct InnerProductSpace
open Quantum

namespace Entropy_Bound

/--
Bell-postselection projector on `ABE`:
Π := |Φ⁺⟩⟨Φ⁺| ⊗ I.
-/
noncomputable def postselectProjector
    {E : Type} [CpxFiniteHilbert E] : Operator (ABESystem E) :=
  (pureOp Φ_plus) ⊗ₗ (LinearMap.id : Operator E)

/-- Unnormalized Bell-postselected operator `Π ρ Π`. -/
noncomputable def postselectUnnormalized
    {E : Type} [CpxFiniteHilbert E]
    (ρABE : Operator (ABESystem E)) : Operator (ABESystem E) :=
  (postselectProjector (E := E)) ∘ₗ ρABE ∘ₗ (postselectProjector (E := E))

/-- Complex postselection success value `Tr(Πρ)`. -/
noncomputable def postselectSuccessC
    {E : Type} [CpxFiniteHilbert E]
    (ρABE : Operator (ABESystem E)) : ℂ :=
  trace (H := ABESystem E) ((postselectProjector (E := E)) ∘ₗ ρABE)

/--
Normalized postselected operator:
ρ̃ := ΠρΠ⁄Tr(Πρ).
-/
noncomputable def postselectState
    {E : Type} [CpxFiniteHilbert E]
    (ρABE : Operator (ABESystem E)) : Operator (ABESystem E) :=
  ((postselectSuccessC (E := E) ρABE)⁻¹ : ℂ) • postselectUnnormalized (E := E) ρABE

private lemma bellProjector_idempotent :
    ((pureOp Φ_plus) : Operator ABSystem) ∘ₗ (pureOp Φ_plus) = (pureOp Φ_plus) := by
  ext ψ
  simp [pureOp_apply]

private lemma postselectProjector_idempotent
    {E : Type} [CpxFiniteHilbert E] :
    (postselectProjector (E := E)) ∘ₗ (postselectProjector (E := E))
      = postselectProjector (E := E) := by
  calc
    (postselectProjector (E := E)) ∘ₗ (postselectProjector (E := E))
        = (((pureOp Φ_plus) : Operator ABSystem) ∘ₗ (pureOp Φ_plus))
            ⊗ₗ (((LinearMap.id : Operator E) ∘ₗ (LinearMap.id : Operator E)) : Operator E) := by
              simpa [postselectProjector, Module.End.mul_eq_comp] using
                (TensorProduct.map_comp
                  (f₂ := ((pureOp Φ_plus) : Operator ABSystem))
                  (g₂ := (LinearMap.id : Operator E))
                  (f₁ := ((pureOp Φ_plus) : Operator ABSystem))
                  (g₁ := (LinearMap.id : Operator E))).symm
    _ = ((pureOp Φ_plus) : Operator ABSystem) ⊗ₗ (LinearMap.id : Operator E) := by
          simp [bellProjector_idempotent]
    _ = postselectProjector (E := E) := rfl

/--
Trace of the unnormalized postselected operator equals the success value:
Tr(ΠρΠ) = Tr(Πρ).
-/
theorem trace_postselectUnnormalized
    {E : Type} [CpxFiniteHilbert E]
    (ρABE : Operator (ABESystem E)) :
    trace (H := ABESystem E) (postselectUnnormalized (E := E) ρABE)
      = postselectSuccessC (E := E) ρABE := by
  calc
    trace (H := ABESystem E) (postselectUnnormalized (E := E) ρABE)
        = trace (H := ABESystem E)
            (((postselectProjector (E := E)) ∘ₗ (postselectProjector (E := E))) ∘ₗ ρABE) := by
            unfold postselectUnnormalized
            simpa [Module.End.mul_eq_comp, LinearMap.comp_assoc] using
              (LinearMap.trace_mul_comm ℂ
                (((postselectProjector (E := E)) ∘ₗ ρABE))
                (postselectProjector (E := E)))
    _ = trace (H := ABESystem E) ((postselectProjector (E := E)) ∘ₗ ρABE) := by
          simp [postselectProjector_idempotent]
    _ = postselectSuccessC (E := E) ρABE := rfl

/--
Normalization identity:
if `Tr(Πρ) ≠ 0`, then `Tr( (Tr(Πρ))⁻¹ ΠρΠ ) = 1`.
-/
theorem trace_postselectState_eq_one
    {E : Type} [CpxFiniteHilbert E]
    (ρABE : Operator (ABESystem E))
    (hSucc : postselectSuccessC (E := E) ρABE ≠ 0) :
    trace (H := ABESystem E) (postselectState (E := E) ρABE) = 1 := by
  calc
    trace (H := ABESystem E) (postselectState (E := E) ρABE)
        = ((postselectSuccessC (E := E) ρABE)⁻¹ : ℂ)
            * trace (H := ABESystem E) (postselectUnnormalized (E := E) ρABE) := by
              simp [postselectState, trace]
    _ = ((postselectSuccessC (E := E) ρABE)⁻¹ : ℂ)
          * (postselectSuccessC (E := E) ρABE) := by
            simp [trace_postselectUnnormalized]
    _ = 1 := by simp [hSucc]

/-- The partial matrix element `(⟨Φ+|_AB ⊗ I_E) ρ_ABE (|Φ+⟩_AB ⊗ I_E)` on `E`. -/
noncomputable def bellPartialElement
    {E : Type} [CpxFiniteHilbert E]
    (ρABE : Operator (ABESystem E)) : Operator E :=
  contractLeft (H := ABSystem) (K := E) Φ_plus ∘ₗ ρABE ∘ₗ
    tensorLeft (H := ABSystem) (K := E) Φ_plus

/-- The Bell-postselection projector factors as `tensorLeft Φ_plus ∘ₗ contractLeft Φ_plus`. -/
private lemma postselectProjector_factored
    {E : Type} [CpxFiniteHilbert E] :
    postselectProjector (E := E) =
      tensorLeft (H := ABSystem) (K := E) Φ_plus ∘ₗ
        contractLeft (H := ABSystem) (K := E) Φ_plus := by
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on (M := ABSystem) (N := E) (z := z) ?h0 ?ht ?ha
  · simp
  · intro h k
    simp [postselectProjector, pureOp_apply, Quantum.contractLeft, Quantum.tensorLeft,
      LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.rTensor_tmul,
      TensorProduct.lid_tmul, TensorProduct.smul_tmul']
  · intro z₁ z₂ hz₁ hz₂
    simp [map_add, hz₁, hz₂]

/--
Lemma 10 (Rank-one postselection, unnormalized):
the postselected unnormalized operator factors as
Π ρ_ABE Π = Φ ⊗ τₑ,
where
τₑ = (⟨Φ⁺| ⊗ I) ρ_ABE (|Φ⁺⟩ ⊗ I).
-/
theorem postselectUnnormalized_eq_bellTensor
    {E : Type} [CpxFiniteHilbert E]
    (ρABE : Operator (ABESystem E)) :
    postselectUnnormalized (E := E) ρABE =
      (pureOp Φ_plus) ⊗ₗ (bellPartialElement (E := E) ρABE) := by
  apply TensorProduct.ext'
  intro h k
  simp [postselectUnnormalized, bellPartialElement, postselectProjector_factored,
    LinearMap.comp_apply, TensorProduct.map_tmul, pureOp_apply, Quantum.contractLeft,
    Quantum.tensorLeft, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul]

/--
Lemma 10 (Rank-one postselection, normalized):
the postselected state factors as
ρ̃_ABE = Φ ⊗ τₑ,
where
τₑ = ¹⁄ₚ (⟨Φ⁺| ⊗ I) ρ_ABE (|Φ⁺⟩ ⊗ I).
-/
theorem postselectState_eq_bellTensor
    {E : Type} [CpxFiniteHilbert E]
    (ρABE : Operator (ABESystem E)) :
    postselectState (E := E) ρABE =
      (pureOp Φ_plus) ⊗ₗ
        ((postselectSuccessC (E := E) ρABE)⁻¹ •
          bellPartialElement (E := E) ρABE) := by
  simp only [postselectState]
  rw [postselectUnnormalized_eq_bellTensor]
  -- Goal: p⁻¹ • (Φ ⊗ₗ τ') = Φ ⊗ₗ (p⁻¹ • τ')
  apply LinearMap.ext
  intro z
  refine TensorProduct.induction_on (M := ABSystem) (N := E) (z := z) ?h0 ?ht ?ha
  · simp
  · intro h k
    simp [TensorProduct.map_tmul, LinearMap.smul_apply,
      TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  · intro z₁ z₂ hz₁ hz₂
    simp [map_add, hz₁, hz₂]


private lemma traceNorm_le_re_trace_of_isPositive
    {H : Type*} [CpxFiniteHilbert H]
    {X : Operator H} (hX : X.IsPositive) :
    traceNorm (H := H) X ≤ Complex.re (trace (H := H) X) := by
  let n : ℕ := Module.finrank ℂ H
  let b : OrthonormalBasis (Fin n) ℂ H := hX.isSymmetric.eigenvectorBasis (hn := rfl)
  have hEig_nonneg : ∀ i : Fin n, 0 ≤ hX.isSymmetric.eigenvalues (hn := rfl) i := by
    intro i
    simpa using hX.nonneg_eigenvalues (hn := rfl) i
  rw [trace_variational X]
  apply csSup_le
  · exact ⟨_, 1, rfl⟩
  · rintro r ⟨u, rfl⟩
    have htrace :
        trace (H := H) (((u : H →L[ℂ] H) : Operator H) ∘ₗ X)
          = ∑ i : Fin n, ⟪b i, (((u : H →L[ℂ] H) : Operator H) ∘ₗ X) (b i)⟫_ℂ := by
      simp [trace, LinearMap.trace_eq_sum_inner _ b]
    rw [htrace]
    calc
      ‖∑ i : Fin n, ⟪b i, (((u : H →L[ℂ] H) : Operator H) ∘ₗ X) (b i)⟫_ℂ‖
          ≤ ∑ i : Fin n, ‖⟪b i, (((u : H →L[ℂ] H) : Operator H) ∘ₗ X) (b i)⟫_ℂ‖ := by
            simpa using
              (norm_sum_le (s := Finset.univ)
                (f := fun i : Fin n => ⟪b i, (((u : H →L[ℂ] H) : Operator H) ∘ₗ X) (b i)⟫_ℂ))
      _ ≤ ∑ i : Fin n, hX.isSymmetric.eigenvalues (hn := rfl) i := by
            gcongr with i
            have hb_norm : ‖b i‖ = 1 := b.orthonormal.1 i
            have hXi : X (b i) = (hX.isSymmetric.eigenvalues (hn := rfl) i : ℂ) • b i :=
              hX.isSymmetric.apply_eigenvectorBasis (hn := rfl) i
            calc
              ‖⟪b i, (((u : H →L[ℂ] H) : Operator H) ∘ₗ X) (b i)⟫_ℂ‖
                  ≤ ‖b i‖ * ‖(((u : H →L[ℂ] H) : Operator H) ∘ₗ X) (b i)‖ := by
                    exact norm_inner_le_norm _ _
              _ = ‖(((u : H →L[ℂ] H) : Operator H) ∘ₗ X) (b i)‖ := by
                    rw [hb_norm, one_mul]
              _ = ‖X (b i)‖ := by
                    simp only [LinearMap.comp_apply]
                    exact Unitary.norm_map u (X (b i))
              _ = ‖(hX.isSymmetric.eigenvalues (hn := rfl) i : ℂ) • b i‖ := by
                    rw [hXi]
              _ = ‖(hX.isSymmetric.eigenvalues (hn := rfl) i : ℂ)‖ := by
                    rw [norm_smul, hb_norm, mul_one]
              _ = hX.isSymmetric.eigenvalues (hn := rfl) i := by
                    simp [Complex.norm_real, abs_of_nonneg (hEig_nonneg i)]
      _ = Complex.re (trace (H := H) X) := by
            simpa [n] using (hX.isSymmetric.re_trace_eq_sum_eigenvalues (hn := rfl)).symm

private lemma norm_trace_le_traceNorm
    {H : Type*} [CpxFiniteHilbert H]
    (A : Operator H) :
    ‖trace (H := H) A‖ ≤ traceNorm (H := H) A := by
  let n : ℕ := Module.finrank ℂ H
  let b : OrthonormalBasis (Fin n) ℂ H := stdOrthonormalBasis ℂ H
  let S : Set ℝ := {r : ℝ | ∃ u : unitary (H →L[ℂ] H),
      r = ‖trace (H := H) (((u : H →L[ℂ] H) : Operator H) ∘ₗ A)‖}
  have hbounded : BddAbove S := by
    refine ⟨∑ i : Fin n, ‖A (b i)‖, ?_⟩
    intro r hr
    rcases hr with ⟨u, rfl⟩
    have htrace :
        trace (H := H) (((u : H →L[ℂ] H) : Operator H) ∘ₗ A)
          = ∑ i : Fin n, ⟪b i, (((u : H →L[ℂ] H) : Operator H) ∘ₗ A) (b i)⟫_ℂ := by
      simp [trace, LinearMap.trace_eq_sum_inner _ b]
    rw [htrace]
    calc
      ‖∑ i : Fin n, ⟪b i, (((u : H →L[ℂ] H) : Operator H) ∘ₗ A) (b i)⟫_ℂ‖
          ≤ ∑ i : Fin n, ‖⟪b i, (((u : H →L[ℂ] H) : Operator H) ∘ₗ A) (b i)⟫_ℂ‖ := by
            simpa using
              (norm_sum_le (s := Finset.univ)
                (f := fun i : Fin n => ⟪b i, (((u : H →L[ℂ] H) : Operator H) ∘ₗ A) (b i)⟫_ℂ))
      _ ≤ ∑ i : Fin n, ‖A (b i)‖ := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hb_norm : ‖b i‖ = 1 := b.orthonormal.1 i
            calc
              ‖⟪b i, (((u : H →L[ℂ] H) : Operator H) ∘ₗ A) (b i)⟫_ℂ‖
                  ≤ ‖b i‖ * ‖(((u : H →L[ℂ] H) : Operator H) ∘ₗ A) (b i)‖ := by
                    exact norm_inner_le_norm _ _
              _ = ‖(((u : H →L[ℂ] H) : Operator H) ∘ₗ A) (b i)‖ := by
                    rw [hb_norm, one_mul]
              _ = ‖A (b i)‖ := by
                    simp only [LinearMap.comp_apply]
                    exact Unitary.norm_map u (A (b i))
  rw [trace_variational (H := H) A]
  have hmem : ‖trace (H := H) A‖ ∈ S := by
    refine ⟨1, ?_⟩
    have hone : (((1 : H →L[ℂ] H) : Operator H) ∘ₗ A) = A := by
      ext x
      rfl
    simp [hone]
  simpa [S] using (le_csSup hbounded hmem)

private lemma traceNorm_eq_re_trace_of_isPositive
    {H : Type*} [CpxFiniteHilbert H]
    {X : Operator H} (hX : X.IsPositive) :
    traceNorm (H := H) X = Complex.re (trace (H := H) X) := by
  have hle :
      traceNorm (H := H) X ≤ Complex.re (trace (H := H) X) :=
    traceNorm_le_re_trace_of_isPositive (H := H) hX
  have hre_nonneg : 0 ≤ Complex.re (trace (H := H) X) := by
    have hsum_nonneg :
        0 ≤ ∑ i : Fin (Module.finrank ℂ H), hX.isSymmetric.eigenvalues (hn := rfl) i := by
      exact Finset.sum_nonneg (fun i _ => hX.nonneg_eigenvalues (hn := rfl) i)
    have htr_re :
        Complex.re (trace (H := H) X)
          = ∑ i : Fin (Module.finrank ℂ H), hX.isSymmetric.eigenvalues (hn := rfl) i := by
      simpa [trace] using hX.isSymmetric.re_trace_eq_sum_eigenvalues (hn := rfl)
    simpa [htr_re] using hsum_nonneg
  have him_zero : Complex.im (trace (H := H) X) = 0 := by
    rw [show trace (H := H) X =
      ((∑ i : Fin (Module.finrank ℂ H), hX.isSymmetric.eigenvalues (hn := rfl) i) : ℂ) by
      simpa [trace] using hX.isSymmetric.trace_eq_sum_eigenvalues (hn := rfl)]
    simp
  have htrace_real :
      trace (H := H) X = (Complex.re (trace (H := H) X) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him_zero]
  have hge :
      Complex.re (trace (H := H) X) ≤ traceNorm (H := H) X := by
    have hnorm : ‖trace (H := H) X‖ = Complex.re (trace (H := H) X) := by
      rw [htrace_real]
      simp [Complex.norm_real, abs_of_nonneg hre_nonneg]
    exact hnorm.symm.le.trans (norm_trace_le_traceNorm (H := H) X)
  exact le_antisymm hle hge

private lemma isPositive_real_smul
    {H : Type*} [CpxFiniteHilbert H]
    {X : Operator H} (hX : X.IsPositive)
    {c : Real} (hc : 0 ≤ c) :
    (((c : ℂ) • X) : Operator H).IsPositive := by
  exact hX.smul_of_nonneg (by exact_mod_cast hc)


/--
Cross-term bound: for an orthogonal projector `Q` (self-adjoint, idempotent)
with complement `Qc = I - Q`, and a density operator `ρ`,
`‖Q ρ Qc‖₁ ≤ √(Re Tr(Qc ρ Qc))`.

Proof: variational formula + eigenbasis of ρ + Cauchy-Schwarz twice.
-/
private lemma traceNorm_cross_le_sqrt_trace
    {H : Type*} [CpxFiniteHilbert H]
    {Q Qc : Operator H}
    (hQ_adj : LinearMap.adjoint Q = Q)
    (hQ_idem : Q ∘ₗ Q = Q)
    (hQc_adj : LinearMap.adjoint Qc = Qc)
    (hQc_idem : Qc ∘ₗ Qc = Qc)
    (_hQQc : Q ∘ₗ Qc = 0)
    {ρ : Operator H}
    (hρ_herm : IsHermitian ρ)
    (hρ_pos : ρ.IsPositive)
    (hρ_tr : trace ρ = 1) :
    traceNorm (H := H) (Q ∘ₗ ρ ∘ₗ Qc) ≤
      Real.sqrt (Complex.re (trace (H := H) (Qc ∘ₗ ρ ∘ₗ Qc))) := by
  let n := Module.finrank ℂ H
  let b : OrthonormalBasis (Fin n) ℂ H := hρ_herm.eigenvectorBasis rfl
  let ev : Fin n → ℝ := hρ_herm.eigenvalues rfl
  have hev_nn : ∀ i, 0 ≤ ev i := fun i => by
    simpa using hρ_pos.nonneg_eigenvalues rfl i
  have hρb : ∀ i, ρ (b i) = (ev i : ℂ) • b i :=
    hρ_herm.apply_eigenvectorBasis rfl
  -- Qc is a contraction: ‖Qc x‖ ≤ ‖x‖.
  have hQc_contr : ∀ x : H, ‖Qc x‖ ≤ ‖x‖ := by
    intro x
    have hadj : (LinearMap.adjoint Qc) (Qc x) = Qc x := by
      rw [hQc_adj]
      exact LinearMap.congr_fun hQc_idem x
    have hinner' : ⟪(LinearMap.adjoint Qc) (Qc x), x⟫_ℂ = ⟪Qc x, Qc x⟫_ℂ :=
      LinearMap.adjoint_inner_left Qc (x := x) (y := Qc x)
    have hinner : ⟪Qc x, x⟫_ℂ = ⟪Qc x, Qc x⟫_ℂ := by
      calc
        ⟪Qc x, x⟫_ℂ = ⟪(LinearMap.adjoint Qc) (Qc x), x⟫_ℂ :=
          congrArg (fun z => ⟪z, x⟫_ℂ) hadj.symm
        _ = ⟪Qc x, Qc x⟫_ℂ := hinner'
    have hsq : ‖Qc x‖ ^ 2 ≤ ‖Qc x‖ * ‖x‖ := by
      calc
        ‖Qc x‖ ^ 2 = ‖⟪Qc x, Qc x⟫_ℂ‖ := by
          rw [inner_self_eq_norm_sq_to_K]
          simp [Complex.norm_real]
        _ = ‖⟪Qc x, x⟫_ℂ‖ := by rw [hinner]
        _ ≤ ‖Qc x‖ * ‖x‖ := norm_inner_le_norm _ _
    nlinarith [norm_nonneg (Qc x), norm_nonneg x, hsq]
  -- Q is also a contraction: ‖Q x‖ ≤ ‖x‖.
  have hQ_contr : ∀ x : H, ‖Q x‖ ≤ ‖x‖ := by
    intro x
    have hadj : (LinearMap.adjoint Q) (Q x) = Q x := by
      rw [hQ_adj]
      exact LinearMap.congr_fun hQ_idem x
    have hinner' : ⟪(LinearMap.adjoint Q) (Q x), x⟫_ℂ = ⟪Q x, Q x⟫_ℂ :=
      LinearMap.adjoint_inner_left Q (x := x) (y := Q x)
    have hinner : ⟪Q x, x⟫_ℂ = ⟪Q x, Q x⟫_ℂ := by
      calc
        ⟪Q x, x⟫_ℂ = ⟪(LinearMap.adjoint Q) (Q x), x⟫_ℂ :=
          congrArg (fun z => ⟪z, x⟫_ℂ) hadj.symm
        _ = ⟪Q x, Q x⟫_ℂ := hinner'
    have hsq : ‖Q x‖ ^ 2 ≤ ‖Q x‖ * ‖x‖ := by
      calc
        ‖Q x‖ ^ 2 = ‖⟪Q x, Q x⟫_ℂ‖ := by
          rw [inner_self_eq_norm_sq_to_K]
          simp [Complex.norm_real]
        _ = ‖⟪Q x, x⟫_ℂ‖ := by rw [hinner]
        _ ≤ ‖Q x‖ * ‖x‖ := norm_inner_le_norm _ _
    nlinarith [norm_nonneg (Q x), norm_nonneg x, hsq]
  -- Key identity: ∑ λ_i ‖Qc b_i‖² = Re(tr(Qc ρ Qc)).
  have hre_norm_Qc : ∀ i, ‖Qc (b i)‖ ^ 2 = Complex.re ⟪b i, Qc (b i)⟫_ℂ := by
    intro i
    have hadj : LinearMap.adjoint Qc (Qc (b i)) = Qc (b i) := by
      rw [hQc_adj]
      exact LinearMap.congr_fun hQc_idem (b i)
    have hinner' : ⟪LinearMap.adjoint Qc (Qc (b i)), b i⟫_ℂ = ⟪Qc (b i), Qc (b i)⟫_ℂ :=
      LinearMap.adjoint_inner_left Qc (x := b i) (y := Qc (b i))
    have hinner : ⟪Qc (b i), b i⟫_ℂ = ⟪Qc (b i), Qc (b i)⟫_ℂ := by
      calc
        ⟪Qc (b i), b i⟫_ℂ = ⟪LinearMap.adjoint Qc (Qc (b i)), b i⟫_ℂ :=
          congrArg (fun z => ⟪z, b i⟫_ℂ) hadj.symm
        _ = ⟪Qc (b i), Qc (b i)⟫_ℂ := hinner'
    calc
      ‖Qc (b i)‖ ^ 2 = Complex.re ⟪Qc (b i), Qc (b i)⟫_ℂ := by
        simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (x := Qc (b i))).symm
      _ = Complex.re ⟪Qc (b i), b i⟫_ℂ := by rw [hinner]
      _ = Complex.re ⟪b i, Qc (b i)⟫_ℂ := by
        simpa using (inner_re_symm (𝕜 := ℂ) (x := Qc (b i)) (y := b i))
  have hsum_norm_sq : ∑ i : Fin n, ev i * ‖Qc (b i)‖ ^ 2 =
      Complex.re (trace (H := H) (Qc ∘ₗ ρ ∘ₗ Qc)) := by
    simp_rw [hre_norm_Qc]
    have hterm : ∀ i : Fin n,
        ev i * Complex.re ⟪b i, Qc (b i)⟫_ℂ =
          Complex.re ⟪b i, (Qc ∘ₗ ρ) (b i)⟫_ℂ := by
      intro i
      rw [LinearMap.comp_apply, hρb i, map_smul, inner_smul_right]
      simp [Complex.mul_re]
    have hstep : ∑ i : Fin n, ev i * Complex.re ⟪b i, Qc (b i)⟫_ℂ =
        ∑ i : Fin n, Complex.re ⟪b i, (Qc ∘ₗ ρ) (b i)⟫_ℂ := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact hterm i
    rw [hstep]
    have hsum_re : (∑ i : Fin n, Complex.re ⟪b i, (Qc ∘ₗ ρ) (b i)⟫_ℂ)
        = Complex.re (∑ i : Fin n, ⟪b i, (Qc ∘ₗ ρ) (b i)⟫_ℂ) := by
      simp
    rw [hsum_re]
    have htr_QcRho : trace (H := H) (Qc ∘ₗ ρ)
        = ∑ i, ⟪b i, (Qc ∘ₗ ρ) (b i)⟫_ℂ := by
      simp [trace, LinearMap.trace_eq_sum_inner _ b]
    have htr_eq : trace (H := H) (Qc ∘ₗ ρ ∘ₗ Qc) = trace (H := H) (Qc ∘ₗ ρ) := by
      calc
        trace (H := H) (Qc ∘ₗ ρ ∘ₗ Qc)
            = trace (H := H) ((Qc ∘ₗ ρ) ∘ₗ Qc) := by rfl
        _ = trace (H := H) (Qc ∘ₗ (Qc ∘ₗ ρ)) := by
              simpa [Module.End.mul_eq_comp] using
                LinearMap.trace_mul_comm ℂ (Qc ∘ₗ ρ) Qc
        _ = trace (H := H) ((Qc ∘ₗ Qc) ∘ₗ ρ) := by
              simp [LinearMap.comp_assoc]
        _ = trace (H := H) (Qc ∘ₗ ρ) := by
              simp [hQc_idem]
    simpa [htr_QcRho] using (congrArg Complex.re htr_eq).symm
  -- Eigenvalue sum: ∑ ev_i = 1
  have hsum_ev : ∑ i : Fin n, ev i = 1 := by
    have : Complex.re (trace (H := H) ρ) = 1 := by simp [hρ_tr]
    rw [← this]
    rw [show trace (H := H) ρ = ∑ i, ⟪b i, ρ (b i)⟫_ℂ from by
      simp [trace, LinearMap.trace_eq_sum_inner _ b]]
    simp_rw [hρb, inner_smul_right]
    simp [b.orthonormal.1, Complex.ofReal_re]
  -- Nonnegativity of Re(tr(Qc ρ Qc))
  have h1p_nn : 0 ≤ Complex.re (trace (H := H) (Qc ∘ₗ ρ ∘ₗ Qc)) := by
    rw [← hsum_norm_sq]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (hev_nn i) (sq_nonneg _)
  -- Now use the variational formula
  rw [trace_variational (Q ∘ₗ ρ ∘ₗ Qc)]
  apply csSup_le
  · exact ⟨_, 1, rfl⟩
  · rintro r ⟨u, rfl⟩
    let u_op : Operator H := ((u : H →L[ℂ] H) : Operator H)
    -- Step 1: cyclicity of trace.
    have hcyc_trace :
        trace (H := H) (u_op ∘ₗ Q ∘ₗ ρ ∘ₗ Qc)
          = trace (H := H) (Qc ∘ₗ u_op ∘ₗ Q ∘ₗ ρ) := by
      calc
        trace (H := H) (u_op ∘ₗ Q ∘ₗ ρ ∘ₗ Qc)
            = trace (H := H) ((u_op ∘ₗ Q ∘ₗ ρ) ∘ₗ Qc) := by rfl
        _ = trace (H := H) (Qc ∘ₗ (u_op ∘ₗ Q ∘ₗ ρ)) := by
              simpa [LinearMap.comp_assoc, Module.End.mul_eq_comp] using
                LinearMap.trace_mul_comm ℂ (u_op ∘ₗ Q ∘ₗ ρ) Qc
        _ = trace (H := H) (Qc ∘ₗ u_op ∘ₗ Q ∘ₗ ρ) := by
              simp
    -- Step 2: expand in eigenbasis of ρ (after cyclicity)
    have hexpand :
        trace (H := H) (Qc ∘ₗ u_op ∘ₗ Q ∘ₗ ρ)
          = ∑ i, (ev i : ℂ) * ⟪b i, (Qc ∘ₗ u_op ∘ₗ Q) (b i)⟫_ℂ := by
      have htrace : trace (H := H) (Qc ∘ₗ u_op ∘ₗ Q ∘ₗ ρ)
          = ∑ i, ⟪b i, (Qc ∘ₗ u_op ∘ₗ Q ∘ₗ ρ) (b i)⟫_ℂ := by
        simp [trace, LinearMap.trace_eq_sum_inner _ b]
      rw [htrace]
      congr 1; ext i
      calc
        ⟪b i, (Qc ∘ₗ u_op ∘ₗ Q ∘ₗ ρ) (b i)⟫_ℂ
            = ⟪b i, (ev i : ℂ) • Qc (u_op (Q (b i)))⟫_ℂ := by
                simp [LinearMap.comp_apply, hρb i]
        _ = (ev i : ℂ) * ⟪b i, Qc (u_op (Q (b i)))⟫_ℂ := by
              simpa using
                (inner_smul_right (x := b i) (r := (ev i : ℂ))
                  (y := Qc (u_op (Q (b i)))))
        _ = (ev i : ℂ) * ⟪b i, (Qc ∘ₗ u_op ∘ₗ Q) (b i)⟫_ℂ := by rfl
    -- Step 3: bound the norm
    rw [hcyc_trace, hexpand]
    calc ‖∑ i, (ev i : ℂ) * ⟪b i, (Qc ∘ₗ u_op ∘ₗ Q) (b i)⟫_ℂ‖
        ≤ ∑ i, ‖(ev i : ℂ) * ⟪b i, (Qc ∘ₗ u_op ∘ₗ Q) (b i)⟫_ℂ‖ :=
            norm_sum_le _ _
      _ = ∑ i, ev i * ‖⟪b i, (Qc ∘ₗ u_op ∘ₗ Q) (b i)⟫_ℂ‖ := by
              congr 1; ext i
              rw [norm_mul]
              simp [Complex.norm_real, abs_of_nonneg (hev_nn i)]
      -- |⟨b_i, Qc(u(Q(b_i)))⟩| ≤ ‖Qc b_i‖.
      _ ≤ ∑ i, ev i * ‖Qc (b i)‖ := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have hadj_inner : ⟪b i, (Qc ∘ₗ u_op ∘ₗ Q) (b i)⟫_ℂ
                  = ⟪Qc (b i), (u_op ∘ₗ Q) (b i)⟫_ℂ := by
                simpa [LinearMap.comp_apply, hQc_adj] using
                  (LinearMap.adjoint_inner_right Qc
                    (x := b i) (y := (u_op ∘ₗ Q) (b i)))
              have hterm :
                  ‖⟪b i, (Qc ∘ₗ u_op ∘ₗ Q) (b i)⟫_ℂ‖ ≤ ‖Qc (b i)‖ := by
                rw [hadj_inner]
                calc
                  ‖⟪Qc (b i), (u_op ∘ₗ Q) (b i)⟫_ℂ‖
                      ≤ ‖Qc (b i)‖ * ‖(u_op ∘ₗ Q) (b i)‖ := norm_inner_le_norm _ _
                  _ = ‖Qc (b i)‖ * ‖(u : H →L[ℂ] H) (Q (b i))‖ := by
                        rfl
                  _ = ‖Qc (b i)‖ * ‖Q (b i)‖ := by
                        rw [Unitary.norm_map u]
                  _ ≤ ‖Qc (b i)‖ * ‖b i‖ := by
                        gcongr
                        exact hQ_contr (b i)
                  _ = ‖Qc (b i)‖ := by
                        simp [b.orthonormal.1 i]
              exact mul_le_mul_of_nonneg_left hterm (hev_nn i)
      -- Weighted Cauchy-Schwarz.
      _ ≤ Real.sqrt (Complex.re (trace (H := H) (Qc ∘ₗ ρ ∘ₗ Qc))) := by
              have hsum_nonneg : 0 ≤ ∑ i : Fin n, ev i * ‖Qc (b i)‖ := by
                exact Finset.sum_nonneg (fun i _ => mul_nonneg (hev_nn i) (norm_nonneg _))
              have hsq :
                  (∑ i : Fin n, ev i * ‖Qc (b i)‖) ^ 2
                    ≤ Complex.re (trace (H := H) (Qc ∘ₗ ρ ∘ₗ Qc)) := by
                have hcs :
                    (∑ i : Fin n, ev i * ‖Qc (b i)‖) ^ 2
                      ≤ (∑ i : Fin n, ev i) * ∑ i : Fin n, ev i * ‖Qc (b i)‖ ^ 2 := by
                  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
                    (Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (s := Finset.univ)
                      (r := fun i : Fin n => ev i * ‖Qc (b i)‖)
                      (f := fun i : Fin n => ev i)
                      (g := fun i : Fin n => ev i * ‖Qc (b i)‖ ^ 2)
                      (hf := fun i _ => hev_nn i)
                      (hg := fun i _ => mul_nonneg (hev_nn i) (sq_nonneg _))
                      (ht := by
                        intro i hi
                        ring))
                calc
                  (∑ i : Fin n, ev i * ‖Qc (b i)‖) ^ 2
                      ≤ (∑ i : Fin n, ev i) * ∑ i : Fin n, ev i * ‖Qc (b i)‖ ^ 2 := hcs
                  _ = 1 * (∑ i : Fin n, ev i * ‖Qc (b i)‖ ^ 2) := by rw [hsum_ev]
                  _ = Complex.re (trace (H := H) (Qc ∘ₗ ρ ∘ₗ Qc)) := by simp [hsum_norm_sq]
              exact (Real.le_sqrt hsum_nonneg h1p_nn).2 hsq

/--
Cross-term bound (reversed order): for orthogonal projectors `Q, Qc` and a density operator `ρ`,
`‖Qc ρ Q‖₁ ≤ √(Re Tr(Qc ρ Qc))`.
-/
private lemma traceNorm_cross_rev_le_sqrt_trace
    {H : Type*} [CpxFiniteHilbert H]
    {Q Qc : Operator H}
    (hQ_adj : LinearMap.adjoint Q = Q)
    (hQ_idem : Q ∘ₗ Q = Q)
    (hQc_adj : LinearMap.adjoint Qc = Qc)
    (hQc_idem : Qc ∘ₗ Qc = Qc)
    (_hQQc : Q ∘ₗ Qc = 0)
    {ρ : Operator H}
    (hρ_herm : IsHermitian ρ)
    (hρ_pos : ρ.IsPositive)
    (hρ_tr : trace ρ = 1) :
    traceNorm (H := H) (Qc ∘ₗ ρ ∘ₗ Q) ≤
      Real.sqrt (Complex.re (trace (H := H) (Qc ∘ₗ ρ ∘ₗ Qc))) := by
  let n := Module.finrank ℂ H
  let b : OrthonormalBasis (Fin n) ℂ H := hρ_herm.eigenvectorBasis rfl
  let ev : Fin n → ℝ := hρ_herm.eigenvalues rfl
  have hev_nn : ∀ i, 0 ≤ ev i := fun i => by
    simpa using hρ_pos.nonneg_eigenvalues rfl i
  have hρb : ∀ i, ρ (b i) = (ev i : ℂ) • b i :=
    hρ_herm.apply_eigenvectorBasis rfl
  have hQc_contr : ∀ x : H, ‖Qc x‖ ≤ ‖x‖ := by
    intro x
    have hadj : (LinearMap.adjoint Qc) (Qc x) = Qc x := by
      rw [hQc_adj]
      exact LinearMap.congr_fun hQc_idem x
    have hinner' : ⟪(LinearMap.adjoint Qc) (Qc x), x⟫_ℂ = ⟪Qc x, Qc x⟫_ℂ :=
      LinearMap.adjoint_inner_left Qc (x := x) (y := Qc x)
    have hinner : ⟪Qc x, x⟫_ℂ = ⟪Qc x, Qc x⟫_ℂ := by
      calc
        ⟪Qc x, x⟫_ℂ = ⟪(LinearMap.adjoint Qc) (Qc x), x⟫_ℂ :=
          congrArg (fun z => ⟪z, x⟫_ℂ) hadj.symm
        _ = ⟪Qc x, Qc x⟫_ℂ := hinner'
    have hsq : ‖Qc x‖ ^ 2 ≤ ‖Qc x‖ * ‖x‖ := by
      calc
        ‖Qc x‖ ^ 2 = ‖⟪Qc x, Qc x⟫_ℂ‖ := by
          rw [inner_self_eq_norm_sq_to_K]
          simp [Complex.norm_real]
        _ = ‖⟪Qc x, x⟫_ℂ‖ := by rw [hinner]
        _ ≤ ‖Qc x‖ * ‖x‖ := norm_inner_le_norm _ _
    nlinarith [norm_nonneg (Qc x), norm_nonneg x, hsq]
  have hQ_contr : ∀ x : H, ‖Q x‖ ≤ ‖x‖ := by
    intro x
    have hadj : (LinearMap.adjoint Q) (Q x) = Q x := by
      rw [hQ_adj]
      exact LinearMap.congr_fun hQ_idem x
    have hinner' : ⟪(LinearMap.adjoint Q) (Q x), x⟫_ℂ = ⟪Q x, Q x⟫_ℂ :=
      LinearMap.adjoint_inner_left Q (x := x) (y := Q x)
    have hinner : ⟪Q x, x⟫_ℂ = ⟪Q x, Q x⟫_ℂ := by
      calc
        ⟪Q x, x⟫_ℂ = ⟪(LinearMap.adjoint Q) (Q x), x⟫_ℂ :=
          congrArg (fun z => ⟪z, x⟫_ℂ) hadj.symm
        _ = ⟪Q x, Q x⟫_ℂ := hinner'
    have hsq : ‖Q x‖ ^ 2 ≤ ‖Q x‖ * ‖x‖ := by
      calc
        ‖Q x‖ ^ 2 = ‖⟪Q x, Q x⟫_ℂ‖ := by
          rw [inner_self_eq_norm_sq_to_K]
          simp [Complex.norm_real]
        _ = ‖⟪Q x, x⟫_ℂ‖ := by rw [hinner]
        _ ≤ ‖Q x‖ * ‖x‖ := norm_inner_le_norm _ _
    nlinarith [norm_nonneg (Q x), norm_nonneg x, hsq]
  have hre_norm_Qc : ∀ i, ‖Qc (b i)‖ ^ 2 = Complex.re ⟪b i, Qc (b i)⟫_ℂ := by
    intro i
    have hadj : LinearMap.adjoint Qc (Qc (b i)) = Qc (b i) := by
      rw [hQc_adj]
      exact LinearMap.congr_fun hQc_idem (b i)
    have hinner' : ⟪LinearMap.adjoint Qc (Qc (b i)), b i⟫_ℂ = ⟪Qc (b i), Qc (b i)⟫_ℂ :=
      LinearMap.adjoint_inner_left Qc (x := b i) (y := Qc (b i))
    have hinner : ⟪Qc (b i), b i⟫_ℂ = ⟪Qc (b i), Qc (b i)⟫_ℂ := by
      calc
        ⟪Qc (b i), b i⟫_ℂ = ⟪LinearMap.adjoint Qc (Qc (b i)), b i⟫_ℂ :=
          congrArg (fun z => ⟪z, b i⟫_ℂ) hadj.symm
        _ = ⟪Qc (b i), Qc (b i)⟫_ℂ := hinner'
    calc
      ‖Qc (b i)‖ ^ 2 = Complex.re ⟪Qc (b i), Qc (b i)⟫_ℂ := by
        simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (x := Qc (b i))).symm
      _ = Complex.re ⟪Qc (b i), b i⟫_ℂ := by rw [hinner]
      _ = Complex.re ⟪b i, Qc (b i)⟫_ℂ := by
        simpa using (inner_re_symm (𝕜 := ℂ) (x := Qc (b i)) (y := b i))
  have hsum_norm_sq : ∑ i : Fin n, ev i * ‖Qc (b i)‖ ^ 2 =
      Complex.re (trace (H := H) (Qc ∘ₗ ρ ∘ₗ Qc)) := by
    simp_rw [hre_norm_Qc]
    have hterm : ∀ i : Fin n,
        ev i * Complex.re ⟪b i, Qc (b i)⟫_ℂ =
          Complex.re ⟪b i, (Qc ∘ₗ ρ) (b i)⟫_ℂ := by
      intro i
      rw [LinearMap.comp_apply, hρb i, map_smul, inner_smul_right]
      simp [Complex.mul_re]
    have hstep : ∑ i : Fin n, ev i * Complex.re ⟪b i, Qc (b i)⟫_ℂ =
        ∑ i : Fin n, Complex.re ⟪b i, (Qc ∘ₗ ρ) (b i)⟫_ℂ := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact hterm i
    rw [hstep]
    have hsum_re : (∑ i : Fin n, Complex.re ⟪b i, (Qc ∘ₗ ρ) (b i)⟫_ℂ)
        = Complex.re (∑ i : Fin n, ⟪b i, (Qc ∘ₗ ρ) (b i)⟫_ℂ) := by
      simp
    rw [hsum_re]
    have htr_QcRho : trace (H := H) (Qc ∘ₗ ρ)
        = ∑ i, ⟪b i, (Qc ∘ₗ ρ) (b i)⟫_ℂ := by
      simp [trace, LinearMap.trace_eq_sum_inner _ b]
    have htr_eq : trace (H := H) (Qc ∘ₗ ρ ∘ₗ Qc) = trace (H := H) (Qc ∘ₗ ρ) := by
      calc
        trace (H := H) (Qc ∘ₗ ρ ∘ₗ Qc)
            = trace (H := H) ((Qc ∘ₗ ρ) ∘ₗ Qc) := by rfl
        _ = trace (H := H) (Qc ∘ₗ (Qc ∘ₗ ρ)) := by
              simpa [Module.End.mul_eq_comp] using
                LinearMap.trace_mul_comm ℂ (Qc ∘ₗ ρ) Qc
        _ = trace (H := H) ((Qc ∘ₗ Qc) ∘ₗ ρ) := by
              simp [LinearMap.comp_assoc]
        _ = trace (H := H) (Qc ∘ₗ ρ) := by
              simp [hQc_idem]
    simpa [htr_QcRho] using (congrArg Complex.re htr_eq).symm
  have hsum_ev : ∑ i : Fin n, ev i = 1 := by
    have : Complex.re (trace (H := H) ρ) = 1 := by simp [hρ_tr]
    rw [← this]
    rw [show trace (H := H) ρ = ∑ i, ⟪b i, ρ (b i)⟫_ℂ from by
      simp [trace, LinearMap.trace_eq_sum_inner _ b]]
    simp_rw [hρb, inner_smul_right]
    simp [b.orthonormal.1, Complex.ofReal_re]
  have h1p_nn : 0 ≤ Complex.re (trace (H := H) (Qc ∘ₗ ρ ∘ₗ Qc)) := by
    rw [← hsum_norm_sq]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (hev_nn i) (sq_nonneg _)
  rw [trace_variational (Qc ∘ₗ ρ ∘ₗ Q)]
  apply csSup_le
  · exact ⟨_, 1, rfl⟩
  · rintro r ⟨u, rfl⟩
    let u_op : Operator H := ((u : H →L[ℂ] H) : Operator H)
    have hcyc_trace :
        trace (H := H) (u_op ∘ₗ Qc ∘ₗ ρ ∘ₗ Q)
          = trace (H := H) (Q ∘ₗ u_op ∘ₗ Qc ∘ₗ ρ) := by
      calc
        trace (H := H) (u_op ∘ₗ Qc ∘ₗ ρ ∘ₗ Q)
            = trace (H := H) ((u_op ∘ₗ Qc ∘ₗ ρ) ∘ₗ Q) := by rfl
        _ = trace (H := H) (Q ∘ₗ (u_op ∘ₗ Qc ∘ₗ ρ)) := by
              simpa [LinearMap.comp_assoc, Module.End.mul_eq_comp] using
                LinearMap.trace_mul_comm ℂ (u_op ∘ₗ Qc ∘ₗ ρ) Q
        _ = trace (H := H) (Q ∘ₗ u_op ∘ₗ Qc ∘ₗ ρ) := by
              simp
    have hexpand :
        trace (H := H) (Q ∘ₗ u_op ∘ₗ Qc ∘ₗ ρ)
          = ∑ i, (ev i : ℂ) * ⟪b i, (Q ∘ₗ u_op ∘ₗ Qc) (b i)⟫_ℂ := by
      have htrace : trace (H := H) (Q ∘ₗ u_op ∘ₗ Qc ∘ₗ ρ)
          = ∑ i, ⟪b i, (Q ∘ₗ u_op ∘ₗ Qc ∘ₗ ρ) (b i)⟫_ℂ := by
        simp [trace, LinearMap.trace_eq_sum_inner _ b]
      rw [htrace]
      congr 1; ext i
      calc
        ⟪b i, (Q ∘ₗ u_op ∘ₗ Qc ∘ₗ ρ) (b i)⟫_ℂ
            = ⟪b i, (ev i : ℂ) • Q (u_op (Qc (b i)))⟫_ℂ := by
                simp [LinearMap.comp_apply, hρb i]
        _ = (ev i : ℂ) * ⟪b i, Q (u_op (Qc (b i)))⟫_ℂ := by
              simpa using
                (inner_smul_right (x := b i) (r := (ev i : ℂ))
                  (y := Q (u_op (Qc (b i)))))
        _ = (ev i : ℂ) * ⟪b i, (Q ∘ₗ u_op ∘ₗ Qc) (b i)⟫_ℂ := by rfl
    rw [hcyc_trace, hexpand]
    calc ‖∑ i, (ev i : ℂ) * ⟪b i, (Q ∘ₗ u_op ∘ₗ Qc) (b i)⟫_ℂ‖
        ≤ ∑ i, ‖(ev i : ℂ) * ⟪b i, (Q ∘ₗ u_op ∘ₗ Qc) (b i)⟫_ℂ‖ :=
            norm_sum_le _ _
      _ = ∑ i, ev i * ‖⟪b i, (Q ∘ₗ u_op ∘ₗ Qc) (b i)⟫_ℂ‖ := by
              congr 1; ext i
              rw [norm_mul]
              simp [Complex.norm_real, abs_of_nonneg (hev_nn i)]
      _ ≤ ∑ i, ev i * ‖Qc (b i)‖ := by
              refine Finset.sum_le_sum ?_
              intro i hi
              have hadj_inner : ⟪b i, (Q ∘ₗ u_op ∘ₗ Qc) (b i)⟫_ℂ
                  = ⟪Q (b i), (u_op ∘ₗ Qc) (b i)⟫_ℂ := by
                simpa [LinearMap.comp_apply, hQ_adj] using
                  (LinearMap.adjoint_inner_right Q
                    (x := b i) (y := (u_op ∘ₗ Qc) (b i)))
              have hterm :
                  ‖⟪b i, (Q ∘ₗ u_op ∘ₗ Qc) (b i)⟫_ℂ‖ ≤ ‖Qc (b i)‖ := by
                rw [hadj_inner]
                calc
                  ‖⟪Q (b i), (u_op ∘ₗ Qc) (b i)⟫_ℂ‖
                      ≤ ‖Q (b i)‖ * ‖(u_op ∘ₗ Qc) (b i)‖ := norm_inner_le_norm _ _
                  _ = ‖Q (b i)‖ * ‖(u : H →L[ℂ] H) (Qc (b i))‖ := by
                        rfl
                  _ = ‖Q (b i)‖ * ‖Qc (b i)‖ := by
                        rw [Unitary.norm_map u]
                  _ ≤ ‖b i‖ * ‖Qc (b i)‖ := by
                        gcongr
                        exact hQ_contr (b i)
                  _ = ‖Qc (b i)‖ := by
                        simp [b.orthonormal.1 i]
              exact mul_le_mul_of_nonneg_left hterm (hev_nn i)
      _ ≤ Real.sqrt (Complex.re (trace (H := H) (Qc ∘ₗ ρ ∘ₗ Qc))) := by
              have hsum_nonneg : 0 ≤ ∑ i : Fin n, ev i * ‖Qc (b i)‖ := by
                exact Finset.sum_nonneg (fun i _ => mul_nonneg (hev_nn i) (norm_nonneg _))
              have hsq :
                  (∑ i : Fin n, ev i * ‖Qc (b i)‖) ^ 2
                    ≤ Complex.re (trace (H := H) (Qc ∘ₗ ρ ∘ₗ Qc)) := by
                have hcs :
                    (∑ i : Fin n, ev i * ‖Qc (b i)‖) ^ 2
                      ≤ (∑ i : Fin n, ev i) * ∑ i : Fin n, ev i * ‖Qc (b i)‖ ^ 2 := by
                  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
                    (Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul (s := Finset.univ)
                      (r := fun i : Fin n => ev i * ‖Qc (b i)‖)
                      (f := fun i : Fin n => ev i)
                      (g := fun i : Fin n => ev i * ‖Qc (b i)‖ ^ 2)
                      (hf := fun i _ => hev_nn i)
                      (hg := fun i _ => mul_nonneg (hev_nn i) (sq_nonneg _))
                      (ht := by
                        intro i hi
                        ring))
                calc
                  (∑ i : Fin n, ev i * ‖Qc (b i)‖) ^ 2
                      ≤ (∑ i : Fin n, ev i) * ∑ i : Fin n, ev i * ‖Qc (b i)‖ ^ 2 := hcs
                  _ = 1 * (∑ i : Fin n, ev i * ‖Qc (b i)‖ ^ 2) := by rw [hsum_ev]
                  _ = Complex.re (trace (H := H) (Qc ∘ₗ ρ ∘ₗ Qc)) := by simp [hsum_norm_sq]
              exact (Real.le_sqrt hsum_nonneg h1p_nn).2 hsq


/-- First piece: `‖ρ − ΠρΠ‖₁ ≤ 2√(1−p) + (1−p)`.
Proof sketch: write `Π⊥ = I − Π` and decompose
  `ρ − ΠρΠ = Π ρ Π⊥ + Π⊥ ρ Π + Π⊥ ρ Π⊥`.
Schatten-2 gives `‖Π ρ Π⊥‖₁, ‖Π⊥ ρ Π‖₁ ≤ √(1−p)` and
`‖Π⊥ ρ Π⊥‖₁ = 1−p`. -/
private lemma traceNorm_rho_sub_postselectUnnormalized_le
    {E : Type} [CpxFiniteHilbert E]
    (ρABE : DensityOperator (ABESystem E)) :
    traceNorm (H := ABESystem E)
      ((ρABE : Operator (ABESystem E)) -
        postselectUnnormalized (E := E) (ρABE : Operator (ABESystem E))) ≤
      2 * Real.sqrt
          (1 - Complex.re (postselectSuccessC (E := E) (ρABE : Operator (ABESystem E)))) +
        (1 - Complex.re (postselectSuccessC (E := E) (ρABE : Operator (ABESystem E)))) := by
  let ρ : Operator (ABESystem E) := (ρABE : Operator (ABESystem E))
  let P : Operator (ABESystem E) := postselectProjector (E := E)
  let Pc : Operator (ABESystem E) := (LinearMap.id : Operator (ABESystem E)) - P
  let p : Real := Complex.re (postselectSuccessC (E := E) ρ)
  have hP_idem : P ∘ₗ P = P := by
    simpa [P] using (postselectProjector_idempotent (E := E))
  have hρ_herm : IsHermitian ρ := by
    simpa [ρ] using ρABE.isHermitian
  have hρ_pos : ρ.IsPositive := IsPSD.isPositive ρABE.isHermitian ρABE.isPSD
  have hρ_tr : trace (H := ABESystem E) ρ = 1 := by
    simpa [ρ] using ρABE.trace_one
  -- set_option trace.profiler true in
  have hPadj : LinearMap.adjoint P = P := by
    simp [P, postselectProjector, pureOp]
  have hPcadj : LinearMap.adjoint Pc = Pc := by
    simp [Pc, hPadj]
  have hPc_idem : Pc ∘ₗ Pc = Pc := by
    apply LinearMap.ext
    intro z
    have hPidem_app : P (P z) = P z := LinearMap.congr_fun hP_idem z
    simp [Pc, hPidem_app]
  have hPPc : P ∘ₗ Pc = 0 := by
    apply LinearMap.ext
    intro z
    have hPidem_app : P (P z) = P z := LinearMap.congr_fun hP_idem z
    simp [Pc, hPidem_app]
  have hpost : postselectUnnormalized (E := E) ρ = P ∘ₗ ρ ∘ₗ P := by
    rfl
  have hdecomp :
      ρ - postselectUnnormalized (E := E) ρ
        = (P ∘ₗ ρ ∘ₗ Pc) + (Pc ∘ₗ ρ ∘ₗ P) + (Pc ∘ₗ ρ ∘ₗ Pc) := by
    rw [hpost]
    ext ψ
    simp [Pc]
    abel
  have hcross1 :
      traceNorm (H := ABESystem E) (P ∘ₗ ρ ∘ₗ Pc)
        ≤ Real.sqrt (Complex.re (trace (H := ABESystem E) (Pc ∘ₗ ρ ∘ₗ Pc))) := by
    exact
      (traceNorm_cross_le_sqrt_trace (H := ABESystem E)
        (Q := P) (Qc := Pc) (ρ := ρ)
        hPadj hP_idem hPcadj hPc_idem hPPc
        (hρ_herm := hρ_herm) (hρ_pos := hρ_pos) (hρ_tr := hρ_tr))
  have hcross2 :
      traceNorm (H := ABESystem E) (Pc ∘ₗ ρ ∘ₗ P)
        ≤ Real.sqrt (Complex.re (trace (H := ABESystem E) (Pc ∘ₗ ρ ∘ₗ Pc))) := by
    exact
      (traceNorm_cross_rev_le_sqrt_trace (H := ABESystem E)
        (Q := P) (Qc := Pc) (ρ := ρ)
        hPadj hP_idem hPcadj hPc_idem hPPc
        (hρ_herm := hρ_herm) (hρ_pos := hρ_pos) (hρ_tr := hρ_tr))
  have htrPc_re :
      Complex.re (trace (H := ABESystem E) (Pc ∘ₗ ρ ∘ₗ Pc)) = 1 - p := by
    have htr_eq :
        trace (H := ABESystem E) (Pc ∘ₗ ρ ∘ₗ Pc)
          = 1 - postselectSuccessC (E := E) ρ := by
      calc
        trace (H := ABESystem E) (Pc ∘ₗ ρ ∘ₗ Pc)
            = trace (H := ABESystem E) (Pc ∘ₗ (Pc ∘ₗ ρ)) := by
                simpa [LinearMap.comp_assoc] using
                  (LinearMap.trace_mul_comm ℂ (Pc ∘ₗ ρ) Pc)
        _ = trace (H := ABESystem E) ((Pc ∘ₗ Pc) ∘ₗ ρ) := by
              simp [LinearMap.comp_assoc]
        _ = trace (H := ABESystem E) (Pc ∘ₗ ρ) := by
              simp [hPc_idem]
        _ = trace (H := ABESystem E) (((LinearMap.id : Operator (ABESystem E)) - P) ∘ₗ ρ) := by
              rfl
        _ = trace (H := ABESystem E) ρ - trace (H := ABESystem E) (P ∘ₗ ρ) := by
              simp [LinearMap.sub_comp, trace]
        _ = 1 - postselectSuccessC (E := E) ρ := by
              simp [ρ, P, postselectSuccessC, hρ_tr]
    simp [htr_eq, p]
  have hdiag :
      traceNorm (H := ABESystem E) (Pc ∘ₗ ρ ∘ₗ Pc) ≤ 1 - p := by
    have hX_pos : (Pc ∘ₗ ρ ∘ₗ Pc).IsPositive := by
      simpa [hPcadj] using LinearMap.IsPositive.conj_adjoint (hT := hρ_pos) (S := Pc)
    have htr_le :
        traceNorm (H := ABESystem E) (Pc ∘ₗ ρ ∘ₗ Pc)
          ≤ Complex.re (trace (H := ABESystem E) (Pc ∘ₗ ρ ∘ₗ Pc)) :=
      traceNorm_le_re_trace_of_isPositive (H := ABESystem E) hX_pos
    exact htr_le.trans_eq htrPc_re
  calc
    traceNorm (H := ABESystem E) (ρ - postselectUnnormalized (E := E) ρ)
        = traceNorm (H := ABESystem E)
            ((P ∘ₗ ρ ∘ₗ Pc) + (Pc ∘ₗ ρ ∘ₗ P) + (Pc ∘ₗ ρ ∘ₗ Pc)) := by
              simp [hdecomp]
    _ = traceNorm (H := ABESystem E)
          (((P ∘ₗ ρ ∘ₗ Pc) + (Pc ∘ₗ ρ ∘ₗ P)) + (Pc ∘ₗ ρ ∘ₗ Pc)) := by
          abel
    _ ≤ traceNorm (H := ABESystem E) ((P ∘ₗ ρ ∘ₗ Pc) + (Pc ∘ₗ ρ ∘ₗ P))
          + traceNorm (H := ABESystem E) (Pc ∘ₗ ρ ∘ₗ Pc) := by
            simpa using
              (traceNorm_add_le (H := ABESystem E)
                ((P ∘ₗ ρ ∘ₗ Pc) + (Pc ∘ₗ ρ ∘ₗ P))
                (Pc ∘ₗ ρ ∘ₗ Pc))
    _ ≤ (traceNorm (H := ABESystem E) (P ∘ₗ ρ ∘ₗ Pc)
            + traceNorm (H := ABESystem E) (Pc ∘ₗ ρ ∘ₗ P))
          + traceNorm (H := ABESystem E) (Pc ∘ₗ ρ ∘ₗ Pc) := by
            gcongr
            simpa using
              (traceNorm_add_le (H := ABESystem E) (P ∘ₗ ρ ∘ₗ Pc) (Pc ∘ₗ ρ ∘ₗ P))
    _ ≤ (Real.sqrt (Complex.re (trace (H := ABESystem E) (Pc ∘ₗ ρ ∘ₗ Pc))) +
          Real.sqrt (Complex.re (trace (H := ABESystem E) (Pc ∘ₗ ρ ∘ₗ Pc)))) + (1 - p) := by
          linarith [hcross1, hcross2, hdiag]
    _ = (Real.sqrt (1 - p) + Real.sqrt (1 - p)) + (1 - p) := by
          simp [htrPc_re]
    _ = 2 * Real.sqrt (1 - p) + (1 - p) := by ring

set_option maxHeartbeats 12000000 in
/-- Second piece: `‖ΠρΠ − ρ̃‖₁ = 1 − p`.
Proof sketch: `ΠρΠ − ρ̃ = (1 − p⁻¹) · ΠρΠ`; then
`‖(1 − p⁻¹) · ΠρΠ‖₁ = |1 − p⁻¹| · Tr(ΠρΠ) = |1 − p⁻¹| · p = 1 − p`. -/
private lemma traceNorm_postselectUnnormalized_sub_state_eq
    {E : Type} [CpxFiniteHilbert E]
    (ρABE : DensityOperator (ABESystem E))
    (hSucc : postselectSuccessC (E := E) (ρABE : Operator (ABESystem E)) ≠ 0) :
    traceNorm (H := ABESystem E)
      (postselectUnnormalized (E := E) (ρABE : Operator (ABESystem E)) -
        postselectState (E := E) (ρABE : Operator (ABESystem E))) =
      1 - Complex.re (postselectSuccessC (E := E) (ρABE : Operator (ABESystem E))) := by
  let ρ : Operator (ABESystem E) := (ρABE : Operator (ABESystem E))
  let P : Operator (ABESystem E) := postselectProjector (E := E)
  let U : Operator (ABESystem E) := postselectUnnormalized (E := E) ρ
  let s : ℂ := postselectSuccessC (E := E) ρ
  let p : ℝ := Complex.re s
  have hs_ne : s ≠ 0 := by simpa [s, ρ] using hSucc
  have hρ_pos : ρ.IsPositive := IsPSD.isPositive ρABE.isHermitian ρABE.isPSD
  have hPadj : LinearMap.adjoint P = P := by simp [P, postselectProjector, pureOp]
  have hU_pos : U.IsPositive := by
    simpa [U, ρ, hPadj] using LinearMap.IsPositive.conj_adjoint (hT := hρ_pos) (S := P)
  have hU_trace : trace (H := ABESystem E) U = s := by
    simpa [U, s, ρ] using (trace_postselectUnnormalized (E := E) ρ)
  -- p is real-valued: s = ↑p (trace of a positive operator)
  have hs_real : s = (p : ℂ) := by
    have hcast : trace (H := ABESystem E) U =
        ↑(∑ i : Fin _, hU_pos.isSymmetric.eigenvalues (hn := rfl) i) := by
      simpa [trace] using hU_pos.isSymmetric.trace_eq_sum_eigenvalues (hn := rfl)
    have hre : p = ∑ i : Fin _, hU_pos.isSymmetric.eigenvalues (hn := rfl) i := by
      simpa [p, trace, ← hU_trace] using hU_pos.isSymmetric.re_trace_eq_sum_eigenvalues (hn := rfl)
    rw [← hU_trace, hcast, ← hre]
  -- 0 ≤ p: non-negativity via traceNorm sandwich 0 ≤ ‖tr U‖ ≤ ‖U‖₁ ≤ Re(tr U) = p
  have hp_nonneg : 0 ≤ p := by
    have hsum_nonneg :
        0 ≤ ∑ i : Fin (Module.finrank ℂ (ABESystem E)),
            hU_pos.isSymmetric.eigenvalues (hn := rfl) i := by
      exact Finset.sum_nonneg (fun i _ => hU_pos.nonneg_eigenvalues (hn := rfl) i)
    have htr_re :
        Complex.re (trace (H := ABESystem E) U)
          = ∑ i : Fin (Module.finrank ℂ (ABESystem E)),
              hU_pos.isSymmetric.eigenvalues (hn := rfl) i := by
      simpa [trace] using hU_pos.isSymmetric.re_trace_eq_sum_eigenvalues (hn := rfl)
    have hre_trace_nonneg : 0 ≤ Complex.re (trace (H := ABESystem E) U) := by
      simpa [htr_re] using hsum_nonneg
    simpa [p, hU_trace] using hre_trace_nonneg
  have hp_pos : 0 < p :=
    lt_of_le_of_ne hp_nonneg (Ne.symm fun h0 => hs_ne (by rw [hs_real, h0]; simp))
  -- p ≤ 1: complementary projector Pc = I − P has Tr(Pc ρ Pc) = 1 − p ≥ 0
  have hp_le_one : p ≤ 1 := by
    let Pc : Operator (ABESystem E) := (LinearMap.id : Operator (ABESystem E)) - P
    have hP_idem : P ∘ₗ P = P := by simpa [P] using postselectProjector_idempotent (E := E)
    have hPcadj : LinearMap.adjoint Pc = Pc := by simp [Pc, hPadj]
    have hPc_idem : Pc ∘ₗ Pc = Pc := by
      apply LinearMap.ext
      intro z
      have hPidem_app : P (P z) = P z := LinearMap.congr_fun hP_idem z
      simp [Pc, hPidem_app]
    have hPc_pos : (Pc ∘ₗ ρ ∘ₗ Pc).IsPositive := by
      simpa [hPcadj] using LinearMap.IsPositive.conj_adjoint (hT := hρ_pos) (S := Pc)
    have hPc_trace_re_nonneg : 0 ≤ Complex.re (trace (H := ABESystem E) (Pc ∘ₗ ρ ∘ₗ Pc)) := by
      have hsum_nonneg :
          0 ≤ ∑ i : Fin (Module.finrank ℂ (ABESystem E)),
              hPc_pos.isSymmetric.eigenvalues (hn := rfl) i := by
        exact Finset.sum_nonneg (fun i _ => hPc_pos.nonneg_eigenvalues (hn := rfl) i)
      have htr_re :
          Complex.re (trace (H := ABESystem E) (Pc ∘ₗ ρ ∘ₗ Pc))
            = ∑ i : Fin (Module.finrank ℂ (ABESystem E)),
                hPc_pos.isSymmetric.eigenvalues (hn := rfl) i := by
        simpa [trace] using hPc_pos.isSymmetric.re_trace_eq_sum_eigenvalues (hn := rfl)
      simpa [htr_re] using hsum_nonneg
    have hPc_tr :
        trace (H := ABESystem E) (Pc ∘ₗ ρ ∘ₗ Pc) = 1 - s := by
      calc
        trace (H := ABESystem E) (Pc ∘ₗ ρ ∘ₗ Pc)
            = trace (H := ABESystem E) (Pc ∘ₗ (Pc ∘ₗ ρ)) := by
                simpa [LinearMap.comp_assoc] using
                  (LinearMap.trace_mul_comm ℂ (Pc ∘ₗ ρ) Pc)
        _ = trace (H := ABESystem E) ((Pc ∘ₗ Pc) ∘ₗ ρ) := by
              simp [LinearMap.comp_assoc]
        _ = trace (H := ABESystem E) (Pc ∘ₗ ρ) := by
              simp [hPc_idem]
        _ = trace (H := ABESystem E) (((LinearMap.id : Operator (ABESystem E)) - P) ∘ₗ ρ) := by
              rfl
        _ = trace (H := ABESystem E) ρ - trace (H := ABESystem E) (P ∘ₗ ρ) := by
              simp [LinearMap.sub_comp, trace]
        _ = 1 - s := by
              simp [ρ, P, s, ρABE.trace_one, postselectSuccessC]
    have hPc_re : Complex.re (trace (H := ABESystem E) (Pc ∘ₗ ρ ∘ₗ Pc)) = 1 - p := by
      simp [hPc_tr, p]
    linarith [hPc_trace_re_nonneg, hPc_re]
  -- Main computation: ρ̃ − U = c · U with c = 1/p − 1 ≥ 0, so ‖U − ρ̃‖₁ = Re(tr(c·U)) = c·p = 1−p
  let c : ℝ := (1 / p) - 1
  have hc_nonneg : 0 ≤ c := sub_nonneg.2 ((one_le_div hp_pos).2 hp_le_one)
  have hstate_sub : postselectState (E := E) ρ - U = ((c : ℂ) • U) := by
    have : postselectState (E := E) ρ - U = (((p : ℂ)⁻¹ - 1) • U) := by
      simp [postselectState, U, s, hs_real, sub_smul]
    rw [this]; simp [c, one_div]
  have hstate_sub_pos : (postselectState (E := E) ρ - U).IsPositive := by
    rw [hstate_sub]; exact isPositive_real_smul (H := ABESystem E) hU_pos hc_nonneg
  have hstate_sub_retrace :
      Complex.re (trace (H := ABESystem E) (postselectState (E := E) ρ - U)) = 1 - p := by
    rw [hstate_sub]
    have hReU : Complex.re (trace (H := ABESystem E) U) = p := by
      simp only [p, hU_trace]
    have h : Complex.re (trace (H := ABESystem E) ((c : ℂ) • U)) = c * p := by
      calc
        Complex.re (trace (H := ABESystem E) ((c : ℂ) • U))
            = Complex.re ((c : ℂ) * trace (H := ABESystem E) U) := by
                simp [trace]
        _ = c * Complex.re (trace (H := ABESystem E) U) := by
              simp [Complex.mul_re]
        _ = c * p := by rw [hReU]
    rw [h]; simp only [c, one_div]; field_simp [ne_of_gt hp_pos]
  calc
    traceNorm (H := ABESystem E) (postselectUnnormalized (E := E) ρ - postselectState (E := E) ρ)
        = traceNorm (H := ABESystem E) (postselectState (E := E) ρ - U) := by
          rw [show postselectUnnormalized (E := E) ρ - postselectState (E := E) ρ =
            -(postselectState (E := E) ρ - U) from by simp [U], traceNorm_neg]
      _ = 1 - p := by
            rw [traceNorm_eq_re_trace_of_isPositive hstate_sub_pos, hstate_sub_retrace]
      _ = 1 - Complex.re (postselectSuccessC (E := E) (ρABE : Operator (ABESystem E))) := by
            simp [p, s, ρ]

/--
Lemma 11 (Gentle postselection bound).
Let `Π` and `p = Re Tr(Π ρ_ABE)` be as in Definition 9, and set
`ρ̃_ABE = Π ρ_ABE Π / p`. Then
\[
  \|\rho_{ABE} - \widetilde\rho_{ABE}\|_1 \le 2\sqrt{1-p} + 2(1-p).
\]

Proof sketch:
Write `Π⊥ = I - Π`. Decompose
  `ρ - Π ρ Π = Π ρ Π⊥ + Π⊥ ρ Π + Π⊥ ρ Π⊥`.
Triangle inequality gives three terms:
- `‖Π⊥ ρ Π⊥‖₁ = Tr(Π⊥ ρ) = 1 - p`,
- `‖Π ρ Π⊥‖₁ ≤ √(p(1-p)) ≤ √(1-p)` via Schatten-2 inequality,
- same bound for `‖Π⊥ ρ Π‖₁`.
This gives `‖ρ - Π ρ Π‖₁ ≤ 2√(1-p) + (1-p)`.
Finally `‖Π ρ Π - ρ̃‖₁ = |1-p|` and a second triangle inequality concludes.
-/
theorem gentle_postselection_bound
    {E : Type} [CpxFiniteHilbert E]
    (ρABE : DensityOperator (ABESystem E))
    (hSucc : postselectSuccessC (E := E) (ρABE : Operator (ABESystem E)) ≠ 0) :
    let p := Complex.re (postselectSuccessC (E := E) (ρABE : Operator (ABESystem E)))
    traceNorm (H := ABESystem E)
        ((ρABE : Operator (ABESystem E)) -
          postselectState (E := E) (ρABE : Operator (ABESystem E)))
      ≤ 2 * Real.sqrt (1 - p) + 2 * (1 - p) := by
  intro p
  let ρ : Operator (ABESystem E) := (ρABE : Operator (ABESystem E))
  let ρu : Operator (ABESystem E) := postselectUnnormalized (E := E) ρ
  let ρn : Operator (ABESystem E) := postselectState (E := E) ρ
  have hfirst :
      traceNorm (H := ABESystem E) (ρ - ρu)
        ≤ 2 * Real.sqrt (1 - p) + (1 - p) := by
    simpa [ρ, ρu, p] using (traceNorm_rho_sub_postselectUnnormalized_le (E := E) ρABE)
  have hsecond :
      traceNorm (H := ABESystem E) (ρu - ρn) = 1 - p := by
    simpa [ρ, ρu, ρn, p] using
      (traceNorm_postselectUnnormalized_sub_state_eq (E := E) ρABE hSucc)
  have hmain :
      traceNorm (H := ABESystem E) (ρ - ρn) ≤
        2 * Real.sqrt (1 - p) + 2 * (1 - p) := by
    calc
      traceNorm (H := ABESystem E) (ρ - ρn)
          = traceNorm (H := ABESystem E) ((ρ - ρu) + (ρu - ρn)) := by
              congr 1; abel
      _ ≤ traceNorm (H := ABESystem E) (ρ - ρu) +
            traceNorm (H := ABESystem E) (ρu - ρn) := by
              simpa using traceNorm_add_le (H := ABESystem E) (ρ - ρu) (ρu - ρn)
      _ = traceNorm (H := ABESystem E) (ρ - ρu) + (1 - p) := by
            rw [hsecond]
      _ ≤ (2 * Real.sqrt (1 - p) + (1 - p)) + (1 - p) := by
            linarith [hfirst]
      _ = 2 * Real.sqrt (1 - p) + 2 * (1 - p) := by
            ring
  simpa [ρ, ρn] using hmain

end Entropy_Bound
