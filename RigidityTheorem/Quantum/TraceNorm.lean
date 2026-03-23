import Quantum.Density


open scoped TensorProduct InnerProductSpace

namespace Quantum

section traceNorm

section SpectralSetup

/-- `√(X†X)` is Hermitian. -/
lemma isHermitian_operatorSqrt_adjoint_mul_self {H : Type*}
    [CpxFiniteHilbert H]
    (X : Operator H) :
    IsHermitian (operatorSqrt ((LinearMap.adjoint X) ∘ₗ X)) := by
  let Xc : H →L[ℂ] H :=
    LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := H) (F' := H) ((LinearMap.adjoint X) ∘ₗ X)
  have hXc_symm : (Xc : H →ₗ[ℂ] H).IsSymmetric := by
    simpa [Xc] using (LinearMap.isSymmetric_adjoint_mul_self X)
  have hXc_sa : IsSelfAdjoint Xc := hXc_symm.isSelfAdjoint
  have hSqrt_sa : IsSelfAdjoint (cfcₙ (Real.sqrt) Xc) := IsSelfAdjoint.cfcₙ
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric
      (A := cfcₙ (Real.sqrt) Xc)).1 <| by simp

/-- Singular values of an operator, listed in decreasing order as eigenvalues of `√(X†X)`. -/
noncomputable def singularValues {H : Type*}
    [CpxFiniteHilbert H]
    (X : Operator H) : Fin (Module.finrank ℂ H) → ℝ :=
  (isHermitian_operatorSqrt_adjoint_mul_self (X := X)).eigenvalues (hn := rfl)

noncomputable def traceNorm {H : Type*}
    [CpxFiniteHilbert H]
    (X : Operator H) : ℝ :=
  (trace (operatorSqrt ((LinearMap.adjoint X) ∘ₗ X))).re

notation:100 "‖" X "‖₁" => traceNorm X


/-! ## Lemma 12: variational form of the trace norm -/

/-!
### Supporting lemmas for `trace_variational`
-/

/--
`operatorSqrt(A†A)` composed with itself equals `A†A`.
Proved via CFC: `(cfcₙ Real.sqrt Bc) * (cfcₙ Real.sqrt Bc) = cfcₙ (sqrt · * sqrt ·) Bc = Bc`.
-/
lemma operatorSqrt_comp_self_eq_adjoint_mul
    {H : Type*} [CpxFiniteHilbert H]
    (A : Operator H) :
    operatorSqrt ((LinearMap.adjoint A) ∘ₗ A) ∘ₗ operatorSqrt ((LinearMap.adjoint A) ∘ₗ A)
      = (LinearMap.adjoint A) ∘ₗ A := by
  simp only [operatorSqrt]
  set Bc : H →L[ℂ] H :=
    LinearMap.toContinuousLinearMap ((LinearMap.adjoint A) ∘ₗ A)
  -- Bc is nonneg.
  have hBc_nonneg : (0 : H →L[ℂ] H) ≤ Bc := by
    refine (ContinuousLinearMap.nonneg_iff_isPositive Bc).2 ?_
    exact (LinearMap.isPositive_toContinuousLinearMap_iff _).2
      (LinearMap.isPositive_adjoint_comp_self A)
  -- cfcₙ sqrt Bc * cfcₙ sqrt Bc = Bc via CFC.
  have hmul : cfcₙ Real.sqrt Bc * cfcₙ Real.sqrt Bc = Bc := by
    rw [← cfcₙ_mul ..]
    nth_rw 2 [← cfcₙ_id ℝ Bc]
    exact cfcₙ_congr (fun x hx =>
      Real.mul_self_sqrt (quasispectrum_nonneg_of_nonneg Bc hBc_nonneg x hx))
  -- Composition of toLinearMaps = toLinearMap of product.
  have hcomp : (cfcₙ Real.sqrt Bc).toLinearMap ∘ₗ (cfcₙ Real.sqrt Bc).toLinearMap
      = (cfcₙ Real.sqrt Bc * cfcₙ Real.sqrt Bc).toLinearMap := by
    ext; simp [LinearMap.comp_apply]
  -- Bc.toLinearMap = A† ∘ A by definition of toContinuousLinearMap.
  have hBc_eq : Bc.toLinearMap = (LinearMap.adjoint A) ∘ₗ A := rfl
  calc (cfcₙ Real.sqrt Bc).toLinearMap ∘ₗ (cfcₙ Real.sqrt Bc).toLinearMap
      = (cfcₙ Real.sqrt Bc * cfcₙ Real.sqrt Bc).toLinearMap := hcomp
    _ = Bc.toLinearMap := by rw [hmul]
    _ = (LinearMap.adjoint A) ∘ₗ A := hBc_eq

/--
In the eigenbasis `bᵢ` of `operatorSqrt(A†A)` with eigenvalue `σᵢ = singularValues A i`,
the norm satisfies `‖A bᵢ‖ = σᵢ`.
This follows from `‖A bᵢ‖² = ⟨bᵢ, A†A bᵢ⟩ = σᵢ²`.
-/
lemma norm_apply_eigvec_eq_singularValue
    {H : Type*} [CpxFiniteHilbert H]
    (A : Operator H)
    (i : Fin (Module.finrank ℂ H)) :
    let hT := isHermitian_operatorSqrt_adjoint_mul_self (X := A)
    let b := hT.eigenvectorBasis rfl
    ‖A (b i)‖ = singularValues A i := by
  intro hT b
  -- σᵢ = hT.eigenvalues rfl i (by definition of singularValues)
  have hσ_eq : singularValues A i = hT.eigenvalues rfl i := rfl
  -- bᵢ is an eigenvector of operatorSqrt(A†A) with eigenvalue σᵢ.
  have hbasis : operatorSqrt ((LinearMap.adjoint A) ∘ₗ A) (b i)
      = (hT.eigenvalues rfl i : ℂ) • b i :=
    hT.apply_eigenvectorBasis rfl i
  -- A†A (b i) = σᵢ² · b i, since A†A = sqrt(A†A) ∘ sqrt(A†A).
  have hATA : (LinearMap.adjoint A ∘ₗ A) (b i)
      = (hT.eigenvalues rfl i : ℂ) ^ 2 • b i := by
    conv_lhs => rw [← operatorSqrt_comp_self_eq_adjoint_mul A]
    simp only [LinearMap.comp_apply, hbasis, map_smul, smul_smul]
    congr 1; ring
  -- ‖A bᵢ‖² = σᵢ² via the complex inner product.
  have hnorm_sq : ‖A (b i)‖ ^ 2 = (hT.eigenvalues rfl i) ^ 2 := by
    -- Key: ⟨Abi, Abi⟩ = ⟨A†Abi, bi⟩ = ⟨(A†A)bi, bi⟩ = ⟨σᵢ² bi, bi⟩ = σᵢ²
    have heq : ⟪A (b i), A (b i)⟫_ℂ = (hT.eigenvalues rfl i : ℂ) ^ 2 := by
      rw [← LinearMap.adjoint_inner_left A (b i) (A (b i))]
      rw [← LinearMap.comp_apply (LinearMap.adjoint A) A, hATA, inner_smul_left]
      simp [b.orthonormal.1 i, inner_self_eq_norm_sq_to_K]
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), heq]
    simp [← Complex.ofReal_pow]
  -- σᵢ ≥ 0: operatorSqrt(A†A) is PSD, so its eigenvalues are nonneg.
  have hσ_nonneg : 0 ≤ hT.eigenvalues rfl i := by
    -- operatorSqrt(A†A) is IsPositive (since cfcₙ sqrt ≥ 0 for nonneg input).
    have hSqrtPos : (operatorSqrt ((LinearMap.adjoint A) ∘ₗ A)).IsPositive := by
      simp only [operatorSqrt]
      apply ContinuousLinearMap.IsPositive.toLinearMap
      exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp
        (cfcₙ_nonneg (fun x _ => Real.sqrt_nonneg x))
    -- Re ⟨bi, sqrt(A†A)(bi)⟩ ≥ 0 (by IsPositive.re_inner_nonneg_right).
    have hre_nonneg := hSqrtPos.re_inner_nonneg_right (b i)
    -- Rewrite using hbasis: sqrt(A†A)(bi) = σᵢ • bi.
    rw [hbasis, inner_smul_right] at hre_nonneg
    simp only [b.orthonormal.1 i, inner_self_eq_norm_sq_to_K, one_pow,
               map_one, mul_one] at hre_nonneg
    exact hre_nonneg
  have hnorm_nonneg : 0 ≤ ‖A (b i)‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖A (b i)‖ - hT.eigenvalues rfl i),
             sq_nonneg (‖A (b i)‖ + hT.eigenvalues rfl i)]

/-- The trace norm is the sum of singular values. -/
theorem traceNorm_eq_sum_singularValues {H : Type*}
    [CpxFiniteHilbert H]
    (X : Operator H) :
    ‖X‖₁ = ∑ i, singularValues X i := by
  simpa [traceNorm, singularValues] using
    (isHermitian_operatorSqrt_adjoint_mul_self (X := X)).re_trace_eq_sum_eigenvalues
      (hn := rfl)

end SpectralSetup

section VariationalCharacterization

/--
For any unitary `u`, `‖trace(u ∘ A)‖ ≤ ‖A‖₁`.

Upper bound half of `trace_variational`: in the eigenbasis `b` of `√(A†A)`,
each diagonal entry satisfies `|⟨bᵢ, u(A bᵢ)⟩| ≤ ‖A bᵢ‖ = σᵢ`, so total ≤ `‖A‖₁`.
-/
lemma norm_trace_unitary_le_traceNorm
    {H : Type*} [CpxFiniteHilbert H]
    (A : Operator H)
    (u : unitary (H →L[ℂ] H)) :
    ‖trace (((u : H →L[ℂ] H) : Operator H) ∘ₗ A)‖ ≤ traceNorm A := by
  let hT := isHermitian_operatorSqrt_adjoint_mul_self (X := A)
  let b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H := hT.eigenvectorBasis rfl
  -- Express trace in the ONB b.
  have htrace : trace (((u : H →L[ℂ] H) : Operator H) ∘ₗ A)
      = ∑ i, ⟪b i, (((u : H →L[ℂ] H) : Operator H) ∘ₗ A) (b i)⟫_ℂ := by
    simp [trace, LinearMap.trace_eq_sum_inner _ b]
  rw [htrace]
  calc ‖∑ i, ⟪b i, (((u : H →L[ℂ] H) : Operator H) ∘ₗ A) (b i)⟫_ℂ‖
      ≤ ∑ i, ‖⟪b i, (((u : H →L[ℂ] H) : Operator H) ∘ₗ A) (b i)⟫_ℂ‖ :=
          norm_sum_le _ _
    _ ≤ ∑ i, ‖(((u : H →L[ℂ] H) : Operator H) ∘ₗ A) (b i)‖ := by
          gcongr with i
          have hb_norm : ‖b i‖ = 1 := b.orthonormal.1 i
          calc ‖⟪b i, _⟫_ℂ‖ ≤ ‖b i‖ * ‖(((u : H →L[ℂ] H) : Operator H) ∘ₗ A) (b i)‖ :=
                  norm_inner_le_norm _ _
            _ = ‖(((u : H →L[ℂ] H) : Operator H) ∘ₗ A) (b i)‖ := by
                    rw [hb_norm, one_mul]
    -- u is an isometry: ‖u v‖ = ‖v‖.
    _ = ∑ i, ‖A (b i)‖ := by
          congr 1; ext i
          simp only [LinearMap.comp_apply]
          exact Unitary.norm_map u (A (b i))
    -- ‖A bᵢ‖ = σᵢ by the eigenbasis lemma.
    _ = ∑ i, singularValues A i := by
          congr 1; ext i
          exact norm_apply_eigvec_eq_singularValue A i
    -- Sum of singular values = trace norm.
    _ = traceNorm A := (traceNorm_eq_sum_singularValues A).symm

/--
Attainability side of the variational formula:
there exists a unitary `u` such that `‖A‖₁ = ‖trace (u ∘ A)‖`.
-/
private lemma exists_unitary_traceNorm_eq_norm_trace
    {H : Type*} [CpxFiniteHilbert H]
    (A : Operator H) :
    ∃ u : unitary (H →L[ℂ] H),
      traceNorm A = ‖trace (((u : H →L[ℂ] H) : Operator H) ∘ₗ A)‖ := by
  set n := Module.finrank ℂ H
  have hT := isHermitian_operatorSqrt_adjoint_mul_self (X := A)
  let b := hT.eigenvectorBasis rfl
  have hσ_nonneg : ∀ i : Fin n, 0 ≤ singularValues A i := fun i =>
    (norm_apply_eigvec_eq_singularValue A i) ▸ norm_nonneg _
  have hATA_bi : ∀ i : Fin n,
      (LinearMap.adjoint A ∘ₗ A) (b i) = (singularValues A i : ℂ) ^ 2 • b i := by
    intro i
    have hbi : operatorSqrt ((LinearMap.adjoint A) ∘ₗ A) (b i) =
        (singularValues A i : ℂ) • b i := hT.apply_eigenvectorBasis rfl i
    conv_lhs => rw [← operatorSqrt_comp_self_eq_adjoint_mul A]
    simp only [LinearMap.comp_apply, hbi, map_smul, smul_smul]
    congr 1; ring
  have hinner : ∀ i j : Fin n,
      ⟪A (b i), A (b j)⟫_ℂ = (singularValues A i : ℂ) ^ 2 * ⟪b i, b j⟫_ℂ := by
    intro i j
    rw [← LinearMap.adjoint_inner_left A (b j) (A (b i)),
        ← LinearMap.comp_apply (LinearMap.adjoint A) A, hATA_bi i, inner_smul_left]
    simp only [map_pow, Complex.conj_ofReal]
  have hA_zero : ∀ i : Fin n, singularValues A i = 0 → A (b i) = 0 := fun i hi =>
    norm_eq_zero.mp ((norm_apply_eigvec_eq_singularValue A i).trans hi)
  let v : Fin n → H := fun i =>
    if singularValues A i ≠ 0 then (singularValues A i : ℂ)⁻¹ • A (b i) else 0
  let s : Set (Fin n) := {i | singularValues A i ≠ 0}
  have hv_def : ∀ i : Fin n, singularValues A i ≠ 0 →
      v i = (singularValues A i : ℂ)⁻¹ • A (b i) := fun i hi => if_pos hi
  have hv_orth : Orthonormal ℂ (s.restrict v) := by
    constructor
    · rintro ⟨i, hi⟩
      have hi' : singularValues A i ≠ 0 := hi
      rw [Set.restrict_apply, hv_def i hi', norm_smul, norm_inv]
      have hσ_norm : ‖(singularValues A i : ℂ)‖ = singularValues A i := by
        simp [Complex.norm_real, abs_of_nonneg (hσ_nonneg i)]
      have hAbi : ‖A (b i)‖ = singularValues A i := norm_apply_eigvec_eq_singularValue A i
      rw [hσ_norm, hAbi]
      exact inv_mul_cancel₀ hi'
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      have hi' : singularValues A i ≠ 0 := hi
      have hj' : singularValues A j ≠ 0 := hj
      rw [Set.restrict_apply, Set.restrict_apply, hv_def i hi', hv_def j hj',
          inner_smul_left, inner_smul_right, hinner i j]
      have hij' : i ≠ j := fun h => hij (Subtype.ext h)
      rw [b.orthonormal.2 hij']
      simp
  obtain ⟨c, hc_ext⟩ := hv_orth.exists_orthonormalBasis_extension_of_card_eq
      (card_ι := (Fintype.card_fin n).symm)
  let e : H ≃ₗᵢ[ℂ] H := c.equiv b (Equiv.refl (Fin n))
  let u : unitary (H →L[ℂ] H) := Unitary.linearIsometryEquiv.symm e
  have hu_eq : ((u : H →L[ℂ] H) : Operator H) = e.toLinearMap := rfl
  have hA_smul_c : ∀ i : Fin n, i ∈ s → A (b i) = (singularValues A i : ℂ) • c i := by
    intro i hi
    have hi' : singularValues A i ≠ 0 := hi
    have hci : c i = (singularValues A i : ℂ)⁻¹ • A (b i) :=
      (hc_ext i hi).trans (hv_def i hi')
    rw [hci, smul_inv_smul₀ (show (singularValues A i : ℂ) ≠ 0 from by exact_mod_cast hi')]
  have he_ci : ∀ i, e (c i) = b i := fun i => by
    change c.equiv b (Equiv.refl (Fin n)) (c i) = b i
    rw [OrthonormalBasis.equiv_apply_basis]
    rfl
  have htrace : trace (((u : H →L[ℂ] H) : Operator H) ∘ₗ A) = (traceNorm A : ℂ) := by
    have hsum : trace (((u : H →L[ℂ] H) : Operator H) ∘ₗ A)
        = ∑ i, ⟪b i, (((u : H →L[ℂ] H) : Operator H) ∘ₗ A) (b i)⟫_ℂ := by
      simp [trace, LinearMap.trace_eq_sum_inner _ b]
    rw [hsum]
    have hterm : ∀ i : Fin n,
        ⟪b i, (((u : H →L[ℂ] H) : Operator H) ∘ₗ A) (b i)⟫_ℂ = (singularValues A i : ℂ) := by
      intro i
      simp only [LinearMap.comp_apply]
      by_cases hi : singularValues A i ≠ 0
      · rw [hA_smul_c i hi, map_smul]
        have heci : ((u : H →L[ℂ] H) : Operator H) (c i) = b i := by
          rw [hu_eq]; exact he_ci i
        rw [heci, inner_smul_right, b.inner_eq_one i, mul_one]
      · push_neg at hi
        rw [hA_zero i hi, map_zero, inner_zero_right]
        simp [hi]
    simp_rw [hterm]
    exact_mod_cast (traceNorm_eq_sum_singularValues A).symm
  have hnn : 0 ≤ traceNorm A := by
    rw [traceNorm_eq_sum_singularValues]
    exact Finset.sum_nonneg fun i _ => hσ_nonneg i
  refine ⟨u, ?_⟩
  rw [htrace]
  simp [Complex.norm_real, abs_of_nonneg hnn]

/--
**Blueprint lemma 12** (`lem:trace-variational`).

For any operator `A` on a finite-dimensional Hilbert space,
```
‖A‖₁ = sup_{U unitary} |Tr(UA)|.
```
-/
theorem trace_variational
    {H : Type*} [CpxFiniteHilbert H]
    (A : Operator H) :
    ‖A‖₁ = sSup {r : ℝ | ∃ u : unitary (H →L[ℂ] H),
        r = ‖trace (((u : H →L[ℂ] H) : Operator H) ∘ₗ A)‖} := by
  set S : Set ℝ := {r : ℝ | ∃ u : unitary (H →L[ℂ] H),
      r = ‖trace (((u : H →L[ℂ] H) : Operator H) ∘ₗ A)‖}
  have hbounded : BddAbove S := by
    refine ⟨traceNorm A, ?_⟩
    intro r hr
    rcases hr with ⟨u, rfl⟩
    exact norm_trace_unitary_le_traceNorm A u
  have hnonempty : S.Nonempty := by
    exact ⟨_, 1, rfl⟩
  have hlower : traceNorm A ≤ sSup S := by
    apply le_csSup hbounded
    rcases exists_unitary_traceNorm_eq_norm_trace A with ⟨u, hu⟩
    exact ⟨u, hu⟩
  have hupper : sSup S ≤ traceNorm A := by
    apply csSup_le hnonempty
    intro r hr
    rcases hr with ⟨u, rfl⟩
    exact norm_trace_unitary_le_traceNorm A u
  exact le_antisymm hlower hupper

end VariationalCharacterization




section TraceNormStructures

/-- Triangle inequality for the trace norm. -/
theorem traceNorm_add_le
    {H : Type*} [CpxFiniteHilbert H] (A B : Operator H) :
    traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  rw [trace_variational (A + B)]
  apply csSup_le
  · exact ⟨_, 1, rfl⟩
  · rintro r ⟨u, rfl⟩
    let U : Operator H := ((u : H →L[ℂ] H) : Operator H)
    have htrace_add : trace (U ∘ₗ A + U ∘ₗ B) = trace (U ∘ₗ A) + trace (U ∘ₗ B) := by
      simp [trace]
    calc
      ‖trace (U ∘ₗ (A + B))‖
          = ‖trace (U ∘ₗ A + U ∘ₗ B)‖ := by
              simp [U, LinearMap.comp_add]
      _ = ‖trace (U ∘ₗ A) + trace (U ∘ₗ B)‖ := by
            rw [htrace_add]
      _ ≤ ‖trace (U ∘ₗ A)‖ + ‖trace (U ∘ₗ B)‖ := norm_add_le _ _
      _ ≤ traceNorm A + traceNorm B := by
            exact add_le_add
              (norm_trace_unitary_le_traceNorm A u)
              (norm_trace_unitary_le_traceNorm B u)


/-- Conjugation map by a linear isometry equivalence is continuous on endomorphisms. -/
private lemma continuous_conjStarAlgEquiv_nonunital {H K : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    [CompleteSpace H] [CompleteSpace K]
    (e : H ≃ₗᵢ[ℂ] K) :
    Continuous
      (((e.conjStarAlgEquiv : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)).toNonUnitalStarAlgHom)
        : (H →L[ℂ] H) → (K →L[ℂ] K)) := by
  change Continuous (fun A : H →L[ℂ] H => (e : H →L[ℂ] K).comp (A.comp (e.symm : K →L[ℂ] H)))
  have hleft : Continuous (fun A : H →L[ℂ] H => (e : H →L[ℂ] K).comp A) := by
    simpa using
      (Continuous.const_clm_comp
        (hf := (continuous_id : Continuous (fun A : H →L[ℂ] H => A)))
        (g := (e : H →L[ℂ] K)))
  simpa [ContinuousLinearMap.comp_assoc] using
    (Continuous.clm_comp_const (hg := hleft) (f := (e.symm : K →L[ℂ] H)))

/-- `cfcₙ sqrt` commutes with conjugation on Gram operators `X⋆X`. -/
private lemma map_cfc_nsqrt_conj_star_mul_self {H K : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K]
    [CompleteSpace H] [CompleteSpace K]
    (e : H ≃ₗᵢ[ℂ] K)
    (X : H →L[ℂ] H) :
    e.conjStarAlgEquiv (cfcₙ Real.sqrt (star X * X))
      = cfcₙ Real.sqrt (e.conjStarAlgEquiv (star X) * e.conjStarAlgEquiv X) := by
  have hmap :
      ((e.conjStarAlgEquiv : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)).toNonUnitalStarAlgHom)
        (cfcₙ Real.sqrt (star X * X))
        = cfcₙ Real.sqrt
            (((e.conjStarAlgEquiv : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)).toNonUnitalStarAlgHom)
              (star X * X)) := by
    exact NonUnitalStarAlgHom.map_cfcₙ
      (φ := ((e.conjStarAlgEquiv : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)).toNonUnitalStarAlgHom))
      (f := Real.sqrt)
      (a := star X * X)
      (hφ := continuous_conjStarAlgEquiv_nonunital (e := e))
      (ha := IsSelfAdjoint.star_mul_self X)
      (hφa := by
        have hEq :
            ((e.conjStarAlgEquiv : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)) (star X * X))
              = star (e.conjStarAlgEquiv X) * e.conjStarAlgEquiv X := by
          simp [map_mul, map_star]
        simpa [StarAlgHom.coe_toNonUnitalStarAlgHom, hEq] using
          (IsSelfAdjoint.star_mul_self (e.conjStarAlgEquiv X)))
  calc
    e.conjStarAlgEquiv (cfcₙ Real.sqrt (star X * X))
        = cfcₙ Real.sqrt
            (((e.conjStarAlgEquiv : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)).toNonUnitalStarAlgHom)
              (star X * X)) := by
                simpa [StarAlgHom.coe_toNonUnitalStarAlgHom] using hmap
    _ = cfcₙ Real.sqrt (e.conjStarAlgEquiv (star X) * e.conjStarAlgEquiv X) := by
          simp [StarAlgHom.coe_toNonUnitalStarAlgHom, map_mul]

/-- Continuous-linear rewrite of `(X†X)` as `X⋆X`. -/
private lemma toContinuousLinearMap_adjoint_mul {H : Type*}
    [CpxFiniteHilbert H]
    (X : Operator H) :
    LinearMap.toContinuousLinearMap ((LinearMap.adjoint X) ∘ₗ X)
      = star (LinearMap.toContinuousLinearMap X) * (LinearMap.toContinuousLinearMap X) := by
  have hadj :
      star (LinearMap.toContinuousLinearMap X)
        = LinearMap.toContinuousLinearMap (LinearMap.adjoint X) := by
    simpa [ContinuousLinearMap.star_eq_adjoint] using
      (LinearMap.adjoint_toContinuousLinearMap (A := X)).symm
  calc
    LinearMap.toContinuousLinearMap ((LinearMap.adjoint X) ∘ₗ X)
        = LinearMap.toContinuousLinearMap (LinearMap.adjoint X)
          * LinearMap.toContinuousLinearMap X := by
            rfl
    _ = star (LinearMap.toContinuousLinearMap X) * (LinearMap.toContinuousLinearMap X) := by
          simp [hadj]

/-- `operatorSqrt (X†X)` in continuous-functional-calculus form. -/
private lemma operatorSqrt_adjoint_mul_eq_cfc {H : Type*}
    [CpxFiniteHilbert H]
    (X : Operator H) :
    operatorSqrt ((LinearMap.adjoint X) ∘ₗ X)
      = (cfcₙ Real.sqrt (star (LinearMap.toContinuousLinearMap X)
          * (LinearMap.toContinuousLinearMap X))).toLinearMap := by
  simp [operatorSqrt, toContinuousLinearMap_adjoint_mul]

/-- Conjugation by a linear isometry equivalence preserves trace norm. -/
theorem traceNorm_conj_linearIsometryEquiv {H K : Type*}
    [CpxFiniteHilbert H] [CpxFiniteHilbert K]
    (e : H ≃ₗᵢ[ℂ] K)
    (X : Operator H) :
    traceNorm (e.toLinearMap ∘ₗ X ∘ₗ e.symm.toLinearMap) = traceNorm X := by
  let Xc : H →L[ℂ] H := LinearMap.toContinuousLinearMap X
  let Yc : K →L[ℂ] K := e.conjStarAlgEquiv Xc
  let Y : Operator K := Yc.toLinearMap
  have hY : Y = e.toLinearMap ∘ₗ X ∘ₗ e.symm.toLinearMap := by rfl
  have hYc_to : LinearMap.toContinuousLinearMap Y = Yc := by
    exact (LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap (f := Y) (g := Yc)).2 rfl
  have hMapSqrt :
      cfcₙ Real.sqrt (star Yc * Yc)
        = e.conjStarAlgEquiv (cfcₙ Real.sqrt (star Xc * Xc)) := by
    have h0 := map_cfc_nsqrt_conj_star_mul_self (e := e) (X := Xc)
    have hstar : e.conjStarAlgEquiv (star Xc) = star (e.conjStarAlgEquiv Xc) := by
      simpa using map_star (e.conjStarAlgEquiv : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)) Xc
    calc
      cfcₙ Real.sqrt (star Yc * Yc)
          = cfcₙ Real.sqrt (e.conjStarAlgEquiv (star Xc) * e.conjStarAlgEquiv Xc) := by
              simp [Yc, hstar]
      _ = e.conjStarAlgEquiv (cfcₙ Real.sqrt (star Xc * Xc)) := by
            simpa using h0.symm
  have hSqrt :
      operatorSqrt ((LinearMap.adjoint Y) ∘ₗ Y)
        = e.toLinearMap ∘ₗ operatorSqrt ((LinearMap.adjoint X) ∘ₗ X) ∘ₗ e.symm.toLinearMap := by
    calc
      operatorSqrt ((LinearMap.adjoint Y) ∘ₗ Y)
          = (cfcₙ Real.sqrt (star Yc * Yc)).toLinearMap := by
              rw [operatorSqrt_adjoint_mul_eq_cfc (X := Y)]
              simp [hYc_to]
      _ = (e.conjStarAlgEquiv (cfcₙ Real.sqrt (star Xc * Xc))).toLinearMap := by
            simpa using congrArg ContinuousLinearMap.toLinearMap hMapSqrt
      _ = e.toLinearMap ∘ₗ (cfcₙ Real.sqrt (star Xc * Xc)).toLinearMap ∘ₗ e.symm.toLinearMap := by
            rfl
      _ = e.toLinearMap ∘ₗ operatorSqrt ((LinearMap.adjoint X) ∘ₗ X) ∘ₗ e.symm.toLinearMap := by
            rw [operatorSqrt_adjoint_mul_eq_cfc (X := X)]
  have htrace :
      trace (operatorSqrt ((LinearMap.adjoint Y) ∘ₗ Y))
        = trace (operatorSqrt ((LinearMap.adjoint X) ∘ₗ X)) := by
    calc
      trace (operatorSqrt ((LinearMap.adjoint Y) ∘ₗ Y))
          = trace
              (e.toLinearMap ∘ₗ
                operatorSqrt ((LinearMap.adjoint X) ∘ₗ X) ∘ₗ
                e.symm.toLinearMap) := by
              simp [hSqrt]
      _ = trace (operatorSqrt ((LinearMap.adjoint X) ∘ₗ X)) := by
            simpa [LinearEquiv.conj_apply, Module.End.mul_eq_comp] using
              (LinearMap.trace_conj' (f := operatorSqrt ((LinearMap.adjoint X) ∘ₗ X))
                (e := e.toLinearEquiv))
  have htraceRe := congrArg Complex.re htrace
  simpa [traceNorm, hY] using htraceRe

/-- Unitary conjugation preserves trace norm. -/
theorem traceNorm_conj_unitary {H : Type*}
    [CpxFiniteHilbert H]
    (u : unitary (H →L[ℂ] H))
    (X : Operator H) :
    traceNorm
      (((u : H →L[ℂ] H) : Operator H) ∘ₗ X
        ∘ₗ (((star u : H →L[ℂ] H) : Operator H)))
      = traceNorm X := by
  let e : H ≃ₗᵢ[ℂ] H := Unitary.linearIsometryEquiv u
  have hu : ((u : H →L[ℂ] H) : Operator H) = e.toLinearMap := by
    rfl
  have hstaru : (((star u : H →L[ℂ] H) : Operator H)) = e.symm.toLinearMap := by
    simpa [e] using
      (LinearIsometryEquiv.adjoint_toLinearMap_eq_symm (e := e)).symm
  calc
    traceNorm
        (((u : H →L[ℂ] H) : Operator H) ∘ₗ X
          ∘ₗ (((star u : H →L[ℂ] H) : Operator H)))
        = traceNorm (e.toLinearMap ∘ₗ X ∘ₗ e.symm.toLinearMap) := by
            simp [hu, hstaru]
    _ = traceNorm X := traceNorm_conj_linearIsometryEquiv (e := e) (X := X)




/-- Normalization of `traceNorm` at `0`. -/
@[simp] lemma traceNorm_zero {H : Type*}
    [CpxFiniteHilbert H] :
    ‖(0 : Operator H)‖₁ = 0 := by
  simp [traceNorm, operatorSqrt, trace]

/-- `traceNorm` is invariant under negation. -/
@[simp] lemma traceNorm_neg {H : Type*}
    [CpxFiniteHilbert H]
    (X : Operator H) :
    ‖(-X)‖₁ = ‖X‖₁ := by
  simp [traceNorm, operatorSqrt]

lemma traceNorm_triangle_ineq {H : Type*}
    [CpxFiniteHilbert H]
    (h_add : ∀ X Y : Operator H, ‖X + Y‖₁ ≤ ‖X‖₁ + ‖Y‖₁)
    (X Y : Operator H) :
    ‖X + Y‖₁ ≤ ‖X‖₁ + ‖Y‖₁ :=
  h_add X Y

/-- `traceNorm` viewed as a bundled seminorm, once the two seminorm axioms are provided. -/
noncomputable def traceNormSeminorm {H : Type*}
    [CpxFiniteHilbert H]
    (h_add : ∀ X Y : Operator H, ‖X + Y‖₁ ≤ ‖X‖₁ + ‖Y‖₁)
    (h_smul : ∀ (a : ℂ) (X : Operator H), ‖a • X‖₁ = ‖a‖ * ‖X‖₁) :
    Seminorm ℂ (Operator H) :=
  Seminorm.of traceNorm h_add h_smul

@[simp] lemma traceNormSeminorm_apply {H : Type*}
    [CpxFiniteHilbert H]
    (h_add : ∀ X Y : Operator H, ‖X + Y‖₁ ≤ ‖X‖₁ + ‖Y‖₁)
    (h_smul : ∀ (a : ℂ) (X : Operator H), ‖a • X‖₁ = ‖a‖ * ‖X‖₁)
    (X : Operator H) :
    traceNormSeminorm (H := H) h_add h_smul X = ‖X‖₁ := rfl

/-- If `traceNorm` satisfies triangle inequality and scalar homogeneity, it is a `Seminorm`. -/
theorem traceNorm_isSeminorm {H : Type*}
    [CpxFiniteHilbert H]
    (h_add : ∀ X Y : Operator H, ‖X + Y‖₁ ≤ ‖X‖₁ + ‖Y‖₁)
    (h_smul : ∀ (a : ℂ) (X : Operator H), ‖a • X‖₁ = ‖a‖ * ‖X‖₁) :
    ∃ p : Seminorm ℂ (Operator H), ∀ X : Operator H, p X = ‖X‖₁ := by
  refine ⟨traceNormSeminorm (H := H) h_add h_smul, ?_⟩
  intro X
  rfl

/-- `traceNorm` viewed as a bundled additive-group norm, once triangle inequality and
definiteness are provided. -/
noncomputable def traceNormAddGroupNorm {H : Type*}
    [CpxFiniteHilbert H]
    (h_add : ∀ X Y : Operator H, ‖X + Y‖₁ ≤ ‖X‖₁ + ‖Y‖₁)
    (h_eq_zero : ∀ X : Operator H, ‖X‖₁ = 0 → X = 0) :
    AddGroupNorm (Operator H) where
  toFun := traceNorm
  map_zero' := traceNorm_zero (H := H)
  add_le' := h_add
  neg' := traceNorm_neg
  eq_zero_of_map_eq_zero' := h_eq_zero

@[simp] lemma traceNormAddGroupNorm_apply {H : Type*}
    [CpxFiniteHilbert H]
    (h_add : ∀ X Y : Operator H, ‖X + Y‖₁ ≤ ‖X‖₁ + ‖Y‖₁)
    (h_eq_zero : ∀ X : Operator H, ‖X‖₁ = 0 → X = 0)
    (X : Operator H) :
    traceNormAddGroupNorm (H := H) h_add h_eq_zero X = ‖X‖₁ := rfl

/-- If `traceNorm` satisfies triangle inequality and definiteness, it is an `AddGroupNorm`. -/
theorem traceNorm_isAddGroupNorm {H : Type*}
    [CpxFiniteHilbert H]
    (h_add : ∀ X Y : Operator H, ‖X + Y‖₁ ≤ ‖X‖₁ + ‖Y‖₁)
    (h_eq_zero : ∀ X : Operator H, ‖X‖₁ = 0 → X = 0) :
    ∃ p : AddGroupNorm (Operator H), ∀ X : Operator H, p X = ‖X‖₁ := by
  refine ⟨traceNormAddGroupNorm (H := H) h_add h_eq_zero, ?_⟩
  intro X
  rfl

/-- The `NormedAddCommGroup` structure induced by `traceNorm`, once the norm axioms are proved. -/
noncomputable def traceNormNormedAddCommGroup {H : Type*}
    [CpxFiniteHilbert H]
    (h_add : ∀ X Y : Operator H, ‖X + Y‖₁ ≤ ‖X‖₁ + ‖Y‖₁)
    (h_eq_zero : ∀ X : Operator H, ‖X‖₁ = 0 → X = 0) :
    NormedAddCommGroup (Operator H) :=
  AddGroupNorm.toNormedAddCommGroup (traceNormAddGroupNorm (H := H) h_add h_eq_zero)

end TraceNormStructures

end traceNorm
