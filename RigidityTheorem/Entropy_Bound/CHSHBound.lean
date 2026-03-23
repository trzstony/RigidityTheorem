import Entropy_Bound.Setup

open scoped TensorProduct InnerProductSpace
open Quantum

namespace Entropy_Bound

/-- Bell overlap on `AB` against `|Φ⁺⟩⟨Φ⁺|`. -/
noncomputable def bellOverlapAB
    (ρAB : DensityOperator ABSystem) : Real :=
  Complex.re (trace ((pureOp Φ_plus) ∘ₗ ((ρAB : DensityOperator ABSystem) : Operator ABSystem)))

/-- Bell infidelity `δ := 1 - ⟨Φ⁺|ρ_AB|Φ⁺⟩`. -/
noncomputable def bellInfidelityAB
    (ρAB : DensityOperator ABSystem) : Real :=
  1 - bellOverlapAB ρAB

private theorem re_trace_canonicalCHSH_mul_eq_bell_terms
    (ρ : Operator ABSystem) :
    Complex.re (trace (canonicalCHSH ∘ₗ ρ))
      = (2 * Real.sqrt 2) *
          (Complex.re ⟪Φ_plus, ρ Φ_plus⟫_ℂ - Complex.re ⟪Ψ_minus, ρ Ψ_minus⟫_ℂ) := by
  let b : OrthonormalBasis (Fin 4) ℂ ABSystem :=
    bellBasis.toOrthonormalBasis bellBasis_orthonormal
  have hb : ∀ i : Fin 4, b i = bellBasis i := fun i => by simp [b]
  let eig : Fin 4 → Real
    | 0 => 2 * Real.sqrt 2
    | 1 => 0
    | 2 => 0
    | 3 => -2 * Real.sqrt 2
  have hK_basis : ∀ i : Fin 4, K (b i) = ((eig i : Real) : ℂ) • b i := by
    intro i; fin_cases i
    · simpa [b, eig, bellBasis_apply, bellVec] using K_Φ_plus
    · simpa [b, eig, bellBasis_apply, bellVec] using K_Φ_minus
    · simpa [b, eig, bellBasis_apply, bellVec] using K_Ψ_plus
    · simpa [b, eig, bellBasis_apply, bellVec] using K_Ψ_minus
  have htrace_expand : trace (canonicalCHSH ∘ₗ ρ)
      = ∑ i : Fin 4, ((eig i : Real) : ℂ) * ⟪b i, ρ (b i)⟫_ℂ :=
    calc trace (canonicalCHSH ∘ₗ ρ)
        = trace (K ∘ₗ ρ) := by simp [K_as_CHSH]
      _ = trace (ρ ∘ₗ K) := by
            simpa [Module.End.mul_eq_comp] using LinearMap.trace_mul_comm ℂ K ρ
      _ = ∑ i : Fin 4, ⟪b i, (ρ ∘ₗ K) (b i)⟫_ℂ := by
            simpa [trace, b] using LinearMap.trace_eq_sum_inner (T := (ρ ∘ₗ K)) (b := b)
      _ = ∑ i : Fin 4, ((eig i : Real) : ℂ) * ⟪b i, ρ (b i)⟫_ℂ :=
            Finset.sum_congr rfl fun i _ => by
              simp only [LinearMap.coe_comp, Function.comp_apply, hK_basis i, map_smul]
              simpa [mul_comm] using
                inner_smul_right (𝕜 := ℂ) (x := b i) (r := ((eig i : Real) : ℂ)) (y := ρ (b i))
  simp only [htrace_expand, eig, hb, bellBasis_apply, bellVec, Fin.sum_univ_four,
             Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/--
From the CHSH expectation lower bound, derive the Bell-overlap infidelity bound
`δ ≤ ε/(2√2)` for `ρ_AB`.
-/
theorem bellInfidelityAB_le_of_chsh
    (ρAB : DensityOperator ABSystem) (ε : Real)
    (hCHSH :
      (2 * Real.sqrt 2 - ε)
        ≤ Complex.re
            (trace
              (canonicalCHSH ∘ₗ
                ((ρAB : DensityOperator ABSystem) : Operator ABSystem)))) :
    bellInfidelityAB ρAB ≤ ε / (2 * Real.sqrt 2) := by
  let p : Real :=
    Complex.re ⟪Φ_plus, ((ρAB : DensityOperator ABSystem) : Operator ABSystem) Φ_plus⟫_ℂ
  let q : Real :=
    Complex.re ⟪Ψ_minus, ((ρAB : DensityOperator ABSystem) : Operator ABSystem) Ψ_minus⟫_ℂ
  have hExp : Complex.re (trace (canonicalCHSH ∘ₗ (ρAB : Operator ABSystem)))
      = (2 * Real.sqrt 2) * (p - q) := by
    simpa [p, q] using re_trace_canonicalCHSH_mul_eq_bell_terms (ρAB : Operator ABSystem)
  have hq_nonneg : 0 ≤ q := by
    simpa [q] using
      (IsPSD.isPositive ρAB.isHermitian ρAB.isPSD).re_inner_nonneg_right Ψ_minus
  have hden_pos : (0 : Real) < 2 * Real.sqrt 2 := by positivity
  have hdelta : 1 - p ≤ ε / (2 * Real.sqrt 2) := by
    rw [le_div_iff₀ hden_pos]
    nlinarith [mul_nonneg (le_of_lt hden_pos) hq_nonneg]
  simpa [bellInfidelityAB, bellOverlapAB, p] using hdelta


end Entropy_Bound
