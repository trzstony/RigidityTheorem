import Quantum.TraceNorm

namespace Quantum

open scoped TensorProduct InnerProductSpace


section DistancesAndFidelity

noncomputable def traceDistance {H : Type*}
    [CpxFiniteHilbert H]
    (ρ σ : Operator H) : ℝ :=
  (1 / 2 : ℝ) * ‖((ρ : Operator H) - (σ : Operator H))‖₁

notation:100 "D(" ρ "," σ ")" => traceDistance ρ σ

@[simp] theorem traceDistance_self {H : Type*}
    [CpxFiniteHilbert H]
    (ρ : Operator H) :
    D(ρ,ρ) = 0 := by
  simp [traceDistance]

@[simp] theorem traceDistance_comm {H : Type*}
    [CpxFiniteHilbert H]
    (ρ σ : Operator H) :
    D(ρ,σ) = D(σ,ρ) := by
  have hsub : σ - ρ = -(ρ - σ) := by
    abel_nf
  have hneg : ‖ρ - σ‖₁ = ‖-(ρ - σ)‖₁ := by
    simpa using (traceNorm_neg (X := (ρ - σ))).symm
  have hnorm : ‖-(ρ - σ)‖₁ = ‖σ - ρ‖₁ := by
    exact congrArg (fun T : Operator H => ‖T‖₁) hsub.symm
  calc
    D(ρ,σ) = (1 / 2 : ℝ) * ‖ρ - σ‖₁ := rfl
    _ = (1 / 2 : ℝ) * ‖-(ρ - σ)‖₁ := by simp [hneg]
    _ = (1 / 2 : ℝ) * ‖σ - ρ‖₁ := by exact congrArg (fun t : Real => (1 / 2 : ℝ) * t) hnorm
    _ = D(σ,ρ) := rfl

/-- Unitary conjugation preserves trace distance. -/
theorem traceDistance_conj_unitary {H : Type*}
    [CpxFiniteHilbert H]
    (u : unitary (H →L[ℂ] H))
    (ρ σ : Operator H) :
    D((((u : H →L[ℂ] H) : Operator H) ∘ₗ ρ ∘ₗ (((star u : H →L[ℂ] H) : Operator H))),
      (((u : H →L[ℂ] H) : Operator H) ∘ₗ σ ∘ₗ (((star u : H →L[ℂ] H) : Operator H))))
      = D(ρ,σ) := by
  have hsub :
      (((u : H →L[ℂ] H) : Operator H) ∘ₗ ρ ∘ₗ (((star u : H →L[ℂ] H) : Operator H)))
        - (((u : H →L[ℂ] H) : Operator H) ∘ₗ σ ∘ₗ (((star u : H →L[ℂ] H) : Operator H)))
      = (((u : H →L[ℂ] H) : Operator H) ∘ₗ (ρ - σ) ∘ₗ (((star u : H →L[ℂ] H) : Operator H))) := by
    ext ψ
    simp
  calc
    D((((u : H →L[ℂ] H) : Operator H) ∘ₗ ρ ∘ₗ (((star u : H →L[ℂ] H) : Operator H))),
      (((u : H →L[ℂ] H) : Operator H) ∘ₗ σ ∘ₗ (((star u : H →L[ℂ] H) : Operator H))))
        = (1 / 2 : ℝ) *
            traceNorm
              ((((u : H →L[ℂ] H) : Operator H) ∘ₗ ρ ∘ₗ (((star u : H →L[ℂ] H) : Operator H)))
                - (((u : H →L[ℂ] H) : Operator H) ∘ₗ σ ∘ₗ (((star u : H →L[ℂ] H) : Operator H)))) := by
              rfl
    _ = (1 / 2 : ℝ) *
          traceNorm
            (((u : H →L[ℂ] H) : Operator H) ∘ₗ (ρ - σ)
              ∘ₗ (((star u : H →L[ℂ] H) : Operator H))) := by simp [hsub]
    _ = (1 / 2 : ℝ) * traceNorm (ρ - σ) := by
          simp [traceNorm_conj_unitary]
    _ = D(ρ,σ) := rfl

noncomputable def fidelity {H : Type*}
    [CpxFiniteHilbert H] [CompleteSpace H]
    (ρ σ : Operator H) : ℝ :=
  ‖operatorSqrt (ρ : Operator H) ∘ₗ operatorSqrt (σ : Operator H)‖₁

notation:100 "F(" ρ "," σ ")" => fidelity ρ σ

end DistancesAndFidelity

end Quantum
