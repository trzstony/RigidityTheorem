import Quantum.Density

open scoped TensorProduct InnerProductSpace

namespace Quantum

universe u v

/-- A finite-outcome POVM: positive effects that sum to identity. -/
structure POVM (I : Type u) (H : Type v)
    [Fintype I]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  effect : I → Operator H
  effect_pos : ∀ i : I, (effect i).IsPositive
  sum_effect : (∑ i : I, effect i) = (LinearMap.id : Operator H)

namespace POVM

variable {I : Type u}
variable {H : Type v}
variable [Fintype I]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

@[simp] lemma effect_isPositive (M : POVM I H) (i : I) : (M.effect i).IsPositive :=
  M.effect_pos i

@[simp] lemma effect_isPSD (M : POVM I H) (i : I) : IsPSD (M.effect i) := by
  intro ψ
  simpa [inner_re_symm] using (M.effect_pos i).re_inner_nonneg_right ψ

@[simp] lemma sum_effect_eq_id (M : POVM I H) :
    (∑ i : I, M.effect i) = (LinearMap.id : Operator H) :=
  M.sum_effect

/-- Born-rule probability for one POVM outcome on a density operator. -/
noncomputable def outcomeProb
    [FiniteDimensional ℂ H]
    (M : POVM I H) (ρ : DensityOperator H) (i : I) : ℝ :=
  Complex.re (trace (M.effect i ∘ₗ (ρ : Operator H)))

/-- The full outcome-probability function of a POVM on a density operator. -/
noncomputable def outcomeProbFun
    [FiniteDimensional ℂ H]
    (M : POVM I H) (ρ : DensityOperator H) : I → ℝ :=
  fun i => outcomeProb M ρ i

end POVM

/-- Two-outcome POVM as a specialization of `POVM` to `Fin 2`. -/
abbrev BinaryPOVM (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  POVM (Fin 2) H

namespace BinaryPOVM

variable {H : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- First effect of a binary POVM. -/
abbrev M0 (M : BinaryPOVM H) : Operator H := M.effect 0

/-- Second effect of a binary POVM. -/
abbrev M1 (M : BinaryPOVM H) : Operator H := M.effect 1

/-- Build a binary POVM from a single effect `Λ` (with complement `I - Λ`). -/
def ofEffect (Λ : Operator H) (hΛ : IsEffect Λ) : BinaryPOVM H where
  effect := fun i => if i = 0 then Λ else (LinearMap.id : Operator H) - Λ
  effect_pos := by
    intro i
    by_cases hi : i = 0
    · simpa [hi] using hΛ.1
    · simpa [hi] using hΛ.2
  sum_effect := by
    simp [Fin.sum_univ_two]

@[simp] lemma ofEffect_M0 (Λ : Operator H) (hΛ : IsEffect Λ) :
    M0 (ofEffect Λ hΛ) = Λ := by
  simp [M0, ofEffect]

@[simp] lemma ofEffect_M1 (Λ : Operator H) (hΛ : IsEffect Λ) :
    M1 (ofEffect Λ hΛ) = (LinearMap.id : Operator H) - Λ := by
  simp [M1, ofEffect]

end BinaryPOVM

end Quantum
