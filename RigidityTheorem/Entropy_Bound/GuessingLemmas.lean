import Entropy_Bound.Infra
import Entropy_Bound.CHSHBound
import Entropy_Bound.PostselectionBridge
import Entropy_Bound.RigidityToPguess

open scoped TensorProduct InnerProductSpace
open Quantum

namespace Entropy_Bound

/--
Guessing functional for one fixed finite-outcome POVM on `E`, with the same
classical alphabet as the register `X`.
-/
noncomputable def guessFunctional
    {X E : Type*} [Fintype X]
    [CpxFiniteHilbert E] :
    Operator ((EuclideanSpace ℂ X) ⊗[ℂ] E) → POVM X E → Real :=
  fun ρXE M =>
    let piOp : Operator ((EuclideanSpace ℂ X) ⊗[ℂ] E) :=
      ∑ x : X, (classicalProjector (X := X) x) ⊗ₗ (M.effect x)
    Complex.re (trace (piOp ∘ₗ ρXE))

/--
Eve's optimal guessing probability for a classical-quantum state whose
classical register has finite alphabet `X`.
-/
noncomputable def pGuess
    {X E : Type*} [Fintype X]
    [CpxFiniteHilbert E]
    (ρXE : Operator ((EuclideanSpace ℂ X) ⊗[ℂ] E)) : Real :=
  sSup {r : Real | ∃ M : POVM X E, r = guessFunctional ρXE M}

/--
For a binary classical register, the uniform POVM
`M_x = (1/2) I_E` witnesses a state-independent lower bound
`pGuess ≥ 1/2` on every density operator.

This is the formal version of the usual "uniform random guess" argument:
the associated decision operator is `(1/2) I_{XE}`, so its value on a
density operator is exactly `(1/2) Tr(ρ_XE) = 1/2`.
-/
theorem pGuess_density_ge_half_fin2
    {E : Type*}
    [CpxFiniteHilbert E]
    (ρXE : DensityOperator (Qubit ⊗[ℂ] E)) :
    (1 / 2 : Real) ≤
      pGuess
        (((ρXE : DensityOperator (Qubit ⊗[ℂ] E)) : Operator (Qubit ⊗[ℂ] E))) := by
  let ρop : Operator (Qubit ⊗[ℂ] E) := ρXE
  let S : Set Real :=
    {r : Real | ∃ M : POVM (Fin 2) E,
      r = guessFunctional (X := Fin 2) (E := E) ρop M}
  let halfI : Operator E := (1 / 2 : ℂ) • (LinearMap.id : Operator E)
  have hproj_sum :
      (classicalProjector (X := Fin 2) 0 + classicalProjector (X := Fin 2) 1)
        = (LinearMap.id : Operator Qubit) := by
    ext q i
    fin_cases i
    · simp [Qubit, classicalProjector, classicalKet, pureOp,
        EuclideanSpace.single_apply, EuclideanSpace.inner_single_left]
    · simp [Qubit, classicalProjector, classicalKet, pureOp,
        EuclideanSpace.single_apply, EuclideanSpace.inner_single_left]
  have hhalf_pos : halfI.IsPositive := by
    have hid_pos : (LinearMap.id : Operator E).IsPositive := LinearMap.isPositive_id
    have hs : (starRingEnd ℂ) ((1 / 2 : ℂ)) = (1 / 2 : ℂ) := by
      simpa using Complex.conj_ofReal (1 / 2 : ℝ)
    refine ⟨LinearMap.IsSymmetric.smul hs hid_pos.isSymmetric, fun ψ => ?_⟩
    simpa [halfI, LinearMap.smul_apply, inner_smul_left, Complex.mul_re] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (hid_pos.re_inner_nonneg_left ψ)
  have heq_half : (LinearMap.id : Operator E) - halfI = halfI := by
    ext v
    calc
      (((LinearMap.id : Operator E) - halfI) v)
          = (1 : ℂ) • v - (1 / 2 : ℂ) • v := by
              simp [halfI, LinearMap.sub_apply, LinearMap.smul_apply]
      _ = ((1 : ℂ) - (1 / 2 : ℂ)) • v := by rw [sub_smul]
      _ = (1 / 2 : ℂ) • v := by norm_num
      _ = halfI v := by simp [halfI, LinearMap.smul_apply]
  have hhalf_isEffect : IsEffect halfI := by
    exact ⟨hhalf_pos, by simpa [heq_half] using hhalf_pos⟩
  let M_half : POVM (Fin 2) E := BinaryPOVM.ofEffect halfI hhalf_isEffect
  have htensor_id :
      (((LinearMap.id : Operator Qubit) ⊗ₗ (LinearMap.id : Operator E))
        : Operator (Qubit ⊗[ℂ] E))
        = (LinearMap.id : Operator (Qubit ⊗[ℂ] E)) := by
    simp
  have hguess_half :
      guessFunctional (X := Fin 2) (E := E) ρop M_half = (1 / 2 : Real) := by
    let piOp : Operator (Qubit ⊗[ℂ] E) :=
      ∑ x : Fin 2, (classicalProjector (X := Fin 2) x) ⊗ₗ (M_half.effect x)
    have hpi :
        piOp = ((1 / 2 : ℂ) • (LinearMap.id : Operator (Qubit ⊗[ℂ] E))) := by
      calc
        piOp
            = ((classicalProjector (X := Fin 2) 0) ⊗ₗ halfI)
                + ((classicalProjector (X := Fin 2) 1) ⊗ₗ halfI) := by
                  simp [piOp, M_half, heq_half]
        _ = (((classicalProjector (X := Fin 2) 0) + classicalProjector (X := Fin 2) 1)
              ⊗ₗ halfI) := by
                rw [← TensorProduct.map_add_left]
        _ = ((LinearMap.id : Operator Qubit) ⊗ₗ halfI) := by
              rw [hproj_sum]
        _ = (1 / 2 : ℂ) •
              (((LinearMap.id : Operator Qubit) ⊗ₗ (LinearMap.id : Operator E))
                : Operator (Qubit ⊗[ℂ] E)) := by
              simp [halfI, TensorProduct.map_smul_right]
        _ = ((1 / 2 : ℂ) • (LinearMap.id : Operator (Qubit ⊗[ℂ] E))) := by
              rw [htensor_id]
    have htr_re : Complex.re (trace ρop) = 1 := by
      simpa [ρop] using congrArg Complex.re ρXE.trace_one
    have hsmul_id_comp :
        (((1 / 2 : ℂ) • (LinearMap.id : Operator (Qubit ⊗[ℂ] E))) ∘ₗ ρop)
          = ((1 / 2 : ℂ) • ρop) := by
      ext z
      simp
    calc
      guessFunctional (X := Fin 2) (E := E) ρop M_half
          = Complex.re (trace (piOp ∘ₗ ρop)) := by
              simp [guessFunctional, piOp]
      _ = Complex.re (trace (((1 / 2 : ℂ) • (LinearMap.id : Operator (Qubit ⊗[ℂ] E))) ∘ₗ ρop)) := by
            rw [hpi]
      _ = Complex.re (trace ((1 / 2 : ℂ) • ρop)) := by
            rw [hsmul_id_comp]
      _ = Complex.re ((1 / 2 : ℂ) * trace ρop) := by
            simp [trace]
      _ = (1 / 2 : Real) := by
            simp [Complex.mul_re, htr_re]
  have hS_bdd : BddAbove S := by
    refine ⟨1, ?_⟩
    intro r hr
    rcases hr with ⟨M, rfl⟩
    let piOp : Operator (Qubit ⊗[ℂ] E) :=
      ∑ x : Fin 2, (classicalProjector (X := Fin 2) x) ⊗ₗ (M.effect x)
    have hρ_pos : ρop.IsPositive := by
      exact IsPSD.isPositive ρXE.isHermitian ρXE.isPSD
    have hpi_effect : IsEffect piOp := by
      simpa [piOp] using (decisionOp_isEffect_fin2 (E := E) M)
    have hle :
        Complex.re (trace (piOp * ρop)) ≤ Complex.re (trace ρop) := by
      exact re_trace_mul_le_re_trace_of_isPositive_of_isEffectLike
        (A := ρop) (B := piOp) hρ_pos hpi_effect.2
    have htr : Complex.re (trace ρop) = 1 := by
      simpa [ρop] using congrArg Complex.re ρXE.trace_one
    calc
      guessFunctional (X := Fin 2) (E := E) ρop M
          = Complex.re (trace (piOp * ρop)) := by
              simp [guessFunctional, piOp, ρop, Module.End.mul_eq_comp]
      _ ≤ Complex.re (trace ρop) := hle
      _ = 1 := htr
  change (1 / 2 : Real) ≤ sSup S
  exact le_csSup hS_bdd ⟨M_half, hguess_half.symm⟩

/--
As a consequence, binary-register guessing probability is always strictly positive
on density operators.
-/
theorem pGuess_density_pos_fin2
    {E : Type*}
    [CpxFiniteHilbert E]
    (ρXE : DensityOperator (Qubit ⊗[ℂ] E)) :
    (0 : Real) <
      pGuess
        (((ρXE : DensityOperator (Qubit ⊗[ℂ] E)) : Operator (Qubit ⊗[ℂ] E))) := by
  exact lt_of_lt_of_le (by norm_num : (0 : Real) < 1 / 2)
    (pGuess_density_ge_half_fin2 (E := E) ρXE)




/--
Lift a binary POVM on `E` to the corresponding decision operator acting on `ABE`
through Alice's key projection.
-/
noncomputable def liftedDecisionOpFromABE
    {E : Type} [CpxFiniteHilbert E]
    (M : POVM (Fin 2) E) : Operator (ABESystem E) :=
  ∑ x : Fin 2,
    (keyProjector (E := E) x) ∘ₗ
      ((((LinearMap.id : Operator ABSystem) ⊗ₗ (M.effect x))
        : Operator (ABESystem E)) ∘ₗ (keyProjector (E := E) x))

/--
Blueprint variational step specialized to the binary decision form:
for any binary POVM decision operator and any operator `Δ`,
the decision bias is bounded by trace distance to `0`.
-/
private theorem guessFunctional_perturbation_bound_fin2
    {E : Type*} [CpxFiniteHilbert E]
    (ρ σ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))
    (M : POVM (Fin 2) E) :
    guessFunctional (X := Fin 2) (E := E)
        ((ρ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) : Operator
          ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) M
      ≤ guessFunctional (X := Fin 2) (E := E)
          ((σ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) : Operator
            ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) M
        + D((((ρ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) : Operator
            ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))),
            (((σ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) : Operator
            ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)))) := by
  let ρop : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E) := ρ
  let σop : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E) := σ
  let Δ : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E) := ρop - σop
  let piOp : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E) :=
    ∑ x : Fin 2, (classicalProjector (X := Fin 2) x) ⊗ₗ (M.effect x)
  have hdiff :
      guessFunctional (X := Fin 2) (E := E) ρop M
        - guessFunctional (X := Fin 2) (E := E) σop M
        = Complex.re (trace (piOp ∘ₗ Δ)) := by
    have htrace :
        trace (piOp ∘ₗ Δ) = trace (piOp ∘ₗ ρop) - trace (piOp ∘ₗ σop) := by
      unfold Quantum.trace
      simp [Δ, sub_eq_add_neg, LinearMap.comp_add, LinearMap.comp_neg]
    calc
      guessFunctional (X := Fin 2) (E := E) ρop M
          - guessFunctional (X := Fin 2) (E := E) σop M
          = Complex.re (trace (piOp ∘ₗ ρop)) - Complex.re (trace (piOp ∘ₗ σop)) := by
              simp [guessFunctional, piOp, ρop, σop]
      _ = Complex.re (trace (piOp ∘ₗ ρop) - trace (piOp ∘ₗ σop)) := by
            simp [Complex.sub_re]
      _ = Complex.re (trace (piOp ∘ₗ Δ)) := by simp [htrace]
  have hvar :
      Complex.re (trace (piOp ∘ₗ Δ))
        ≤ (1 / 2 : Real) * traceNorm Δ := by
    simpa [piOp, Δ, ρop, σop] using
      (trace_variational_decisionOp_fin2 (E := E) (M := M) (ρ := ρ) (σ := σ))
  have hsub :
      guessFunctional (X := Fin 2) (E := E) ρop M
        - guessFunctional (X := Fin 2) (E := E) σop M ≤ D(ρop, σop) := by
    have hsub' :
        guessFunctional (X := Fin 2) (E := E) ρop M
          - guessFunctional (X := Fin 2) (E := E) σop M
          ≤ (1 / 2 : Real) * traceNorm Δ := by
      simpa [hdiff] using hvar
    simpa [traceDistance, Δ] using hsub'
  simpa [ρop, σop] using (sub_le_iff_le_add').mp hsub

/-- Any binary-POVM guessing value on a density operator is at most `1`. -/
private theorem guessFunctional_le_one_fin2
    {E : Type*} [CpxFiniteHilbert E]
    (ρ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))
    (M : POVM (Fin 2) E) :
    guessFunctional (X := Fin 2) (E := E)
      (((ρ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) : Operator
        ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))) M
      ≤ 1 := by
  let ρop : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E) := ρ
  let piOp : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E) :=
    ∑ x : Fin 2, (classicalProjector (X := Fin 2) x) ⊗ₗ (M.effect x)
  have hρ_pos : ρop.IsPositive := by
    exact IsPSD.isPositive ρ.isHermitian ρ.isPSD
  have hpi_effect : IsEffect piOp := by
    simpa [piOp] using (decisionOp_isEffect_fin2 (E := E) M)
  have hle :
      Complex.re (trace (piOp * ρop)) ≤ Complex.re (trace ρop) := by
    exact re_trace_mul_le_re_trace_of_isPositive_of_isEffectLike
      (A := ρop) (B := piOp) hρ_pos hpi_effect.2
  have htr :
      Complex.re (trace ρop) = 1 := by
    simpa [ρop] using congrArg Complex.re ρ.trace_one
  calc
    guessFunctional (X := Fin 2) (E := E)
        (((ρ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) : Operator
          ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))) M
        = Complex.re (trace (piOp * ρop)) := by
            simp [guessFunctional, piOp, ρop, Module.End.mul_eq_comp]
    _ ≤ Complex.re (trace ρop) := hle
    _ = 1 := htr

/-- Finite-2 version of continuity, used to discharge the `Qubit` statement by rewriting. -/
private theorem pGuess_continuity_fin2
    {E : Type*}
    [CpxFiniteHilbert E]
    (ρ σ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) :
    pGuess (X := Fin 2) (E := E)
        (((ρ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) : Operator
          ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)))
      ≤ pGuess (X := Fin 2) (E := E)
          (((σ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) : Operator
            ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)))
        + D((((ρ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) : Operator
              ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))),
            (((σ : DensityOperator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)) : Operator
              ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E)))) := by
  let ρop : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E) := ρ
  let σop : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E) := σ
  let Sρ : Set Real :=
    {r : Real | ∃ M : POVM (Fin 2) E,
      r = guessFunctional (X := Fin 2) (E := E)
        ρop M}
  let Sσ : Set Real :=
    {r : Real | ∃ M : POVM (Fin 2) E,
      r = guessFunctional (X := Fin 2) (E := E)
        σop M}
  have hEffect0 : IsEffect (0 : Operator E) := by
    constructor
    · simp
    · simp
  let Mtriv : POVM (Fin 2) E := BinaryPOVM.ofEffect (H := E) (0 : Operator E) hEffect0
  have hneρ : Sρ.Nonempty := by
    refine ⟨guessFunctional (X := Fin 2) (E := E)
      ρop Mtriv, ?_⟩
    exact ⟨Mtriv, rfl⟩
  have hbddσ : BddAbove Sσ := by
    refine ⟨1, ?_⟩
    intro r hr
    rcases hr with ⟨M, rfl⟩
    simpa [σop] using (guessFunctional_le_one_fin2 (E := E) (ρ := σ) M)
  have hmain :
      ∀ r ∈ Sρ,
        r ≤ pGuess (X := Fin 2) (E := E) σop + D(ρop, σop) := by
    intro r hr
    rcases hr with ⟨M, rfl⟩
    have hpert := guessFunctional_perturbation_bound_fin2
      (E := E) (ρ := ρ) (σ := σ) M
    have hσ_to_sup :
        guessFunctional (X := Fin 2) (E := E)
          σop M
        ≤ pGuess (X := Fin 2) (E := E) σop := by
      change guessFunctional (X := Fin 2) (E := E) σop M ≤ sSup Sσ
      exact le_csSup hbddσ ⟨M, rfl⟩
    calc
      guessFunctional (X := Fin 2) (E := E)
          ρop M
          ≤ guessFunctional (X := Fin 2) (E := E)
              σop M
            + D(ρop, σop) := by
              simpa [ρop, σop] using hpert
      _ ≤ pGuess (X := Fin 2) (E := E)
            σop
          + D(ρop, σop) := by gcongr
  change sSup Sρ ≤ sSup Sσ + D(ρop, σop)
  exact csSup_le hneρ hmain

/-- Continuity of the guessing probability under trace distance. -/
theorem pGuess_continuity
    {E : Type*}
    [CpxFiniteHilbert E]
    (ρXE σXE : DensityOperator (Qubit ⊗[ℂ] E)) :
    pGuess (((ρXE : DensityOperator (Qubit ⊗[ℂ] E)) : Operator (Qubit ⊗[ℂ] E)))
      ≤ pGuess (((σXE : DensityOperator (Qubit ⊗[ℂ] E)) : Operator (Qubit ⊗[ℂ] E)))
        + D((((ρXE : DensityOperator (Qubit ⊗[ℂ] E)) : Operator (Qubit ⊗[ℂ] E))),
            (((σXE : DensityOperator (Qubit ⊗[ℂ] E)) : Operator (Qubit ⊗[ℂ] E)))) := by
  simpa [Qubit] using
    (pGuess_continuity_fin2 (E := E) (ρ := ρXE) (σ := σXE))

/-- Uniform-bit tensor states give a constant guessing functional value `1/2`. -/
private theorem guessFunctional_const_of_uniform_bit_tensor
    {E : Type*}
    [CpxFiniteHilbert E]
    (τE : DensityOperator E) :
    ∀ M : POVM (Fin 2) E,
      guessFunctional (X := Fin 2) (E := E)
        (idealBitTensorState (E := E) ((τE : DensityOperator E) : Operator E)) M
        = (1 / 2 : Real) := by
  intro M
  let T : Operator E := (1 / 2 : ℂ) • ((τE : DensityOperator E) : Operator E)
  have hsum : M.effect 0 + M.effect 1 = (LinearMap.id : Operator E) := by
    have hs := M.sum_effect
    rw [Fin.sum_univ_two] at hs
    exact hs
  have htrace_tensor :
      ∀ x : Fin 2, ∀ A : Operator E,
        trace
          (((classicalProjector (X := Fin 2) x) ⊗ₗ A)
            : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))
          = trace A := by
    intro x A
    have htp :
        trace
            (((classicalProjector (X := Fin 2) x) ⊗ₗ A)
              : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))
          = trace (classicalProjector (X := Fin 2) x) * trace A := by
      exact (LinearMap.trace_tensorProduct' (R := ℂ)
        (M := EuclideanSpace ℂ (Fin 2)) (N := E)
        (f := classicalProjector (X := Fin 2) x) (g := A))
    have htr :
        trace (classicalProjector (X := Fin 2) x) = 1 := by
      simpa [classicalProjector, classicalKet] using
        (trace_pureOp_comp (H := EuclideanSpace ℂ (Fin 2))
          (ψ := classicalKet (X := Fin 2) x)
          (X := (LinearMap.id : Operator (EuclideanSpace ℂ (Fin 2)))))
    calc
      trace
          (((classicalProjector (X := Fin 2) x) ⊗ₗ A)
            : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))
          = trace (classicalProjector (X := Fin 2) x) * trace A := htp
      _ = trace A := by simp [htr]
  have hdecomp :
      guessFunctional (X := Fin 2) (E := E)
          (idealBitTensorState (E := E) ((τE : DensityOperator E) : Operator E)) M
        =
          Complex.re (trace (((classicalProjector (X := Fin 2) 0) ⊗ₗ (M.effect 0)) ∘ₗ
            ((classicalProjector (X := Fin 2) 0) ⊗ₗ T)))
          + Complex.re (trace (((classicalProjector (X := Fin 2) 1) ⊗ₗ (M.effect 1)) ∘ₗ
            ((classicalProjector (X := Fin 2) 0) ⊗ₗ T)))
          + (Complex.re (trace (((classicalProjector (X := Fin 2) 0) ⊗ₗ (M.effect 0)) ∘ₗ
              ((classicalProjector (X := Fin 2) 1) ⊗ₗ T)))
            + Complex.re (trace (((classicalProjector (X := Fin 2) 1) ⊗ₗ (M.effect 1)) ∘ₗ
              ((classicalProjector (X := Fin 2) 1) ⊗ₗ T)))) := by
    simp [guessFunctional, idealBitTensorState, Fin.sum_univ_two, T, trace, Complex.add_re,
      LinearMap.comp_add, LinearMap.add_comp]
  rw [hdecomp]
  let P0 : Operator (EuclideanSpace ℂ (Fin 2)) := classicalProjector (X := Fin 2) 0
  let P1 : Operator (EuclideanSpace ℂ (Fin 2)) := classicalProjector (X := Fin 2) 1
  have hmul00 : P0 * P0 = P0 := by
    ext q i
    fin_cases i <;>
      simp
        [P0, classicalProjector, classicalKet, pureOp, Module.End.mul_eq_comp]
  have hmul11 : P1 * P1 = P1 := by
    ext q i
    fin_cases i <;>
      simp
        [P1, classicalProjector, classicalKet, pureOp, Module.End.mul_eq_comp]
  have hmul10 : P1 * P0 = 0 := by
    ext q i
    fin_cases i
    · simp
        [P0, P1, classicalProjector, classicalKet, pureOp, Module.End.mul_eq_comp]
    · simp
        [P0, P1, classicalProjector, classicalKet, pureOp, Module.End.mul_eq_comp,
          LinearMap.comp_apply, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
  have hmul01 : P0 * P1 = 0 := by
    ext q i
    fin_cases i
    · simp
        [P0, P1, classicalProjector, classicalKet, pureOp, Module.End.mul_eq_comp,
          LinearMap.comp_apply, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]
    · simp
        [P0, P1, classicalProjector, classicalKet, pureOp, Module.End.mul_eq_comp]
  have hcomp00 :
      ((P0 ⊗ₗ (M.effect 0)) ∘ₗ (P0 ⊗ₗ T))
        = ((P0 * P0) ⊗ₗ ((M.effect 0) ∘ₗ T)) := by
    simpa [P0, Module.End.mul_eq_comp] using
      (TensorProduct.map_comp (f₂ := P0) (g₂ := M.effect 0) (f₁ := P0) (g₁ := T)).symm
  have hcomp11 :
      ((P1 ⊗ₗ (M.effect 1)) ∘ₗ (P1 ⊗ₗ T))
        = ((P1 * P1) ⊗ₗ ((M.effect 1) ∘ₗ T)) := by
    simpa [P1, Module.End.mul_eq_comp] using
      (TensorProduct.map_comp (f₂ := P1) (g₂ := M.effect 1) (f₁ := P1) (g₁ := T)).symm
  have hcomp10 :
      ((P1 ⊗ₗ (M.effect 1)) ∘ₗ (P0 ⊗ₗ T))
        = ((P1 * P0) ⊗ₗ ((M.effect 1) ∘ₗ T)) := by
    simpa [P0, P1, Module.End.mul_eq_comp] using
      (TensorProduct.map_comp (f₂ := P1) (g₂ := M.effect 1) (f₁ := P0) (g₁ := T)).symm
  have hcomp01 :
      ((P0 ⊗ₗ (M.effect 0)) ∘ₗ (P1 ⊗ₗ T))
        = ((P0 * P1) ⊗ₗ ((M.effect 0) ∘ₗ T)) := by
    simpa [P0, P1, Module.End.mul_eq_comp] using
      (TensorProduct.map_comp (f₂ := P0) (g₂ := M.effect 0) (f₁ := P1) (g₁ := T)).symm
  have hdiag0 :
      Complex.re (trace (((classicalProjector (X := Fin 2) 0) ⊗ₗ (M.effect 0)) ∘ₗ
        ((classicalProjector (X := Fin 2) 0) ⊗ₗ T)))
      = Complex.re (trace ((M.effect 0) ∘ₗ T)) := by
    calc
      Complex.re (trace (((classicalProjector (X := Fin 2) 0) ⊗ₗ (M.effect 0)) ∘ₗ
          ((classicalProjector (X := Fin 2) 0) ⊗ₗ T)))
          = Complex.re (trace (((P0 * P0) ⊗ₗ ((M.effect 0) ∘ₗ T)))) := by
              simpa [P0] using congrArg (fun Z => Complex.re (trace Z)) hcomp00
      _ = Complex.re (trace ((P0 ⊗ₗ ((M.effect 0) ∘ₗ T))
            : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))) := by
            simp [hmul00]
      _ = Complex.re (trace ((M.effect 0) ∘ₗ T)) := by
            simpa [P0] using congrArg Complex.re (htrace_tensor 0 ((M.effect 0) ∘ₗ T))
  have hdiag1 :
      Complex.re (trace (((classicalProjector (X := Fin 2) 1) ⊗ₗ (M.effect 1)) ∘ₗ
        ((classicalProjector (X := Fin 2) 1) ⊗ₗ T)))
      = Complex.re (trace ((M.effect 1) ∘ₗ T)) := by
    calc
      Complex.re (trace (((classicalProjector (X := Fin 2) 1) ⊗ₗ (M.effect 1)) ∘ₗ
          ((classicalProjector (X := Fin 2) 1) ⊗ₗ T)))
          = Complex.re (trace (((P1 * P1) ⊗ₗ ((M.effect 1) ∘ₗ T)))) := by
              simpa [P1] using congrArg (fun Z => Complex.re (trace Z)) hcomp11
      _ = Complex.re (trace ((P1 ⊗ₗ ((M.effect 1) ∘ₗ T))
            : Operator ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] E))) := by
            simp [hmul11]
      _ = Complex.re (trace ((M.effect 1) ∘ₗ T)) := by
            simpa [P1] using congrArg Complex.re (htrace_tensor 1 ((M.effect 1) ∘ₗ T))
  have hcross10 :
      Complex.re (trace (((classicalProjector (X := Fin 2) 1) ⊗ₗ (M.effect 1)) ∘ₗ
        ((classicalProjector (X := Fin 2) 0) ⊗ₗ T))) = 0 := by
    calc
      Complex.re (trace (((classicalProjector (X := Fin 2) 1) ⊗ₗ (M.effect 1)) ∘ₗ
          ((classicalProjector (X := Fin 2) 0) ⊗ₗ T)))
          = Complex.re (trace (((P1 * P0) ⊗ₗ ((M.effect 1) ∘ₗ T)))) := by
              simpa [P0, P1] using congrArg (fun Z => Complex.re (trace Z)) hcomp10
      _ = 0 := by
            unfold trace
            simp [hmul10]
  have hcross01 :
      Complex.re (trace (((classicalProjector (X := Fin 2) 0) ⊗ₗ (M.effect 0)) ∘ₗ
        ((classicalProjector (X := Fin 2) 1) ⊗ₗ T))) = 0 := by
    calc
      Complex.re (trace (((classicalProjector (X := Fin 2) 0) ⊗ₗ (M.effect 0)) ∘ₗ
          ((classicalProjector (X := Fin 2) 1) ⊗ₗ T)))
          = Complex.re (trace (((P0 * P1) ⊗ₗ ((M.effect 0) ∘ₗ T)))) := by
              simpa [P0, P1] using congrArg (fun Z => Complex.re (trace Z)) hcomp01
      _ = 0 := by
            unfold trace
            simp [hmul01]
  rw [hdiag0, hdiag1, hcross10, hcross01, zero_add, add_zero]
  calc
    Complex.re (trace ((M.effect 0) ∘ₗ T))
        + Complex.re (trace ((M.effect 1) ∘ₗ T))
        = Complex.re (trace ((M.effect 0) ∘ₗ T) + trace ((M.effect 1) ∘ₗ T)) := by
            simp [Complex.add_re]
    _ = Complex.re (trace (((M.effect 0) ∘ₗ T) + ((M.effect 1) ∘ₗ T))) := by
          unfold trace
          simp
    _ = Complex.re (trace (((M.effect 0 + M.effect 1) : Operator E) ∘ₗ T)) := by
          simp [LinearMap.add_comp]
    _ = Complex.re (trace (((LinearMap.id : Operator E)) ∘ₗ T)) := by
          simp [hsum]
    _ = Complex.re (trace T) := by simp
    _ = (1 / 2 : Real) := by
          have htr_re :
              Complex.re (trace (((τE : DensityOperator E) : Operator E))) = 1 := by
            simpa using congrArg Complex.re τE.trace_one
          simpa [T, trace, htr_re]

/-- The ideal Bell-induced bit is uniform and independent of Eve. -/
theorem ideal_bell_induces_uniform_independent_bit
    {E : Type*}
    [CpxFiniteHilbert E]
    (σXE : Operator (Qubit ⊗[ℂ] E))
    (hIdeal : IsUniformBitIndependent σXE) :
    pGuess σXE = (1 / 2 : Real) := by
  rcases hIdeal with ⟨τE, rfl⟩
  let S : Set Real :=
    {r : Real | ∃ M : POVM (Fin 2) E,
      r = guessFunctional (X := Fin 2) (E := E)
        (idealBitTensorState (E := E) ((τE : DensityOperator E) : Operator E)) M}
  have hS_sub : S ⊆ {(1 / 2 : Real)} := by
    intro r hr
    rcases hr with ⟨M, rfl⟩
    exact guessFunctional_const_of_uniform_bit_tensor (E := E) τE M
  have hEffect0 : IsEffect (0 : Operator E) := by
    constructor
    · simp
    · simp
  let Mtriv : POVM (Fin 2) E := BinaryPOVM.ofEffect (H := E) (0 : Operator E) hEffect0
  have hS_sup : {(1 / 2 : Real)} ⊆ S := by
    intro r hr
    rcases hr with rfl
    exact ⟨Mtriv, (guessFunctional_const_of_uniform_bit_tensor (E := E) τE Mtriv).symm⟩
  have hSeq : S = {(1 / 2 : Real)} := Set.Subset.antisymm hS_sub hS_sup
  change sSup S = (1 / 2 : Real)
  rw [hSeq]
  simp

/--
Core pGuess bound given an ideal reference state and an explicit ε-distance bound.

This is the irreducible combination of:
- `pGuess` continuity under trace distance,
- the ideal uniform-bit value `pGuess σXE = 1/2`.

Note: the CHSH-to-distance chain (converting hCHSH + hD_bridge into the ε-form)
is handled by the caller; this theorem just needs the final bound directly.
-/
theorem chsh_to_pGuess_bound
    {E : Type*}
    [CpxFiniteHilbert E]
    (ρXE σXE : DensityOperator (Qubit ⊗[ℂ] E))
    (ε : Real)
    (hIdeal :
      IsUniformBitIndependent
        (((σXE : DensityOperator (Qubit ⊗[ℂ] E)) : Operator (Qubit ⊗[ℂ] E))))
    (hD :
      traceDistance
        (((ρXE : DensityOperator (Qubit ⊗[ℂ] E)) : Operator (Qubit ⊗[ℂ] E)))
        (((σXE : DensityOperator (Qubit ⊗[ℂ] E)) : Operator (Qubit ⊗[ℂ] E)))
      ≤ Real.sqrt (ε / (2 * Real.sqrt 2)) + ε / (2 * Real.sqrt 2)) :
    pGuess (((ρXE : DensityOperator (Qubit ⊗[ℂ] E)) : Operator (Qubit ⊗[ℂ] E)))
      ≤ (1 / 2 : Real) + Real.sqrt (ε / (2 * Real.sqrt 2)) + ε / (2 * Real.sqrt 2) := by
  -- Chain: pGuess_continuity + hhalf rewrite + add_assoc + add_le_add.
  -- Avoids linarith (which calls ring_nf → whnf on traceDistance).
  refine le_trans (pGuess_continuity (E := E) ρXE σXE) ?_
  rw [ideal_bell_induces_uniform_independent_bit _ hIdeal]
  rw [add_assoc]
  exact add_le_add (le_refl _) hD

private theorem trace_rankOne_comp
    {H : Type*} [CpxFiniteHilbert H]
    (x y : H) (X : Operator H) :
    trace (((InnerProductSpace.rankOne ℂ x y).toLinearMap) ∘ₗ X) = ⟪y, X x⟫_ℂ := by
  unfold trace
  rw [LinearMap.trace_comp_comm']
  have h :
      X ∘ₗ ((InnerProductSpace.rankOne ℂ x y).toLinearMap)
        = (innerₛₗ ℂ y).smulRight (X x) := by
    ext z
    simp [InnerProductSpace.rankOne_apply]
  rw [h]
  exact
    (LinearMap.trace_smulRight (R := ℂ) (M := H) (f := innerₛₗ ℂ y) (x := X x))

private theorem partialTraceLeft_tensor_pureOp
    {H K : Type*} [CpxFiniteHilbert H] [CpxFiniteHilbert K]
    (ψ : H) (A : Operator K) :
    partialTraceLeft (H := H) (K := K) ((pureOp ψ) ⊗ₗ A) = (trace (pureOp ψ)) • A := by
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  calc
    ⟪y, partialTraceLeft (H := H) (K := K) ((pureOp ψ) ⊗ₗ A) x⟫_ℂ
        = trace (((InnerProductSpace.rankOne ℂ x y).toLinearMap) ∘ₗ
            partialTraceLeft (H := H) (K := K) ((pureOp ψ) ⊗ₗ A)) := by
              symm
              simpa using
                (trace_rankOne_comp (x := x) (y := y)
                  (X := partialTraceLeft (H := H) (K := K) ((pureOp ψ) ⊗ₗ A)))
    _ = trace (((LinearMap.id : Operator H) ⊗ₗ ((InnerProductSpace.rankOne ℂ x y).toLinearMap)) ∘ₗ
          (((pureOp ψ) : Operator H) ⊗ₗ A)) := by
            simpa using
              (trace_mul_partialTraceLeft
                (((InnerProductSpace.rankOne ℂ x y).toLinearMap) : Operator K)
                (((pureOp ψ) : Operator H) ⊗ₗ A))
    _ = trace ((((LinearMap.id : Operator H) ∘ₗ (pureOp ψ)) ⊗ₗ
          (((InnerProductSpace.rankOne ℂ x y).toLinearMap) ∘ₗ A)) :
            Operator (H ⊗[ℂ] K)) := by
            simpa [Module.End.mul_eq_comp] using
              congrArg (fun T => trace T)
                ((TensorProduct.map_comp
                  (f₂ := (LinearMap.id : Operator H))
                  (g₂ := ((InnerProductSpace.rankOne ℂ x y).toLinearMap : Operator K))
                  (f₁ := (pureOp ψ : Operator H))
                  (g₁ := A)).symm)
    _ = trace (((LinearMap.id : Operator H) ∘ₗ (pureOp ψ)) : Operator H) *
          trace ((((InnerProductSpace.rankOne ℂ x y).toLinearMap) ∘ₗ A) : Operator K) := by
            exact LinearMap.trace_tensorProduct' (R := ℂ)
              (M := H) (N := K)
              (f := ((LinearMap.id : Operator H) ∘ₗ (pureOp ψ)))
              (g := (((InnerProductSpace.rankOne ℂ x y).toLinearMap) ∘ₗ A))
    _ = trace (pureOp ψ) * ⟪y, A x⟫_ℂ := by
          rw [trace_rankOne_comp (x := x) (y := y) (X := A)]
          simp
    _ = ⟪y, ((trace (pureOp ψ)) • A) x⟫_ℂ := by
          simp [LinearMap.smul_apply, inner_smul_right]

private theorem conj_pureOp_of_adjoint_eq
    {H : Type*} [CpxFiniteHilbert H]
    (P : Operator H) (hP : LinearMap.adjoint P = P) (ψ : H) :
    P ∘ₗ pureOp ψ ∘ₗ P = pureOp (P ψ) := by
  ext x
  simp [pureOp_apply, LinearMap.comp_apply]
  have hinner := LinearMap.adjoint_inner_left (A := P) (x := x) (y := ψ)
  rw [hP] at hinner
  simp [hinner]

private theorem keyProjector_apply_tmul
    {E : Type} [CpxFiniteHilbert E]
    (x : Fin 2) (ab : ABSystem) (e : E) :
    keyProjector (E := E) x (ab ⊗ₜ[ℂ] e) =
      ((((if x = 0 then proj0 else proj1) : Operator Qubit) ⊗ₗ
          (LinearMap.id : Operator Qubit)) ab) ⊗ₜ[ℂ] e := by
  refine TensorProduct.induction_on ab ?_ ?_ ?_
  · simp
  · intro a b
    simpa [TensorProduct.map_tmul] using
      (keyProjector_tmul (E := E) (x := x) a b e)
  · intro ab₁ ab₂ h₁ h₂
    simp [TensorProduct.add_tmul, h₁, h₂]

private theorem bell_branch0_AB :
    ((((proj0 : Operator Qubit) ⊗ₗ (LinearMap.id : Operator Qubit)) ∘ₗ
        (pureOp Φ_plus)) ∘ₗ
      (((proj0 : Operator Qubit) ⊗ₗ (LinearMap.id : Operator Qubit))))
      = pureOp (((Real.sqrt 2 : ℂ)⁻¹) • ket00) := by
  let P0AB : Operator ABSystem :=
    (proj0 : Operator Qubit) ⊗ₗ (LinearMap.id : Operator Qubit)
  have hsa : LinearMap.adjoint P0AB = P0AB := by
    simp [P0AB, proj0_sa]
  have hmap : P0AB Φ_plus = ((Real.sqrt 2 : ℂ)⁻¹) • ket00 := by
    simp [P0AB, Φ_plus, ket00, ket11, TensorProduct.map_tmul, proj0_ket0, proj0_ket1]
  calc
    P0AB ∘ₗ pureOp Φ_plus ∘ₗ P0AB = pureOp (P0AB Φ_plus) := by
      simpa [LinearMap.comp_assoc] using
        (conj_pureOp_of_adjoint_eq (P := P0AB) hsa Φ_plus)
    _ = pureOp (((Real.sqrt 2 : ℂ)⁻¹) • ket00) := by rw [hmap]

private theorem bell_branch1_AB :
    ((((proj1 : Operator Qubit) ⊗ₗ (LinearMap.id : Operator Qubit)) ∘ₗ
        (pureOp Φ_plus)) ∘ₗ
      (((proj1 : Operator Qubit) ⊗ₗ (LinearMap.id : Operator Qubit))))
      = pureOp (((Real.sqrt 2 : ℂ)⁻¹) • ket11) := by
  let P1AB : Operator ABSystem :=
    (proj1 : Operator Qubit) ⊗ₗ (LinearMap.id : Operator Qubit)
  have hsa : LinearMap.adjoint P1AB = P1AB := by
    simp [P1AB, proj1_sa]
  have hmap : P1AB Φ_plus = ((Real.sqrt 2 : ℂ)⁻¹) • ket11 := by
    simp [P1AB, Φ_plus, ket00, ket11, TensorProduct.map_tmul, proj1_ket0, proj1_ket1]
  calc
    P1AB ∘ₗ pureOp Φ_plus ∘ₗ P1AB = pureOp (P1AB Φ_plus) := by
      simpa [LinearMap.comp_assoc] using
        (conj_pureOp_of_adjoint_eq (P := P1AB) hsa Φ_plus)
    _ = pureOp (((Real.sqrt 2 : ℂ)⁻¹) • ket11) := by rw [hmap]

private theorem sqrt2_ne_zero_complex : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))

private theorem trace_pureOp_half_ket00 :
    trace (pureOp (((Real.sqrt 2 : ℂ)⁻¹) • ket00) : Operator ABSystem) = (1 / 2 : ℂ) := by
  have hmul : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = (2 : ℂ) := by
    exact_mod_cast (by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] :
      (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2)
  calc
    trace (pureOp (((Real.sqrt 2 : ℂ)⁻¹) • ket00) : Operator ABSystem)
        = ((‖((Real.sqrt 2 : ℂ)⁻¹) • ket00‖ ^ 2 : ℝ) : ℂ) := by
              simpa using
                (trace_pureOp_comp (H := ABSystem)
                  (ψ := ((Real.sqrt 2 : ℂ)⁻¹) • ket00)
                  (X := (LinearMap.id : Operator ABSystem)))
    _ = (2 : ℂ)⁻¹ := by
          have hk0 : ‖ket0‖ = (1 : ℝ) := by simp [ket0]
          have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
          simp [norm_smul, ket00, hk0, Real.norm_eq_abs, abs_of_nonneg hsqrt_nonneg]
    _ = (1 / 2 : ℂ) := by
          norm_num [one_div]

private theorem trace_pureOp_half_ket11 :
    trace (pureOp (((Real.sqrt 2 : ℂ)⁻¹) • ket11) : Operator ABSystem) = (1 / 2 : ℂ) := by
  have hmul : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = (2 : ℂ) := by
    exact_mod_cast (by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] :
      (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2)
  calc
    trace (pureOp (((Real.sqrt 2 : ℂ)⁻¹) • ket11) : Operator ABSystem)
        = ((‖((Real.sqrt 2 : ℂ)⁻¹) • ket11‖ ^ 2 : ℝ) : ℂ) := by
              simpa using
                (trace_pureOp_comp (H := ABSystem)
                  (ψ := ((Real.sqrt 2 : ℂ)⁻¹) • ket11)
                  (X := (LinearMap.id : Operator ABSystem)))
    _ = (2 : ℂ)⁻¹ := by
          have hk1 : ‖ket1‖ = (1 : ℝ) := by simp [ket1]
          have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
          simp [norm_smul, ket11, hk1, Real.norm_eq_abs, abs_of_nonneg hsqrt_nonneg]
    _ = (1 / 2 : ℂ) := by
          norm_num [one_div]

private lemma rhoECond_bellTensor_bit0
    {E : Type} [CpxFiniteHilbert E] (A : Operator E) :
    rhoECond (E := E) ((((pureOp Φ_plus) : Operator ABSystem) ⊗ₗ A)) 0
      = (1 / 2 : ℂ) • A := by
  let P0AB : Operator ABSystem :=
    (proj0 : Operator Qubit) ⊗ₗ (LinearMap.id : Operator Qubit)
  have hsand :
      keyProjector (E := E) 0 ∘ₗ
          ((((pureOp Φ_plus) : Operator ABSystem) ⊗ₗ A)) ∘ₗ
          keyProjector (E := E) 0
        =
      (pureOp (((Real.sqrt 2 : ℂ)⁻¹) • ket00)) ⊗ₗ A := by
    apply LinearMap.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp
    · intro ab e
      calc
        (keyProjector (E := E) 0 ∘ₗ ((((pureOp Φ_plus) : Operator ABSystem) ⊗ₗ A)) ∘ₗ
            keyProjector (E := E) 0) (ab ⊗ₜ[ℂ] e)
            = (P0AB (((pureOp Φ_plus) : Operator ABSystem) (P0AB ab))) ⊗ₜ[ℂ] A e := by
                simp [LinearMap.comp_apply, keyProjector_apply_tmul, P0AB, TensorProduct.map_tmul]
        _ = (pureOp (((Real.sqrt 2 : ℂ)⁻¹) • ket00) ab) ⊗ₜ[ℂ] A e := by
              simpa [LinearMap.comp_apply] using
                congrArg (fun v : ABSystem => v ⊗ₜ[ℂ] A e)
                  (congrArg (fun T : Operator ABSystem => T ab) bell_branch0_AB)
        _ = (((pureOp (((Real.sqrt 2 : ℂ)⁻¹) • ket00)) ⊗ₗ A) : Operator (ABESystem E))
              (ab ⊗ₜ[ℂ] e) := by
                simp [TensorProduct.map_tmul]
    · intro z₁ z₂ hz₁ hz₂
      simp [map_add, hz₁, hz₂]
  dsimp [rhoECond]
  rw [hsand, partialTraceLeft_tensor_pureOp]
  simp [trace_pureOp_half_ket00]

private lemma rhoECond_bellTensor_bit1
    {E : Type} [CpxFiniteHilbert E] (A : Operator E) :
    rhoECond (E := E) ((((pureOp Φ_plus) : Operator ABSystem) ⊗ₗ A)) 1
      = (1 / 2 : ℂ) • A := by
  let P1AB : Operator ABSystem :=
    (proj1 : Operator Qubit) ⊗ₗ (LinearMap.id : Operator Qubit)
  have hsand :
      keyProjector (E := E) 1 ∘ₗ
          ((((pureOp Φ_plus) : Operator ABSystem) ⊗ₗ A)) ∘ₗ
          keyProjector (E := E) 1
        =
      (pureOp (((Real.sqrt 2 : ℂ)⁻¹) • ket11)) ⊗ₗ A := by
    apply LinearMap.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp
    · intro ab e
      calc
        (keyProjector (E := E) 1 ∘ₗ ((((pureOp Φ_plus) : Operator ABSystem) ⊗ₗ A)) ∘ₗ
            keyProjector (E := E) 1) (ab ⊗ₜ[ℂ] e)
            = (P1AB (((pureOp Φ_plus) : Operator ABSystem) (P1AB ab))) ⊗ₜ[ℂ] A e := by
                simp [LinearMap.comp_apply, keyProjector_apply_tmul, P1AB, TensorProduct.map_tmul]
        _ = (pureOp (((Real.sqrt 2 : ℂ)⁻¹) • ket11) ab) ⊗ₜ[ℂ] A e := by
              simpa [LinearMap.comp_apply] using
                congrArg (fun v : ABSystem => v ⊗ₜ[ℂ] A e)
                  (congrArg (fun T : Operator ABSystem => T ab) bell_branch1_AB)
        _ = (((pureOp (((Real.sqrt 2 : ℂ)⁻¹) • ket11)) ⊗ₗ A) : Operator (ABESystem E))
              (ab ⊗ₜ[ℂ] e) := by
                simp [TensorProduct.map_tmul]
    · intro z₁ z₂ hz₁ hz₂
      simp [map_add, hz₁, hz₂]
  dsimp [rhoECond]
  rw [hsand, partialTraceLeft_tensor_pureOp]
  simpa [trace_pureOp_half_ket11]

private theorem re_postselectSuccessC_eq_bellOverlapAB
    {E : Type} [CpxFiniteHilbert E]
    (ρABE : DensityOperator (ABESystem E)) :
    Complex.re (postselectSuccessC (E := E) (ρABE : Operator (ABESystem E)))
      = bellOverlapAB (ρAB ρABE) := by
  calc
    Complex.re (postselectSuccessC (E := E) (ρABE : Operator (ABESystem E)))
        = Complex.re
            (trace
              (((pureOp Φ_plus) : Operator ABSystem) ∘ₗ
                (Quantum.partialTraceRight (H := ABSystem) (K := E)
                  ((ρABE : DensityOperator (ABESystem E)) : Operator (ABESystem E))))) := by
          simpa [postselectSuccessC, postselectProjector] using
            congrArg Complex.re
              ((Quantum.trace_comp_partialTraceRight
                (H := ABSystem) (K := E)
                (((pureOp Φ_plus) : Operator ABSystem))
                (((ρABE : DensityOperator (ABESystem E)) : Operator (ABESystem E)))).symm)
    _ = bellOverlapAB (ρAB ρABE) := by
          simp [bellOverlapAB, ρAB, DensityOperator.partialTraceRight]


/--
Blueprint-faithful CHSH entropy bound.

**Inputs:** the physical ABE state `ρABE` and the CHSH parameter `ε`
(with auxiliary range assumptions `hε`, `hε'` kept in the signature).

**Only hypothesis:** the CHSH score on the AB marginal of `ρABE`.

**Internally derived quantities:**
- `ρXE`: the measured state from `ρABE`,
- `σXE`: an ideal reference `XE` state.

**Current status:** the theorem body is now reduced to one deferred helper
`hBridge` (the only `sorry`), which packages the remaining blueprint steps:
- construction of `ρXE, σXE` as `DensityOperator`s,
- ideality of `σXE` (`IsUniformBitIndependent`),
- bridge distance bound
  `D(ρXE,σXE) ≤ √(bellInfidelityAB (ρAB ρABE)) + bellInfidelityAB (ρAB ρABE)`.

After `hBridge`, the rest is fully discharged:
1. `chsh_to_traceDistance_bound` converts the bridge to the explicit
   `ε`-distance bound;
2. `chsh_to_pGuess_bound` yields the final `pGuess` inequality;
3. a final rewrite identifies `ρXE` with `rhoXE_from_ABE ρABE`.
-/
private noncomputable def rhoXE_from_ABE_density
    {E : Type}
    [CpxFiniteHilbert E]
    (ρABE : DensityOperator (ABESystem E)) : DensityOperator (Qubit ⊗[ℂ] E) :=
  { val := rhoXE_from_ABE (E := E) (ρABE : Operator (ABESystem E))
    isPSD := by
      let ρ : Operator (ABESystem E) := (ρABE : Operator (ABESystem E))
      have hρ_pos : ρ.IsPositive := IsPSD.isPositive ρABE.isHermitian ρABE.isPSD
      have hcond_pos : ∀ x : Fin 2, (rhoECond (E := E) ρ x).IsPositive := by
        intro x
        let Ux : Operator (ABESystem E) :=
          keyProjector (E := E) x ∘ₗ ρ ∘ₗ keyProjector (E := E) x
        have hUx_pos : Ux.IsPositive := by
          simpa [Ux, ρ, keyProjector_sa (E := E) x] using
            (LinearMap.IsPositive.conj_adjoint (hT := hρ_pos) (S := keyProjector (E := E) x))
        have hUx_psd : IsPSD Ux := by
          intro ψ
          exact hUx_pos.re_inner_nonneg_right ψ
        have hUx_herm : IsHermitian Ux := hUx_pos.isSymmetric
        exact IsPSD.isPositive
          (IsHermitian.partialTraceLeft (H := ABSystem) (K := E) hUx_herm)
          (IsPSD.partialTraceLeft (H := ABSystem) (K := E) hUx_psd)
      have hρXE_pos :
          (rhoXE_from_ABE (E := E) (ρABE : Operator (ABESystem E))).IsPositive := by
        dsimp [rhoXE_from_ABE]
        rw [Fin.sum_univ_two]
        exact
          (classicalProjector_tensor_isPositive (E := E) 0 _ (hcond_pos 0)).add
            (classicalProjector_tensor_isPositive (E := E) 1 _ (hcond_pos 1))
      intro ψ
      exact hρXE_pos.re_inner_nonneg_right ψ
    isHermitian := by
      let ρ : Operator (ABESystem E) := (ρABE : Operator (ABESystem E))
      have hρ_pos : ρ.IsPositive := IsPSD.isPositive ρABE.isHermitian ρABE.isPSD
      have hcond_pos : ∀ x : Fin 2, (rhoECond (E := E) ρ x).IsPositive := by
        intro x
        let Ux : Operator (ABESystem E) :=
          keyProjector (E := E) x ∘ₗ ρ ∘ₗ keyProjector (E := E) x
        have hUx_pos : Ux.IsPositive := by
          simpa [Ux, ρ, keyProjector_sa (E := E) x] using
            (LinearMap.IsPositive.conj_adjoint (hT := hρ_pos) (S := keyProjector (E := E) x))
        have hUx_psd : IsPSD Ux := by
          intro ψ
          exact hUx_pos.re_inner_nonneg_right ψ
        have hUx_herm : IsHermitian Ux := hUx_pos.isSymmetric
        exact IsPSD.isPositive
          (IsHermitian.partialTraceLeft (H := ABSystem) (K := E) hUx_herm)
          (IsPSD.partialTraceLeft (H := ABSystem) (K := E) hUx_psd)
      have hρXE_pos :
          (rhoXE_from_ABE (E := E) (ρABE : Operator (ABESystem E))).IsPositive := by
        dsimp [rhoXE_from_ABE]
        rw [Fin.sum_univ_two]
        exact
          (classicalProjector_tensor_isPositive (E := E) 0 _ (hcond_pos 0)).add
            (classicalProjector_tensor_isPositive (E := E) 1 _ (hcond_pos 1))
      exact hρXE_pos.isSymmetric
    trace_one := by
      let ρ : Operator (ABESystem E) := (ρABE : Operator (ABESystem E))
      change trace (rhoXE_from_ABE (E := E) ρ) = 1
      have htrace_tensor :
          ∀ x : Fin 2, ∀ A : Operator E,
            trace
                (((classicalProjector (X := Fin 2) x) ⊗ₗ A)
                  : Operator (Qubit ⊗[ℂ] E))
              = trace A := by
        intro x A
        have htp :
            trace
                (((classicalProjector (X := Fin 2) x) ⊗ₗ A)
                  : Operator (Qubit ⊗[ℂ] E))
              = trace (classicalProjector (X := Fin 2) x) * trace A := by
          exact (LinearMap.trace_tensorProduct' (R := ℂ)
            (M := Qubit) (N := E)
            (f := classicalProjector (X := Fin 2) x) (g := A))
        have htr :
            trace (classicalProjector (X := Fin 2) x) = 1 := by
          simpa [classicalProjector, classicalKet] using
            (trace_pureOp_comp (H := Qubit)
              (ψ := classicalKet (X := Fin 2) x)
              (X := (LinearMap.id : Operator Qubit)))
        calc
          trace
              (((classicalProjector (X := Fin 2) x) ⊗ₗ A)
                : Operator (Qubit ⊗[ℂ] E))
              = trace (classicalProjector (X := Fin 2) x) * trace A := htp
          _ = trace A := by simp [htr]
      have htrace_cond :
          ∀ x : Fin 2,
            trace (rhoECond (E := E) ρ x)
              = trace (H := ABESystem E)
                  ((((keyProjector (E := E) x) : Operator (ABESystem E)) ∘ₗ ρ)
                    : Operator (ABESystem E)) := by
        intro x
        calc
          trace (rhoECond (E := E) ρ x)
              = trace (H := ABESystem E)
                  ((((keyProjector (E := E) x : Operator (ABESystem E)) ∘ₗ ρ) ∘ₗ
                    keyProjector (E := E) x) : Operator (ABESystem E)) := by
                  simp [rhoECond, LinearMap.comp_assoc]
          _ = trace (H := ABESystem E)
                (((keyProjector (E := E) x : Operator (ABESystem E)) ∘ₗ ρ ∘ₗ
                  keyProjector (E := E) x) : Operator (ABESystem E)) := by
                simp [LinearMap.comp_assoc]
          _ = trace (H := ABESystem E)
                ((((keyProjector (E := E) x : Operator (ABESystem E)) ∘ₗ
                    keyProjector (E := E) x) ∘ₗ ρ) : Operator (ABESystem E)) := by
                simpa [Module.End.mul_eq_comp, LinearMap.comp_assoc] using
                  (LinearMap.trace_mul_comm ℂ
                    ((keyProjector (E := E) x) ∘ₗ ρ)
                    (keyProjector (E := E) x))
          _ = trace (H := ABESystem E)
                ((((keyProjector (E := E) x : Operator (ABESystem E)) ∘ₗ ρ))
                  : Operator (ABESystem E)) := by
                rw [keyProjector_idem (E := E) x]
      calc
        trace (rhoXE_from_ABE (E := E) ρ)
            = ∑ x : Fin 2,
                trace
                  ((((classicalProjector (X := Fin 2) x) ⊗ₗ rhoECond (E := E) ρ x)
                    : Operator (Qubit ⊗[ℂ] E))) := by
                      simp [rhoXE_from_ABE, trace]
        _ = ∑ x : Fin 2, trace (rhoECond (E := E) ρ x) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              exact htrace_tensor x (rhoECond (E := E) ρ x)
        _ = ∑ x : Fin 2,
              trace (H := ABESystem E)
                (((keyProjector (E := E) x) ∘ₗ ρ) : Operator (ABESystem E)) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              simpa [ρ] using htrace_cond x
        _ = trace (H := ABESystem E)
              (((∑ x : Fin 2, keyProjector (E := E) x) ∘ₗ ρ)
                : Operator (ABESystem E)) := by
              rw [Fin.sum_univ_two]
              simp [LinearMap.add_comp, trace]
        _ = trace ρ := by
              simpa using
                congrArg
                  (fun T : Operator (ABESystem E) => trace (T ∘ₗ ρ))
                  (keyProjector_sum (E := E))
        _ = 1 := by simpa [ρ] using ρABE.trace_one }

set_option maxHeartbeats 4000000 in
theorem chsh_to_pGuess_bound_of_measure_contract_and_gentle
    {E : Type}
    [CpxFiniteHilbert E]
    (ρABE : DensityOperator (ABESystem E))
    (ε : Real) (hε' : ε ≤ 2 * Real.sqrt 2 - 2)
    (hCHSH :
      (2 * Real.sqrt 2 - ε)
        ≤ Complex.re
            (trace
              (canonicalCHSH ∘ₗ
                ((ρAB ρABE : DensityOperator ABSystem) : Operator ABSystem)))) :
    pGuess (rhoXE_from_ABE (E := E) (ρABE : Operator (ABESystem E)))
      ≤ (1 / 2 : Real) + Real.sqrt (ε / (2 * Real.sqrt 2)) + ε / (2 * Real.sqrt 2) := by
  have hsucc_re_eq :
      Complex.re (postselectSuccessC (E := E) (ρABE : Operator (ABESystem E)))
        = bellOverlapAB (ρAB ρABE) :=
    re_postselectSuccessC_eq_bellOverlapAB (E := E) ρABE
  have hδ :
      bellInfidelityAB (ρAB ρABE) ≤ ε / (2 * Real.sqrt 2) :=
    bellInfidelityAB_le_of_chsh (ρAB := ρAB ρABE) (ε := ε) hCHSH
  have hfrac_lt_one : ε / (2 * Real.sqrt 2) < 1 := by
    have hden_pos : 0 < 2 * Real.sqrt 2 := by positivity
    have hnum_lt : ε < 2 * Real.sqrt 2 := by
      linarith
    exact (div_lt_iff₀ hden_pos).2 (hnum_lt.trans_eq (one_mul _).symm)
  have hoverlap_pos : 0 < bellOverlapAB (ρAB ρABE) := by
    have hδ_lt_one : bellInfidelityAB (ρAB ρABE) < 1 :=
      lt_of_le_of_lt hδ hfrac_lt_one
    have hlt : 1 - bellOverlapAB (ρAB ρABE) < 1 := by
      simpa [bellInfidelityAB] using hδ_lt_one
    linarith
  have hpneq_zero : postselectSuccessC (E := E) (ρABE : Operator (ABESystem E)) ≠ 0 := by
    intro hs_zero
    have hs_re_zero :
        Complex.re (postselectSuccessC (E := E) (ρABE : Operator (ABESystem E))) = 0 := by
      simp [hs_zero]
    rw [hsucc_re_eq] at hs_re_zero
    linarith
  let ρXE : Operator (Qubit ⊗[ℂ] E) :=
    rhoXE_from_ABE (E := E) (ρABE : Operator (ABESystem E))
  -- Blueprint formula:
  -- τ_E = (1/p) * (⟨Φ+| ⊗ I) ρ_ABE (|Φ+⟩ ⊗ I), with p = Tr((Φ ⊗ I) ρ_ABE).
  let τE : Operator E :=
    ((postselectSuccessC (E := E) (ρABE : Operator (ABESystem E)))⁻¹ : ℂ) •
      bellPartialElement (E := E) (ρABE : Operator (ABESystem E))
  let τEd : DensityOperator E :=
    { val := τE
      isPSD := by
        let ρ : Operator (ABESystem E) := (ρABE : Operator (ABESystem E))
        let P : Operator (ABESystem E) := postselectProjector (E := E)
        let U : Operator (ABESystem E) := postselectUnnormalized (E := E) ρ
        let s : ℂ := postselectSuccessC (E := E) ρ
        let p : ℝ := Complex.re s
        have hρ_pos : ρ.IsPositive := IsPSD.isPositive ρABE.isHermitian ρABE.isPSD
        have hPadj : LinearMap.adjoint P = P := by simp [P, postselectProjector, pureOp]
        have hU_pos : U.IsPositive := by
          simpa [U, ρ, hPadj] using LinearMap.IsPositive.conj_adjoint (hT := hρ_pos) (S := P)
        have hU_trace : trace (H := ABESystem E) U = s := by
          simpa [U, s, ρ] using (trace_postselectUnnormalized (E := E) ρ)
        -- s is real (trace of a positive operator equals its real eigenvalue sum)
        have hs_real : s = (p : ℂ) := by
          have h1 : trace (H := ABESystem E) U =
              ↑(∑ i : Fin _, hU_pos.isSymmetric.eigenvalues (hn := rfl) i) :=
            by simpa [trace] using hU_pos.isSymmetric.trace_eq_sum_eigenvalues (hn := rfl)
          have h2 : p = ∑ i : Fin _, hU_pos.isSymmetric.eigenvalues (hn := rfl) i :=
            by simpa [p, trace, ← hU_trace] using
              hU_pos.isSymmetric.re_trace_eq_sum_eigenvalues (hn := rfl)
          rw [← hU_trace, h1, ← h2]
        -- 0 ≤ p: eigenvalues of a positive operator are nonneg
        have hp_nonneg : 0 ≤ p := by
          have h1 : Complex.re (trace (H := ABESystem E) U) =
              ∑ i : Fin _, hU_pos.isSymmetric.eigenvalues (hn := rfl) i :=
            by simpa [trace] using hU_pos.isSymmetric.re_trace_eq_sum_eigenvalues (hn := rfl)
          have hsum_nonneg : 0 ≤ ∑ i : Fin _, hU_pos.isSymmetric.eigenvalues (hn := rfl) i := by
            exact Finset.sum_nonneg (fun i _ => hU_pos.nonneg_eigenvalues (hn := rfl) i)
          have hs_re : s.re = ∑ i : Fin _, hU_pos.isSymmetric.eigenvalues (hn := rfl) i := by
            simpa [hU_trace] using h1
          calc
            0 ≤ ∑ i : Fin _, hU_pos.isSymmetric.eigenvalues (hn := rfl) i := hsum_nonneg
            _ = p := by simpa [p] using hs_re.symm
        -- ⟪ψ, contractLeft h z⟫ = ⟪tensorLeft h ψ, z⟫ (adjoint identity)
        have hInnerCL : ∀ (h : ABSystem) (ψ : E) (z : ABSystem ⊗[ℂ] E),
            ⟪ψ, Quantum.contractLeft (H := ABSystem) (K := E) h z⟫_ℂ
              = ⟪Quantum.tensorLeft (H := ABSystem) (K := E) h ψ, z⟫_ℂ := fun h ψ z => by
          refine TensorProduct.induction_on z ?_ ?_ ?_
          · simp [Quantum.contractLeft]
          · intro h' k
            simp [Quantum.contractLeft, Quantum.tensorLeft, TensorProduct.inner_tmul,
              inner_smul_right]
          · intro z₁ z₂ hz₁ hz₂; simp [hz₁, hz₂, inner_add_right]
        -- bellPartialElement ρ is PSD: ⟪Φ+⊗ψ, ρ(Φ+⊗ψ)⟫ ≥ 0 by positivity of ρ
        have hBellPSD : IsPSD (bellPartialElement (E := E) ρ) := fun ψ => by
          simpa [bellPartialElement, LinearMap.comp_apply, hInnerCL] using
            hρ_pos.re_inner_nonneg_right _
        -- Scaling by p⁻¹ ≥ 0 preserves PSD
        have hScaledPSD : IsPSD (((p⁻¹ : ℂ) • bellPartialElement (E := E) ρ) : Operator E) :=
          fun ψ => by
            simpa [inner_smul_right, Complex.mul_re] using
              mul_nonneg (inv_nonneg.mpr hp_nonneg) (hBellPSD ψ)
        simpa [τE, s, ρ] using show
            IsPSD (((s⁻¹ : ℂ) • bellPartialElement (E := E) ρ) : Operator E) by
          simpa [hs_real, Complex.ofReal_inv] using hScaledPSD
      isHermitian := by
        let ρ : Operator (ABESystem E) := (ρABE : Operator (ABESystem E))
        let U : Operator (ABESystem E) := postselectUnnormalized (E := E) ρ
        let s : ℂ := postselectSuccessC (E := E) ρ
        let p : ℝ := Complex.re s
        have hρ_pos : ρ.IsPositive := IsPSD.isPositive ρABE.isHermitian ρABE.isPSD
        have hU_trace : trace (H := ABESystem E) U = s := by
          simpa [U, s, ρ] using (trace_postselectUnnormalized (E := E) ρ)
        have hInnerCL : ∀ (h : ABSystem) (ψ : E) (z : ABSystem ⊗[ℂ] E),
            ⟪ψ, Quantum.contractLeft (H := ABSystem) (K := E) h z⟫_ℂ
              = ⟪Quantum.tensorLeft (H := ABSystem) (K := E) h ψ, z⟫_ℂ := fun h ψ z => by
          refine TensorProduct.induction_on z ?h0 ?ht ?ha
          · simp [Quantum.contractLeft]
          · intro h' k
            simp [Quantum.contractLeft, Quantum.tensorLeft, TensorProduct.inner_tmul,
              inner_smul_right]
          · intro z₁ z₂ hz₁ hz₂; simp [hz₁, hz₂, inner_add_right]
        have hadj_tensor :
            LinearMap.adjoint (Quantum.tensorLeft (H := ABSystem) (K := E) Φ_plus)
              = Quantum.contractLeft (H := ABSystem) (K := E) Φ_plus := by
          apply LinearMap.ext
          intro z
          apply ext_inner_right ℂ
          intro ψ
          calc
            ⟪(LinearMap.adjoint (Quantum.tensorLeft (H := ABSystem) (K := E) Φ_plus)) z, ψ⟫_ℂ
                = ⟪z, (Quantum.tensorLeft (H := ABSystem) (K := E) Φ_plus) ψ⟫_ℂ := by
                    simpa using
                      (LinearMap.adjoint_inner_left
                        (A := Quantum.tensorLeft (H := ABSystem) (K := E) Φ_plus)
                        (x := ψ) (y := z))
            _ = ⟪Quantum.contractLeft (H := ABSystem) (K := E) Φ_plus z, ψ⟫_ℂ := by
                  have hEq :
                      ⟪Quantum.contractLeft (H := ABSystem) (K := E) Φ_plus z, ψ⟫_ℂ
                        = ⟪z, Quantum.tensorLeft (H := ABSystem) (K := E) Φ_plus ψ⟫_ℂ := by
                    calc
                      ⟪Quantum.contractLeft (H := ABSystem) (K := E) Φ_plus z, ψ⟫_ℂ
                          = star (⟪ψ,
                              Quantum.contractLeft (H := ABSystem) (K := E) Φ_plus z⟫_ℂ) := by
                              simp
                      _ = star (⟪Quantum.tensorLeft (H := ABSystem) (K := E) Φ_plus ψ, z⟫_ℂ) := by
                            rw [hInnerCL Φ_plus ψ z]
                      _ = ⟪z, Quantum.tensorLeft (H := ABSystem) (K := E) Φ_plus ψ⟫_ℂ := by
                            exact inner_conj_symm z
                              (Quantum.tensorLeft (H := ABSystem) (K := E) Φ_plus ψ)
                  simpa using hEq.symm
        have hadj_contract :
            LinearMap.adjoint (Quantum.contractLeft (H := ABSystem) (K := E) Φ_plus)
              = Quantum.tensorLeft (H := ABSystem) (K := E) Φ_plus := by
          have h' := congrArg LinearMap.adjoint hadj_tensor
          simpa using h'.symm
        have hBell_pos : (bellPartialElement (E := E) ρ).IsPositive := by
          simpa [bellPartialElement, hadj_contract] using
            (LinearMap.IsPositive.conj_adjoint (hT := hρ_pos)
              (S := Quantum.contractLeft (H := ABSystem) (K := E) Φ_plus))
        have hs_real : s = (p : ℂ) := by
          have hU_pos : U.IsPositive := by
            let P : Operator (ABESystem E) := postselectProjector (E := E)
            have hPadj : LinearMap.adjoint P = P := by
              simp [P, postselectProjector, pureOp]
            simpa [U, ρ, hPadj] using
              LinearMap.IsPositive.conj_adjoint (hT := hρ_pos) (S := P)
          have h1 : trace (H := ABESystem E) U =
              ↑(∑ i : Fin _, hU_pos.isSymmetric.eigenvalues (hn := rfl) i) := by
            simpa [trace] using hU_pos.isSymmetric.trace_eq_sum_eigenvalues (hn := rfl)
          have h2 : p = ∑ i : Fin _, hU_pos.isSymmetric.eigenvalues (hn := rfl) i := by
            simpa [p, trace, ← hU_trace] using
              hU_pos.isSymmetric.re_trace_eq_sum_eigenvalues (hn := rfl)
          rw [← hU_trace, h1, ← h2]
        have hs_inv_real : (starRingEnd ℂ) (s⁻¹) = s⁻¹ := by
          simp [hs_real]
        simpa [IsHermitian, τE, s, ρ] using
          (LinearMap.IsSymmetric.smul (c := s⁻¹) hs_inv_real hBell_pos.isSymmetric)
      trace_one := by
        let ρ : Operator (ABESystem E) := (ρABE : Operator (ABESystem E))
        let s : ℂ := postselectSuccessC (E := E) ρ
        have hs_ne : s ≠ 0 := by
          simpa [s, ρ] using hpneq_zero
        have hPhi_tr : trace (H := ABSystem) (pureOp Φ_plus) = 1 := by
          simpa using
            (trace_pureOp_comp (H := ABSystem) (ψ := Φ_plus)
              (X := (LinearMap.id : Operator ABSystem)))
        have hU_trace : trace (H := ABESystem E) (postselectUnnormalized (E := E) ρ) = s := by
          simpa [s] using (trace_postselectUnnormalized (E := E) ρ)
        have hprod :
            trace (H := ABSystem) (pureOp Φ_plus)
              * trace (H := E) (bellPartialElement (E := E) ρ) = s := by
          calc
            trace (H := ABSystem) (pureOp Φ_plus)
                * trace (H := E) (bellPartialElement (E := E) ρ)
                = trace (H := ABESystem E)
                    (((pureOp Φ_plus) ⊗ₗ (bellPartialElement (E := E) ρ)) :
                      Operator (ABESystem E)) := by
                    simpa using
                      (LinearMap.trace_tensorProduct' (R := ℂ)
                        (M := ABSystem) (N := E)
                        (f := pureOp Φ_plus) (g := bellPartialElement (E := E) ρ)).symm
            _ = trace (H := ABESystem E) (postselectUnnormalized (E := E) ρ) := by
                  rw [postselectUnnormalized_eq_bellTensor (E := E) ρ]
            _ = s := hU_trace
        have hBell_tr : trace (H := E) (bellPartialElement (E := E) ρ) = s := by
          have hprod' : (1 : ℂ) * trace (H := E) (bellPartialElement (E := E) ρ) = s := by
            simpa [hPhi_tr] using hprod
          simpa using hprod'
        calc
          trace (H := E) τE
              = trace (H := E) (((s⁻¹ : ℂ) • bellPartialElement (E := E) ρ) : Operator E) := by
                  simp [τE, s, ρ]
          _ = ((s⁻¹ : ℂ) * trace (H := E) (bellPartialElement (E := E) ρ)) := by
                simp [trace]
          _ = ((s⁻¹ : ℂ) * s) := by rw [hBell_tr]
          _ = 1 := by simp [hs_ne]
    }
  -- Hence σ_XE = (I_X / 2) ⊗ τ_E.
  let σXE : Operator (Qubit ⊗[ℂ] E) := idealBitTensorState (E := E) τE
  let ρXEd : DensityOperator (Qubit ⊗[ℂ] E) := rhoXE_from_ABE_density (E := E) ρABE
  let σXEd : DensityOperator (Qubit ⊗[ℂ] E) :=
    { val := σXE
      isPSD := by
        have hτ_pos : τE.IsPositive := IsPSD.isPositive τEd.isHermitian τEd.isPSD
        have hhalf_pos : (((1 / 2 : ℂ) • τE) : Operator E).IsPositive := by
          refine ⟨?_, ?_⟩
          · have hs : (starRingEnd ℂ) ((1 / 2 : ℂ)) = (1 / 2 : ℂ) := by
              simpa using (Complex.conj_ofReal (1 / 2 : ℝ))
            simpa [IsHermitian] using
              (LinearMap.IsSymmetric.smul (c := (1 / 2 : ℂ)) hs hτ_pos.isSymmetric)
          · intro ψ
            simpa [LinearMap.smul_apply, inner_smul_left, Complex.mul_re] using
              mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) (hτ_pos.re_inner_nonneg_left ψ)
        have hσ_pos : σXE.IsPositive := by
          dsimp [σXE, idealBitTensorState]
          rw [Fin.sum_univ_two]
          exact
            (classicalProjector_tensor_isPositive (E := E) 0 _ hhalf_pos).add
              (classicalProjector_tensor_isPositive (E := E) 1 _ hhalf_pos)
        intro ψ
        exact hσ_pos.re_inner_nonneg_right ψ
      isHermitian := by
        have hτ_pos : τE.IsPositive := IsPSD.isPositive τEd.isHermitian τEd.isPSD
        have hhalf_pos : (((1 / 2 : ℂ) • τE) : Operator E).IsPositive := by
          refine ⟨?_, ?_⟩
          · have hs : (starRingEnd ℂ) ((1 / 2 : ℂ)) = (1 / 2 : ℂ) := by
              simpa using (Complex.conj_ofReal (1 / 2 : ℝ))
            simpa [IsHermitian] using
              (LinearMap.IsSymmetric.smul (c := (1 / 2 : ℂ)) hs hτ_pos.isSymmetric)
          · intro ψ
            simpa [LinearMap.smul_apply, inner_smul_left, Complex.mul_re] using
              mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) (hτ_pos.re_inner_nonneg_left ψ)
        have hσ_pos : σXE.IsPositive := by
          dsimp [σXE, idealBitTensorState]
          rw [Fin.sum_univ_two]
          exact
            (classicalProjector_tensor_isPositive (E := E) 0 _ hhalf_pos).add
              (classicalProjector_tensor_isPositive (E := E) 1 _ hhalf_pos)
        exact hσ_pos.isSymmetric
      trace_one := by
        have htrace_tensor :
            ∀ x : Fin 2, ∀ A : Operator E,
              trace
                  (((classicalProjector (X := Fin 2) x) ⊗ₗ A)
                    : Operator (Qubit ⊗[ℂ] E))
                = trace A := by
          intro x A
          have htp :
              trace
                  (((classicalProjector (X := Fin 2) x) ⊗ₗ A)
                    : Operator (Qubit ⊗[ℂ] E))
                = trace (classicalProjector (X := Fin 2) x) * trace A := by
            exact (LinearMap.trace_tensorProduct' (R := ℂ)
              (M := Qubit) (N := E)
              (f := classicalProjector (X := Fin 2) x) (g := A))
          have htr :
              trace (classicalProjector (X := Fin 2) x) = 1 := by
            simpa [classicalProjector, classicalKet] using
              (trace_pureOp_comp (H := Qubit)
                (ψ := classicalKet (X := Fin 2) x)
                (X := (LinearMap.id : Operator Qubit)))
          calc
            trace
                (((classicalProjector (X := Fin 2) x) ⊗ₗ A)
                  : Operator (Qubit ⊗[ℂ] E))
                = trace (classicalProjector (X := Fin 2) x) * trace A := htp
            _ = trace A := by simp [htr]
        have hτ_trace : trace τE = 1 := by
          simpa [τEd, τE] using τEd.trace_one
        calc
          trace σXE
              = ∑ x : Fin 2,
                  trace
                    ((((classicalProjector (X := Fin 2) x) ⊗ₗ ((1 / 2 : ℂ) • τE))
                      : Operator (Qubit ⊗[ℂ] E))) := by
                        simp [σXE, idealBitTensorState, trace]
          _ = ∑ x : Fin 2, trace (((1 / 2 : ℂ) • τE) : Operator E) := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                exact htrace_tensor x (((1 / 2 : ℂ) • τE) : Operator E)
          _ = ∑ x : Fin 2, ((1 / 2 : ℂ) * trace τE) := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                simp [trace]
          _ = ∑ x : Fin 2, (1 / 2 : ℂ) := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                simp [hτ_trace]
          _ = 1 := by
                simp only [one_div, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                  nsmul_eq_mul, Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
                  mul_inv_cancel₀]
    }
  have hIdeal : IsUniformBitIndependent σXE := by
    dsimp [IsUniformBitIndependent]
    use τEd

  have hD_bridge :
      traceDistance ρXE σXE
        ≤ Real.sqrt (bellInfidelityAB (ρAB ρABE)) + bellInfidelityAB (ρAB ρABE) := by
    let p : Real := Complex.re (postselectSuccessC (E := E) (ρABE : Operator (ABESystem E)))
    let ρPostABE : DensityOperator (ABESystem E) :=
      { val := postselectState (E := E) (ρABE : Operator (ABESystem E))
        isPSD := by
          let ρ : Operator (ABESystem E) := (ρABE : Operator (ABESystem E))
          let P : Operator (ABESystem E) := postselectProjector (E := E)
          let U : Operator (ABESystem E) := postselectUnnormalized (E := E) ρ
          let s : ℂ := postselectSuccessC (E := E) ρ
          let p : ℝ := Complex.re s
          have hs_ne : s ≠ 0 := by simpa [s, ρ] using hpneq_zero
          have hρ_pos : ρ.IsPositive := IsPSD.isPositive ρABE.isHermitian ρABE.isPSD
          have hPadj : LinearMap.adjoint P = P := by simp [P, postselectProjector, pureOp]
          have hU_pos : U.IsPositive := by
            simpa [U, ρ, hPadj] using LinearMap.IsPositive.conj_adjoint (hT := hρ_pos) (S := P)
          have hU_trace : trace (H := ABESystem E) U = s := by
            simpa [U, s, ρ] using (trace_postselectUnnormalized (E := E) ρ)
          have hs_real : s = (p : ℂ) := by
            have h1 : trace (H := ABESystem E) U =
                ↑(∑ i : Fin _, hU_pos.isSymmetric.eigenvalues (hn := rfl) i) := by
              simpa [trace] using hU_pos.isSymmetric.trace_eq_sum_eigenvalues (hn := rfl)
            have h2 : p = ∑ i : Fin _, hU_pos.isSymmetric.eigenvalues (hn := rfl) i := by
              simpa [p, trace, ← hU_trace] using
                hU_pos.isSymmetric.re_trace_eq_sum_eigenvalues (hn := rfl)
            rw [← hU_trace, h1, ← h2]
          have hp_nonneg : 0 ≤ p := by
            have h1 : Complex.re (trace (H := ABESystem E) U) =
                ∑ i : Fin _, hU_pos.isSymmetric.eigenvalues (hn := rfl) i := by
              simpa [trace] using hU_pos.isSymmetric.re_trace_eq_sum_eigenvalues (hn := rfl)
            have hsum_nonneg : 0 ≤ ∑ i : Fin _, hU_pos.isSymmetric.eigenvalues (hn := rfl) i := by
              exact Finset.sum_nonneg (fun i _ => hU_pos.nonneg_eigenvalues (hn := rfl) i)
            have hs_re : s.re = ∑ i : Fin _, hU_pos.isSymmetric.eigenvalues (hn := rfl) i := by
              simpa [hU_trace] using h1
            calc
              0 ≤ ∑ i : Fin _, hU_pos.isSymmetric.eigenvalues (hn := rfl) i := hsum_nonneg
              _ = p := by simpa [p] using hs_re.symm
          have hScaledPSD : IsPSD (((p⁻¹ : ℂ) • U) : Operator (ABESystem E)) :=
            fun ψ => by
              calc
                0 ≤ p⁻¹ * Complex.re ⟪ψ, U ψ⟫_ℂ := by
                      exact mul_nonneg (inv_nonneg.mpr hp_nonneg) (hU_pos.re_inner_nonneg_right ψ)
                _ = Complex.re (((p⁻¹ : ℂ) * ⟪ψ, U ψ⟫_ℂ) : ℂ) := by
                      simp [Complex.mul_re]
                _ = Complex.re ⟪ψ, (((p⁻¹ : ℂ) • U) : Operator (ABESystem E)) ψ⟫_ℂ := by
                      simp [LinearMap.smul_apply, inner_smul_right]
          simpa [postselectState, s, ρ] using show
              IsPSD (((s⁻¹ : ℂ) • U) : Operator (ABESystem E)) by
            simpa [hs_real, Complex.ofReal_inv] using hScaledPSD
        isHermitian := by
          let ρ : Operator (ABESystem E) := (ρABE : Operator (ABESystem E))
          let P : Operator (ABESystem E) := postselectProjector (E := E)
          let U : Operator (ABESystem E) := postselectUnnormalized (E := E) ρ
          let s : ℂ := postselectSuccessC (E := E) ρ
          let p : ℝ := Complex.re s
          have hρ_pos : ρ.IsPositive := IsPSD.isPositive ρABE.isHermitian ρABE.isPSD
          have hPadj : LinearMap.adjoint P = P := by simp [P, postselectProjector, pureOp]
          have hU_pos : U.IsPositive := by
            simpa [U, ρ, hPadj] using LinearMap.IsPositive.conj_adjoint (hT := hρ_pos) (S := P)
          have hU_trace : trace (H := ABESystem E) U = s := by
            simpa [U, s, ρ] using (trace_postselectUnnormalized (E := E) ρ)
          have hs_real : s = (p : ℂ) := by
            have h1 : trace (H := ABESystem E) U =
                ↑(∑ i : Fin _, hU_pos.isSymmetric.eigenvalues (hn := rfl) i) := by
              simpa [trace] using hU_pos.isSymmetric.trace_eq_sum_eigenvalues (hn := rfl)
            have h2 : p = ∑ i : Fin _, hU_pos.isSymmetric.eigenvalues (hn := rfl) i := by
              simpa [p, trace, ← hU_trace] using
                hU_pos.isSymmetric.re_trace_eq_sum_eigenvalues (hn := rfl)
            rw [← hU_trace, h1, ← h2]
          have hs_inv_real : (starRingEnd ℂ) (s⁻¹) = s⁻¹ := by
            simp [hs_real]
          simpa [postselectState, s, ρ] using
            (LinearMap.IsSymmetric.smul (c := s⁻¹) hs_inv_real hU_pos.isSymmetric)
        trace_one := by
          simpa using
            (trace_postselectState_eq_one (E := E)
              (ρABE := (ρABE : Operator (ABESystem E))) hpneq_zero)
      }
    have hMeasure_norm :
        traceNorm
          (rhoXE_from_ABE (E := E) ((ρABE : Operator (ABESystem E)))
            - rhoXE_from_ABE (E := E) ((ρPostABE : Operator (ABESystem E))))
          ≤
        traceNorm
          ((ρABE : Operator (ABESystem E))
            - (ρPostABE : Operator (ABESystem E))) := by
      simpa using RigidityToPguess.measure_contract (E := E) ρABE ρPostABE
    have hMeasure_dist :
        traceDistance ρXE (rhoXE_from_ABE (E := E) ((ρPostABE : Operator (ABESystem E))))
          ≤ traceDistance
              ((ρABE : Operator (ABESystem E)))
              ((ρPostABE : Operator (ABESystem E))) := by
      simpa [traceDistance, ρXE] using
        mul_le_mul_of_nonneg_left hMeasure_norm (by norm_num : (0 : Real) ≤ (1 / 2 : Real))
    have hGentle_norm :
        traceNorm
            ((ρABE : Operator (ABESystem E))
              - (ρPostABE : Operator (ABESystem E)))
          ≤ 2 * Real.sqrt (1 - p) + 2 * (1 - p) := by
      simpa [ρPostABE, p] using
        (gentle_postselection_bound (E := E) ρABE hpneq_zero)
    have hGentle_dist :
        traceDistance
            ((ρABE : Operator (ABESystem E)))
            ((ρPostABE : Operator (ABESystem E)))
          ≤ Real.sqrt (1 - p) + (1 - p) := by
      calc
        traceDistance
            ((ρABE : Operator (ABESystem E)))
            ((ρPostABE : Operator (ABESystem E)))
            = (1 / 2 : Real) *
                traceNorm
                  (((ρABE : Operator (ABESystem E)))
                    - ((ρPostABE : Operator (ABESystem E)))) := rfl
        _ ≤ (1 / 2 : Real) * (2 * Real.sqrt (1 - p) + 2 * (1 - p)) := by
              exact mul_le_mul_of_nonneg_left hGentle_norm (by norm_num : (0 : Real) ≤ (1 / 2 : Real))
        _ = Real.sqrt (1 - p) + (1 - p) := by ring
    have hσ_eq :
        rhoXE_from_ABE (E := E) ((ρPostABE : Operator (ABESystem E))) = σXE := by
      change rhoXE_from_ABE (E := E)
          (postselectState (E := E) (ρABE : Operator (ABESystem E))) = σXE
      rw [postselectState_eq_bellTensor (E := E) (ρABE := (ρABE : Operator (ABESystem E)))]
      rw [rhoXE_from_ABE, Fin.sum_univ_two]
      let Tpost : Operator (ABESystem E) :=
        (((pureOp Φ_plus) : Operator ABSystem) ⊗ₗ
          ((postselectSuccessC (E := E) (ρABE : Operator (ABESystem E)))⁻¹ •
            bellPartialElement (E := E) (ρABE : Operator (ABESystem E))))
      have h0 :
          rhoECond (E := E)
            Tpost 0
            = (1 / 2 : ℂ) • τE := by
        simpa [Tpost, τE] using rhoECond_bellTensor_bit0 (E := E) (A := τE)
      have h1 :
          rhoECond (E := E)
            Tpost 1
            = (1 / 2 : ℂ) • τE := by
        simpa [Tpost, τE] using rhoECond_bellTensor_bit1 (E := E) (A := τE)
      rw [h0, h1]
      simp [σXE, idealBitTensorState, Fin.sum_univ_two]
    have hp_to_delta :
        1 - p = bellInfidelityAB (ρAB ρABE) := by
      have hp_eq_overlap : p = bellOverlapAB (ρAB ρABE) := by
        simpa [p] using re_postselectSuccessC_eq_bellOverlapAB (E := E) ρABE
      calc
        1 - p = 1 - bellOverlapAB (ρAB ρABE) := by rw [hp_eq_overlap]
        _ = bellInfidelityAB (ρAB ρABE) := by
              simp [bellInfidelityAB]
    calc
      traceDistance ρXE σXE
          = traceDistance ρXE
              (rhoXE_from_ABE (E := E) ((ρPostABE : Operator (ABESystem E)))) := by
                rw [hσ_eq]
      _ ≤ traceDistance
            ((ρABE : Operator (ABESystem E)))
            ((ρPostABE : Operator (ABESystem E))) := hMeasure_dist
      _ ≤ Real.sqrt (1 - p) + (1 - p) := hGentle_dist
      _ = Real.sqrt (bellInfidelityAB (ρAB ρABE)) + bellInfidelityAB (ρAB ρABE) := by
            simp [hp_to_delta]
  have hD_explicit :
      traceDistance
        (((ρXEd : DensityOperator (Qubit ⊗[ℂ] E)) : Operator (Qubit ⊗[ℂ] E)))
        (((σXEd : DensityOperator (Qubit ⊗[ℂ] E)) : Operator (Qubit ⊗[ℂ] E)))
        ≤ Real.sqrt (ε / (2 * Real.sqrt 2)) + ε / (2 * Real.sqrt 2) := by
    have hD_explicit_op :
        traceDistance ρXE σXE
          ≤ Real.sqrt (ε / (2 * Real.sqrt 2)) + ε / (2 * Real.sqrt 2) := by
      have hδ :
          bellInfidelityAB (ρAB ρABE) ≤ ε / (2 * Real.sqrt 2) :=
        bellInfidelityAB_le_of_chsh (ρAB := ρAB ρABE) (ε := ε) hCHSH
      exact le_trans hD_bridge (add_le_add (Real.sqrt_le_sqrt hδ) hδ)
    change traceDistance
        (rhoXE_from_ABE (E := E) (ρABE : Operator (ABESystem E)))
        σXE
      ≤ Real.sqrt (ε / (2 * Real.sqrt 2)) + ε / (2 * Real.sqrt 2)
    simpa [ρXE, ρXEd, σXEd, rhoXE_from_ABE_density] using hD_explicit_op
  have hcore :=
    chsh_to_pGuess_bound (E := E) ρXEd σXEd ε
      (by simpa [σXEd] using hIdeal) hD_explicit
  simpa [ρXEd, ρXE] using hcore


example
    {E : Type}
    [CpxFiniteHilbert E]
    (ρABE : DensityOperator (ABESystem E))
    (ε : Real) (hε' : ε ≤ 2 * Real.sqrt 2 - 2)
    (hCHSH :
      (2 * Real.sqrt 2 - ε)
        ≤ Complex.re
            (trace
              (canonicalCHSH ∘ₗ
                ((ρAB ρABE : DensityOperator ABSystem) : Operator ABSystem)))) :
    minEntropy (E := E)
        (pGuess (rhoXE_from_ABE (E := E) (ρABE : Operator (ABESystem E))))
      ≥ 1
          - 2
              * (Real.sqrt (ε / (2 * Real.sqrt 2)) + ε / (2 * Real.sqrt 2))
              / Real.log 2 := by
      let p := pGuess (rhoXE_from_ABE (E := E) (ρABE : Operator (ABESystem E)))
      let δ := Real.sqrt (ε / (2 * Real.sqrt 2)) + ε / (2 * Real.sqrt 2)
      let ρXEd : DensityOperator (Qubit ⊗[ℂ] E) := rhoXE_from_ABE_density (E := E) ρABE
      have pBound : p ≤ (1 / 2 : Real) + δ := by
        dsimp [p, δ]
        linarith [chsh_to_pGuess_bound_of_measure_contract_and_gentle ρABE ε hε' hCHSH]
      have hp_geq_half : (1 / 2 : Real) ≤ p := by
        simpa [p, ρXEd] using (pGuess_density_ge_half_fin2 (E := E) ρXEd)
      have hδ_nonneg : (0 : Real) ≤ δ := by
        linarith
      change minEntropy p ≥ 1 - 2 * δ / Real.log 2
      dsimp [minEntropy]
      have : Real.logb 2 p = Real.log p / Real.log 2 := by rfl
      rw [this]
      suffices h :
        Real.log p / Real.log 2 ≤ -1 + 2 * δ / Real.log 2 by
        linarith
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hhalfδ_pos : (0 : Real) < 1 / 2 + δ := by linarith
      have hp_pos : (0 : Real) < p := by linarith
      have h1plus2δ_pos : (0 : Real) < 1 + 2 * δ := by linarith
      have hmain : Real.log (1 + 2 * δ) ≤ 2 * δ := by
        linarith [Real.log_le_sub_one_of_pos h1plus2δ_pos]
      have hlogmul : Real.log (1 / 2 + δ) + Real.log 2 = Real.log (1 + 2 * δ) := by
        rw [← Real.log_mul (by linarith) (by norm_num : (2 : Real) ≠ 0)]
        ring_nf
      have hp_log : Real.log p ≤ Real.log (1 / 2 + δ) := by
        exact Real.log_le_log hp_pos pBound
      have h : Real.log p ≤ 2 * δ - Real.log 2 := by
        linarith
      rw [_root_.div_le_iff₀ hlog2_pos]
      have hmul :
          (-1 + 2 * δ / Real.log 2) * Real.log 2 = 2 * δ - Real.log 2 := by
        field_simp [hlog2_pos.ne']
        ring
      simpa [hmul] using h




end Entropy_Bound
