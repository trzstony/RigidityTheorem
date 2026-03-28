import Approximate_Rigidity.SpectralArgument
import Quantum.Bell

namespace Approximate_Rigidity
open Quantum
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators



variable {H_A H_B : Type*}
variable [NormedAddCommGroup H_A] [NormedAddCommGroup H_B]
variable [InnerProductSpace ℂ H_A] [InnerProductSpace ℂ H_B]
variable (Ψ : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B))
variable (delta : Real)


section JunkState

/-- The `0`-th Bell component in the decomposition of `Ψ`. -/
noncomputable def junkComponent
    (Ψ : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B)) : (H_A ⊗[ℂ] H_B) :=
  bellDecomposition (J := (H_A ⊗[ℂ] H_B)) Ψ 0

/-- The normalized `0`-th Bell component; returns `0` if the component is `0`. -/
noncomputable def junkState
    (Ψ : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B)) : (H_A ⊗[ℂ] H_B) :=
  ((‖junkComponent (H_A := H_A) (H_B := H_B) Ψ‖ : ℂ)⁻¹) •
    (junkComponent (H_A := H_A) (H_B := H_B) Ψ)

example (x y u v : (H_A ⊗[ℂ] H_B)) : ⟪x ⊗ₜ[ℂ] y, u ⊗ₜ[ℂ] v⟫_ℂ = ⟪x, u⟫_ℂ * ⟪y, v⟫_ℂ := by
  simp only [TensorProduct.inner_tmul]

example (a b c : ℝ) (hab : a ≤ b) : a + c ≤ b + c := by
  linarith

/-!
### Expanding the CHSH expectation in the Bell decomposition

Since `K` is diagonal in the Bell basis with eigenvalues `2√2, 0, 0, -2√2`,
expanding `Ψ` along that basis gives a closed form for `⟪Ψ, (K ⊗ I) Ψ⟫`.
-/

theorem inner_K_tensor_id_eq_bellDecomposition
    (Ψ : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B)) :
    ⟪Ψ, ((K ⊗ₗ (LinearMap.id)) Ψ)⟫_ℂ =
      2 * Real.sqrt 2 * (‖bellDecomposition Ψ 0‖ ^ 2 - ‖bellDecomposition Ψ 3‖ ^ 2) := by
  classical
  -- Expand `Ψ` in the Bell basis.
  let η : Fin 4 → (H_A ⊗[ℂ] H_B) := bellDecomposition (J := (H_A ⊗[ℂ] H_B)) Ψ
  have hΨ : Ψ = ∑ i : Fin 4, (bellBasis i) ⊗ₜ[ℂ] (η i) := by
    simpa [η] using
      (sum_bellBasis_tmul_bellDecomposition (J := (H_A ⊗[ℂ] H_B)) Ψ).symm
  -- `K` acts diagonally on the Bell basis.
  let eig : Fin 4 → ℂ
    | 0 => (2 * Real.sqrt 2 : ℂ)
    | 1 => 0
    | 2 => 0
    | 3 => (-2 * Real.sqrt 2 : ℂ)
  have happlyK : ∀ i : Fin 4, K (bellBasis i) = eig i • bellBasis i := by
    intro i
    fin_cases i
    · simp [eig, bellBasis_apply, bellVec, K_Φ_plus]
    · simp [eig, bellBasis_apply, bellVec, K_Φ_minus]
    · simp [eig, bellBasis_apply, bellVec, K_Ψ_plus]
    · simp [eig, bellBasis_apply, bellVec, K_Ψ_minus]
  -- Compute the expectation by bilinearity + orthonormality (only diagonal terms survive).
  have hexpand :
      ⟪Ψ, ((K ⊗ₗ (LinearMap.id)) Ψ)⟫_ℂ
        = ∑ i : Fin 4, (eig i) * (‖η i‖ ^ 2) := by
    let s : Finset (Fin 4) := Finset.univ
    let f : Fin 4 → (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B) :=
      fun i => (bellBasis i) ⊗ₜ[ℂ] (η i)
    let g : Fin 4 → (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B) :=
      fun i => (K (bellBasis i)) ⊗ₜ[ℂ] (η i)
    have hg : g = fun i => eig i • (f i) := by
      funext i
      simp only [g, f, happlyK i, TensorProduct.smul_tmul']
    have hmap :
        ((K ⊗ₗ (LinearMap.id)) (∑ i : Fin 4, f i))
          = ∑ i : Fin 4, g i := by
      simp [f, g]
    calc
      ⟪Ψ, ((K ⊗ₗ (LinearMap.id)) Ψ)⟫_ℂ
          = ⟪(∑ i : Fin 4, f i),
              ((K ⊗ₗ (LinearMap.id)) (∑ i : Fin 4, f i))⟫_ℂ := by
              simp [hΨ, f]
      _ = ⟪(∑ i : Fin 4, f i), (∑ j : Fin 4, g j)⟫_ℂ := by
            simp [hmap]
      _ = ⟪(∑ i : Fin 4, f i), (∑ j : Fin 4, eig j • (f j))⟫_ℂ := by
            simp only [hg]
      _ = ∑ i ∈ s, ∑ j ∈ s, (eig j) * ⟪f i, f j⟫_ℂ := by
            rw [sum_inner (𝕜 := ℂ) (s := s) (f := f) (x := ∑ j ∈ s, eig j • (f j))]
            -- Expand the inner product against a sum in the right slot, then pull out scalars.
            refine Finset.sum_congr rfl ?_
            intro i hi
            calc
              ⟪f i, ∑ x ∈ s, eig x • f x⟫_ℂ = ∑ x ∈ s, ⟪f i, eig x • f x⟫_ℂ := by
                simpa using
                  (inner_sum (𝕜 := ℂ) (s := s) (f := fun x => eig x • f x) (x := f i))
              _ = ∑ x ∈ s, eig x * ⟪f i, f x⟫_ℂ := by
                refine Finset.sum_congr rfl ?_
                intro x hx
                simpa using
                  (inner_smul_right (𝕜 := ℂ) (x := f i) (y := f x) (r := eig x))
      _ = ∑ i ∈ s, ∑ j ∈ s, (eig j) * (⟪bellBasis i, bellBasis j⟫_ℂ * ⟪η i, η j⟫_ℂ) := by
            simp only [f, TensorProduct.inner_tmul]
      _ = ∑ i ∈ s, ∑ j ∈ s, (eig j) * ((if i = j then 1 else 0) * ⟪η i, η j⟫_ℂ) := by
            simp_rw [orthonormal_iff_ite.mp bellBasis_orthonormal]
      _ = ∑ i : Fin 4, (eig i) * ⟪η i, η i⟫_ℂ := by
            classical
            -- Only diagonal terms survive.
            simp [s, ite_mul, mul_ite]
      _ = ∑ i : Fin 4, (eig i) * (‖η i‖ ^ 2) := by
            classical
            -- Rewrite each `⟪η i, η i⟫` as `(‖η i‖ : ℂ)^2`.
            refine Fintype.sum_congr _ _ ?_
            intro i
            exact
              congrArg (fun z : ℂ => (eig i) * z)
                (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (η i))
  -- Evaluate the finite sum: only indices `0` and `3` contribute.
  -- Then rewrite `η` back to `bellDecomposition Ψ`.
  -- (The remaining algebra is a straightforward simplification.)
  simp [η, eig, Fin.sum_univ_four, hexpand, sub_eq_add_neg, mul_add, add_mul,
  mul_left_comm, mul_comm]

example (u v : (H_A ⊗[ℂ] H_B)) : ‖u ⊗ₜ[ℂ] v‖ = ‖u‖ * ‖v‖ := by
  simp only [TensorProduct.norm_tmul]

example (u : (H_A ⊗[ℂ] H_B)) (h : ‖u‖ ≤ 1) : ‖u‖ ^ 2 ≤ 1 := by
  nlinarith [norm_nonneg u]

example (a b : ℝ) (hab : a ≤ b) : Real.sqrt a ≤ Real.sqrt b := by
  exact Real.sqrt_le_sqrt (by simp only [hab])


private lemma proj_estimate (hΨ : ‖Ψ‖ = 1) :
    ‖Ψ - bellState ⊗ₜ[ℂ] junkState (H_A := H_A) (H_B := H_B) (Ψ := Ψ)‖
      ≤ Real.sqrt (2 *
          (1 - ‖bellDecomposition (J := (H_A ⊗[ℂ] H_B)) Ψ 0‖ ^ 2)) := by
  classical
  set η : Fin 4 → (H_A ⊗[ℂ] H_B) := bellDecomposition (J := (H_A ⊗[ℂ] H_B)) Ψ
  have hηsum : (∑ i : Fin 4, ‖η i‖ ^ 2) = 1 := by
    simpa [η] using
      (decomposition_probs_sum_eq_one (J := (H_A ⊗[ℂ] H_B)) (Ψ := Ψ) hΨ)
  have hη0_le_one : ‖η 0‖ ≤ (1 : ℝ) := by
    have h0sq : ‖η 0‖ ^ 2 ≤ (1 : ℝ) := by
      have : ‖η 0‖ ^ 2 ≤ ∑ i : Fin 4, ‖η i‖ ^ 2 := by
        simpa using
          (Finset.single_le_sum (s := (Finset.univ : Finset (Fin 4)))
            (f := fun i => ‖η i‖ ^ 2)
            (by intro i hi; nlinarith [norm_nonneg (η i)]) (by simp))
      simpa [hηsum] using this
    nlinarith [h0sq, norm_nonneg (η 0)]
  have hinner :
      ⟪Ψ, bellState ⊗ₜ[ℂ] junkState (H_A := H_A) (H_B := H_B) (Ψ := Ψ)⟫_ℂ =
        (‖η 0‖ : ℂ) := by
    set x : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B) :=
      bellState ⊗ₜ[ℂ] junkState (H_A := H_A) (H_B := H_B) (Ψ := Ψ)
    have hdecomp : Ψ = ∑ i : Fin 4, (bellBasis i) ⊗ₜ[ℂ] η i := by
      simpa [η] using
        (sum_bellBasis_tmul_bellDecomposition (J := (H_A ⊗[ℂ] H_B)) Ψ).symm
    have hjunk :
        ⟪η 0, junkState (H_A := H_A) (H_B := H_B) (Ψ := Ψ)⟫_ℂ = (‖η 0‖ : ℂ) := by
      by_cases h0 : ‖η 0‖ = 0
      · simp [junkState, junkComponent, η, h0]
      · have h0c : (‖η 0‖ : ℂ) ≠ 0 := by exact_mod_cast h0
        calc
          ⟪η 0, junkState (H_A := H_A) (H_B := H_B) (Ψ := Ψ)⟫_ℂ
              = ((‖η 0‖ : ℂ)⁻¹) * ⟪η 0, η 0⟫_ℂ := by
                  simpa [junkState, junkComponent, η, -inner_self_eq_norm_sq_to_K] using
                    (inner_smul_right (𝕜 := ℂ) (x := η 0) (y := η 0) (r := ((‖η 0‖ : ℂ)⁻¹)))
          _ = ((‖η 0‖ : ℂ)⁻¹) * ((‖η 0‖ : ℂ) ^ 2) := by
                  exact congrArg (fun t : ℂ => ((‖η 0‖ : ℂ)⁻¹) * t)
                    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (η 0))
          _ = (‖η 0‖ : ℂ) := by
                  simpa [pow_two] using (inv_mul_cancel_left₀ h0c (b := (‖η 0‖ : ℂ)))
    calc
      ⟪Ψ, x⟫_ℂ = ∑ i : Fin 4, ⟪(bellBasis i) ⊗ₜ[ℂ] η i, x⟫_ℂ := by
        simpa [hdecomp] using
          (sum_inner (𝕜 := ℂ) (s := (Finset.univ : Finset (Fin 4)))
            (f := fun i => (bellBasis i) ⊗ₜ[ℂ] η i) (x := x))
      _ = ⟪η 0, junkState (H_A := H_A) (H_B := H_B) (Ψ := Ψ)⟫_ℂ := by
        simp [Fin.sum_univ_four, x, bellState, TensorProduct.inner_tmul (𝕜 := ℂ),
          bellBasis_apply, bellVec, -inner_self_eq_norm_sq_to_K]
      _ = (‖η 0‖ : ℂ) := hjunk
  have hinner_re :
      (⟪Ψ, bellState ⊗ₜ[ℂ] junkState (H_A := H_A) (H_B := H_B) (Ψ := Ψ)⟫_ℂ).re = ‖η 0‖ := by
    simpa using congrArg Complex.re hinner
  have hjunk :
      ‖junkState (H_A := H_A) (H_B := H_B) (Ψ := Ψ)‖ ≤ (1 : ℝ) := by
    by_cases hx : η 0 = 0
    · simp [junkState, junkComponent, η, hx]
    · have hx' : ‖η 0‖ ≠ 0 := by simpa [norm_eq_zero] using hx
      have : ‖junkState (H_A := H_A) (H_B := H_B) (Ψ := Ψ)‖ = (1 : ℝ) := by
        calc
          ‖junkState (H_A := H_A) (H_B := H_B) (Ψ := Ψ)‖
              = ‖((‖η 0‖ : ℂ)⁻¹) • η 0‖ := by simp [junkState, junkComponent, η]
          _ = ‖((‖η 0‖ : ℂ)⁻¹)‖ * ‖η 0‖ := by simp [norm_smul]
          _ = (‖η 0‖)⁻¹ * ‖η 0‖ := by
                simp [norm_inv]
          _ = 1 := by simp [hx']
      simp [this]
  have hproj :
      ‖Ψ - bellState ⊗ₜ[ℂ] junkState (H_A := H_A) (H_B := H_B) (Ψ := Ψ)‖
        ≤ Real.sqrt (2 * (1 - ‖η 0‖ ^ 2)) := by
    set y : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B) :=
      bellState ⊗ₜ[ℂ] junkState (H_A := H_A) (H_B := H_B) (Ψ := Ψ)
    have hy : ‖y‖ ≤ (1 : ℝ) := by
      simpa [y, TensorProduct.norm_tmul, bellState, Φ_plus_norm] using hjunk
    have hy2 : ‖y‖ ^ 2 ≤ (1 : ℝ) := by
      nlinarith [hy, norm_nonneg y]
    have hinner_re' : RCLike.re ⟪Ψ, y⟫_ℂ = ‖η 0‖ := by
      simpa using hinner_re
    have ha0 : 0 ≤ ‖η 0‖ := norm_nonneg _
    have hsq0 : ‖Ψ - y‖ ^ 2 ≤ 2 - 2 * ‖η 0‖ := by
      have hsub := norm_sub_sq (𝕜 := ℂ) Ψ y
      have hΨ2 : ‖Ψ‖ ^ 2 = (1 : ℝ) := by simp [hΨ]
      nlinarith [hsub, hΨ2, hinner_re', hy2]
    have hsq : ‖Ψ - y‖ ^ 2 ≤ 2 * (1 - ‖η 0‖ ^ 2) := by
      have hmono : 2 - 2 * ‖η 0‖ ≤ 2 * (1 - ‖η 0‖ ^ 2) := by
        nlinarith [ha0, hη0_le_one]
      exact le_trans hsq0 hmono
    have hnonneg : 0 ≤ 2 * (1 - ‖η 0‖ ^ 2) := by
      nlinarith [ha0, hη0_le_one]
    -- Convert the squared bound to the desired bound via monotonicity of `Real.sqrt`.
    have : ‖Ψ - y‖ ≤ Real.sqrt (2 * (1 - ‖η 0‖ ^ 2)) :=
      (Real.le_sqrt (norm_nonneg _) hnonneg).2 hsq
    simpa [y] using this
  simpa [η] using hproj

private lemma spectral_sqrt_bound
    (hExp :
      (⟪Ψ, ((K ⊗ₗ (LinearMap.id)) Ψ)⟫_ℂ).re
        ≥ 2 * Real.sqrt 2 - delta) :
    Real.sqrt (2 * (1 - ‖bellDecomposition (J := (H_A ⊗[ℂ] H_B)) Ψ 0‖ ^ 2))
      ≤ Real.sqrt (delta / Real.sqrt 2) := by
  classical
  set η : Fin 4 → (H_A ⊗[ℂ] H_B) := bellDecomposition (J := (H_A ⊗[ℂ] H_B)) Ψ
  have hre :
      (⟪Ψ, ((K ⊗ₗ (LinearMap.id)) Ψ)⟫_ℂ).re
        = 2 * Real.sqrt 2 * (‖η 0‖ ^ 2 - ‖η 3‖ ^ 2) := by
    have hEq :=
      congrArg Complex.re
        (inner_K_tensor_id_eq_bellDecomposition (H_A := H_A) (H_B := H_B) Ψ)
    have hc : (2 : ℂ) * (Real.sqrt 2 : ℂ) = ((2 * Real.sqrt 2 : ℝ) : ℂ) := by
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
    have hpow : ∀ r : ℝ, ((r : ℂ) ^ 2).re = r ^ 2 := by
      intro r
      have : (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) := by
        simp only [Complex.ofReal_pow]
      rw [this]
      rfl
    have hEq' :
        (⟪Ψ, ((K ⊗ₗ (LinearMap.id)) Ψ)⟫_ℂ).re
          = (((2 : ℂ) * (Real.sqrt 2 : ℂ)) *
              ((‖η 0‖ : ℂ) ^ 2 - (‖η 3‖ : ℂ) ^ 2)).re := by
      simpa [η, mul_assoc] using hEq
    have hEq'' :
        (⟪Ψ, ((K ⊗ₗ (LinearMap.id)) Ψ)⟫_ℂ).re
          = (((2 * Real.sqrt 2 : ℝ) : ℂ) *
              ((‖η 0‖ : ℂ) ^ 2 - (‖η 3‖ : ℂ) ^ 2)).re := by
      have h := hEq'
      rw [hc] at h
      simpa using h
    simpa [Complex.mul_re, Complex.sub_re, hpow] using hEq''
  have hpos : 0 < (2 * Real.sqrt 2) :=
    by nlinarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < (2 : ℝ))]
  have hn3 : 0 ≤ ‖η 3‖ ^ 2 := by nlinarith
  have hp0 : (1 - ‖η 0‖ ^ 2) ≤ delta / (2 * Real.sqrt 2) := by
    have : (1 - ‖η 0‖ ^ 2) * (2 * Real.sqrt 2) ≤ delta := by
      nlinarith [hre, hExp]
    exact (le_div_iff₀ hpos).2 this
  have hsqrt :
      Real.sqrt (2 * (1 - ‖η 0‖ ^ 2)) ≤ Real.sqrt (delta / Real.sqrt 2) := by
    apply Real.sqrt_le_sqrt
    have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    rw [le_div_iff₀ hsqrt2_pos]
    nlinarith [(le_div_iff₀ hpos).mp hp0]
  simpa [η] using hsqrt

theorem state_extraction_bound
    (hΨ : ‖Ψ‖ = 1)
    (hExp :
      (⟪Ψ, ((K ⊗ₗ (LinearMap.id)) Ψ)⟫_ℂ).re
        ≥ 2 * Real.sqrt 2 - delta) :
      ‖Ψ - bellState ⊗ₜ[ℂ] junkState (Ψ := Ψ)‖
        ≤ Real.sqrt (delta / Real.sqrt 2) := by
  simpa using le_trans (proj_estimate (H_A := H_A) (H_B := H_B) (Ψ := Ψ) hΨ)
    (spectral_sqrt_bound (H_A := H_A) (H_B := H_B) (Ψ := Ψ) (delta := delta) hExp)


end JunkState

end Approximate_Rigidity
