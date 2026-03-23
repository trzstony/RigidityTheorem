import Quantum.Bell
import Approximate_Rigidity.Isometries
import Approximate_Rigidity.IsometriesApprox

open scoped TensorProduct InnerProductSpace ComplexConjugate
open Quantum

namespace Approximate_Rigidity

-- The bookkeeping proof in this file expands large tensor expressions; we scope extra heartbeats
-- to the main theorem to avoid unscoped `set_option` lint.

/-!
Link between the physical CHSH value `chshBias S` and the spectral argument for the
two-qubit operator `K`.

This file is the formal counterpart of the “term-by-term estimate / bookkeeping” step
in `theorem11_1_proof_modified.md` (and Section 11.4 of the QIC 890 notes around
Eqs. (217)–(221)).

The goal is to produce a reusable lemma that turns:
- a lower bound on `chshBias S`, and
- approximate operator-extraction (vector-action) bounds,

into a lower bound on the extracted expectation `(⟪Ψ, (K ⊗ I) Ψ⟫).re`,
which is then fed into `SpectralArgument.state_extraction_bound`.
-/

/-! ### Error function used by the spectral argument -/

noncomputable def delta (epsilon : Real) : Real :=
  epsilon + 4 * Real.sqrt (cConst * epsilon)

lemma delta_nonneg (epsilon : Real) (hε : 0 ≤ epsilon) : 0 ≤ delta epsilon := by
  simp only [delta]
  nlinarith [Real.sqrt_nonneg (cConst * epsilon)]

/-! ### Generic analytic lemmas (Cauchy–Schwarz bookkeeping) -/

section Analytic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma re_inner_ge_sub_norm (x y z : E) (hx : ‖x‖ = 1) :
    (⟪x, y⟫_ℂ).re ≥ (⟪x, z⟫_ℂ).re - ‖y - z‖ := by
  -- `re ⟪x,y⟫ - re ⟪x,z⟫ = re ⟪x, y - z⟫` and `|re w| ≤ ‖w‖ ≤ ‖x‖‖y-z‖`.
  have hsub : ⟪x, y - z⟫_ℂ = ⟪x, y⟫_ℂ - ⟪x, z⟫_ℂ := by
    simpa using (inner_sub_right (𝕜 := ℂ) x y z)
  have hre' : (⟪x, y - z⟫_ℂ).re = (⟪x, y⟫_ℂ).re - (⟪x, z⟫_ℂ).re := by
    -- Take real parts of `hsub`.
    simp [hsub]
  have hre :
      (⟪x, y⟫_ℂ).re - (⟪x, z⟫_ℂ).re = (⟪x, y - z⟫_ℂ).re := by
    linarith [hre']
  have hneg : -(‖⟪x, y - z⟫_ℂ‖) ≤ (⟪x, y - z⟫_ℂ).re := by
    have habs : |(⟪x, y - z⟫_ℂ).re| ≤ ‖⟪x, y - z⟫_ℂ‖ := by
      simpa using (RCLike.abs_re_le_norm (⟪x, y - z⟫_ℂ))
    exact (abs_le.mp habs).1
  have hcs : ‖⟪x, y - z⟫_ℂ‖ ≤ ‖x‖ * ‖y - z‖ :=
    norm_inner_le_norm (𝕜 := ℂ) x (y - z)
  have hx' : ‖x‖ = 1 := hx
  have hbound : (⟪x, y - z⟫_ℂ).re ≥ -(‖y - z‖) := by
    -- Combine the two bounds, using `‖x‖ = 1`.
    have : -(‖x‖ * ‖y - z‖) ≤ (⟪x, y - z⟫_ℂ).re := by
      exact le_trans (neg_le_neg hcs) hneg
    -- Now rewrite `‖x‖` as `1`.
    simpa [hx', one_mul] using this
  -- Finish by rearranging the inequality.
  have : (⟪x, y⟫_ℂ).re ≥ (⟪x, z⟫_ℂ).re - ‖y - z‖ := by
    -- From `hre`: `re⟪x,y⟫ = re⟪x,z⟫ + re⟪x,y-z⟫`.
    have hre' : (⟪x, y⟫_ℂ).re = (⟪x, z⟫_ℂ).re + (⟪x, y - z⟫_ℂ).re := by
      linarith [hre]
    linarith [hre', hbound]
  exact this

lemma re_inner_le_add_norm (x y z : E) (hx : ‖x‖ = 1) :
    (⟪x, y⟫_ℂ).re ≤ (⟪x, z⟫_ℂ).re + ‖y - z‖ := by
  -- Apply the previous lemma to `-y` and `-z`.
  have := re_inner_ge_sub_norm (x := x) (y := z) (z := y) hx
  -- `this : re⟪x,z⟫ ≥ re⟪x,y⟫ - ‖z - y‖` -> rearrange.
  have hnorm : ‖z - y‖ = ‖y - z‖ := by simpa [sub_eq_add_neg, add_comm] using (norm_sub_rev z y)
  linarith [this, hnorm]

end Analytic


/-! ### Main CHSH→spectral link (to be proved using extraction bounds) -/

section Link

variable {H_A H_B : Type*}
variable [NormedAddCommGroup H_A] [NormedAddCommGroup H_B]
variable [InnerProductSpace ℂ H_A] [InnerProductSpace ℂ H_B]
variable [FiniteDimensional ℂ H_A] [FiniteDimensional ℂ H_B]
variable (S : CHSHStrategy H_A H_B)
variable (ε : Real)

lemma chshBias_eq_re_inner_regSwap_isometryV
    (S : CHSHStrategy H_A H_B) :
    let V_A : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) := VA (H := H_A) S.A0 S.A1
    let V_B : H_B →ₗ[ℂ] (Qubit ⊗[ℂ] H_B) := VB (H := H_B) S.B0 S.B1
    let Ψ : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B) := regSwap ((V_A ⊗ₗ V_B) S.psi)
    let CHSHphys :
        (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B) :=
      regSwap
        ((V_A ⊗ₗ V_B)
          ((CHSH_op (H_A := H_A) (H_B := H_B) S.A0 S.A1 S.B0 S.B1) S.psi))
    Complex.re (⟪Ψ, CHSHphys⟫_ℂ) = chshBias S := by
  classical
  dsimp
  set V_A : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) := VA (H := H_A) S.A0 S.A1 with hV_A
  set V_B : H_B →ₗ[ℂ] (Qubit ⊗[ℂ] H_B) := VB (H := H_B) S.B0 S.B1 with hV_B
  set Ψ : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B) :=
    regSwap ((V_A ⊗ₗ V_B) S.psi) with hΨ
  set CHSHphys :
      (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B) :=
    regSwap
      ((V_A ⊗ₗ V_B)
        ((CHSH_op (H_A := H_A) (H_B := H_B) S.A0 S.A1 S.B0 S.B1) S.psi)) with hCHSHphys
  have hVA : Isometry V_A := by
    simpa [hV_A] using
      (VA_is_isometry S.A0 S.A1)
  have hVB : Isometry V_B := by
    simpa [hV_B] using
      (VB_is_isometry S.B0 S.B1)
  let VAᵢ : H_A →ₗᵢ[ℂ] (Qubit ⊗[ℂ] H_A) :=
    { toLinearMap := V_A
      norm_map' := (AddMonoidHomClass.isometry_iff_norm V_A).1 hVA }
  let VBᵢ : H_B →ₗᵢ[ℂ] (Qubit ⊗[ℂ] H_B) :=
    { toLinearMap := V_B
      norm_map' := (AddMonoidHomClass.isometry_iff_norm V_B).1 hVB }
  have hVt_inner (u v : H_A ⊗[ℂ] H_B) :
      ⟪(V_A ⊗ₗ V_B) u, (V_A ⊗ₗ V_B) v⟫_ℂ = ⟪u, v⟫_ℂ := by
    simpa [VAᵢ, VBᵢ] using (TensorProduct.inner_map_map (𝕜 := ℂ) VAᵢ VBᵢ u v)
  have hinner :
      ⟪Ψ, CHSHphys⟫_ℂ =
        ⟪S.psi,
            (CHSH_op (H_A := H_A) (H_B := H_B) S.A0 S.A1 S.B0 S.B1) S.psi⟫_ℂ := by
    calc
      ⟪Ψ, CHSHphys⟫_ℂ
          =
            ⟪regSwap ((V_A ⊗ₗ V_B) S.psi),
              regSwap
                ((V_A ⊗ₗ V_B)
                  ((CHSH_op (H_A := H_A) (H_B := H_B) S.A0 S.A1 S.B0 S.B1) S.psi))⟫_ℂ := by
              simp [hΨ, hCHSHphys]
      _ =
            ⟪(V_A ⊗ₗ V_B) S.psi,
              (V_A ⊗ₗ V_B)
                ((CHSH_op (H_A := H_A) (H_B := H_B) S.A0 S.A1 S.B0 S.B1) S.psi)⟫_ℂ := by
              simpa using
                (regSwap_inner (H_A := H_A) (H_B := H_B)
                  ((V_A ⊗ₗ V_B) S.psi)
                  ((V_A ⊗ₗ V_B)
                    ((CHSH_op (H_A := H_A) (H_B := H_B) S.A0 S.A1 S.B0 S.B1) S.psi)))
      _ =
            ⟪S.psi,
              (CHSH_op (H_A := H_A) (H_B := H_B) S.A0 S.A1 S.B0 S.B1) S.psi⟫_ℂ := by
              simpa using
                (hVt_inner S.psi
                  ((CHSH_op (H_A := H_A) (H_B := H_B) S.A0 S.A1 S.B0 S.B1) S.psi))
  simp [chshBias, hinner]

section LinkHelpers

variable {H_A H_B : Type*}
variable [NormedAddCommGroup H_A] [NormedAddCommGroup H_B]
variable [InnerProductSpace ℂ H_A] [InnerProductSpace ℂ H_B]
-- variable [FiniteDimensional ℂ H_A] [FiniteDimensional ℂ H_B]
variable (S : CHSHStrategy H_A H_B)

private lemma extracted_state_norm_one
    (V_A : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A))
    (V_B : H_B →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))
    (hVA : Isometry V_A) (hVB : Isometry V_B) :
    ‖regSwap (H_A := H_A) (H_B := H_B) ((V_A ⊗ₗ V_B) S.psi)‖ = 1 := by
  simpa using
    (regSwap_map_norm_eq_one (H_A := H_A) (H_B := H_B)
      (V_A := V_A) (V_B := V_B) hVA hVB (ψ := S.psi) S.psi_norm)

private lemma ideal_CHSH_action_eq_K
    (idJ : (H_A ⊗[ℂ] H_B) →ₗ[ℂ] (H_A ⊗[ℂ] H_B))
    (Ψ : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B)) :
    (((CHSH_op (H_A := Qubit) (H_B := Qubit) pauliZ pauliX Hadamard pauliZHZ) ⊗ₗ idJ) Ψ)
      = ((K ⊗ₗ idJ) Ψ) := by
  simp [K_as_CHSH, canonicalCHSH, CHSH_op]

private lemma re_inner_ge_sub_norm_of_diff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y z : E) (err : Real)
    (hx : ‖x‖ = 1) (hdiff : ‖y - z‖ ≤ err) :
    (⟪x, y⟫_ℂ).re ≥ (⟪x, z⟫_ℂ).re - err := by
  have h := re_inner_ge_sub_norm (x := x) (y := y) (z := z) hx
  linarith [h, hdiff]

private lemma regSwap_qubit_naturality
    (fA fB : Qubit →ₗ[ℂ] Qubit) :
    (((fA ⊗ₗ fB) ⊗ₗ
        (LinearMap.id : (H_A ⊗[ℂ] H_B) →ₗ[ℂ] (H_A ⊗[ℂ] H_B))) ∘ₗ
      regSwap (H_A := H_A) (H_B := H_B))
      =
    (regSwap (H_A := H_A) (H_B := H_B) ∘ₗ
      (((fA ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
          (fB ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))) :
        ((Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B)) →ₗ[ℂ]
          ((Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B)))) := by
  ext q a q' b
  simp [regSwap]

private lemma regSwap_dist_eq
    (x y : (Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B)) :
    ‖regSwap (H_A := H_A) (H_B := H_B) x
        - regSwap (H_A := H_A) (H_B := H_B) y‖ = ‖x - y‖ := by
  simpa [LinearMap.map_sub] using
    (regSwap_norm (H_A := H_A) (H_B := H_B) (ψ := x - y))

private lemma Hadamard_is_isometry : Isometry (Hadamard : Qubit →ₗ[ℂ] Qubit) := by
  simpa using
    (isometry_of_adjoint_eq_self_and_sq_one
      (H := Qubit) (A := (Hadamard : Qubit →ₗ[ℂ] Qubit))
      Hadamard_adjoint Hadamard_sq)

private lemma four_term_norm_sub_le
    {E : Type*} [NormedAddCommGroup E]
    (a b c d : E) :
    ‖a + b + c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have hcd : ‖c - d‖ ≤ ‖c‖ + ‖d‖ := by
    calc
      ‖c - d‖ = ‖c + (-d)‖ := by simp [sub_eq_add_neg]
      _ ≤ ‖c‖ + ‖-d‖ := norm_add_le c (-d)
      _ = ‖c‖ + ‖d‖ := by simp
  calc
    ‖a + b + c - d‖ = ‖(a + b) + (c - d)‖ := by abel_nf
    _ ≤ ‖a + b‖ + ‖c - d‖ := norm_add_le (a + b) (c - d)
    _ ≤ (‖a‖ + ‖b‖) + (‖c‖ + ‖d‖) := add_le_add (norm_add_le a b) hcd
    _ = ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by ring

private lemma norm_le_sqrt_of_sq_le
    {E : Type*} [NormedAddCommGroup E] (x : E) {r : Real}
    (h : ‖x‖ ^ 2 ≤ r) : ‖x‖ ≤ Real.sqrt r := by
  have hsqrt : Real.sqrt (‖x‖ ^ 2) ≤ Real.sqrt r := Real.sqrt_le_sqrt h
  have hx : Real.sqrt (‖x‖ ^ 2) = ‖x‖ := by
    simp [Real.sqrt_sq_eq_abs ‖x‖]
  simpa [hx] using hsqrt

private lemma norm_sub_le_two_mul_of_intermediate
    {E : Type*} [NormedAddCommGroup E]
    (a b c : E) (err0 : Real)
    (hab : ‖a - b‖ ≤ err0) (hbc : ‖b - c‖ ≤ err0) :
    ‖a - c‖ ≤ 2 * err0 := by
  have htri : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
    have hrew : a - c = (a - b) + (b - c) := by abel
    rw [hrew]
    exact norm_add_le (a - b) (b - c)
  calc
    ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := htri
    _ ≤ err0 + err0 := add_le_add hab hbc
    _ = 2 * err0 := (two_mul err0).symm

private lemma dist_le_of_transport
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F]
    (T : E →ₗ[ℂ] F) (hT : ∀ x, ‖T x‖ = ‖x‖)
    (x y : E) {r : Real} (hxy : ‖y - x‖ ≤ r) :
    ‖T x - T y‖ ≤ r := by
  have hxy' : ‖x - y‖ ≤ r := by simpa [norm_sub_rev] using hxy
  have hm : ‖T x - T y‖ = ‖T (x - y)‖ := by
    simp [LinearMap.map_sub T x y]
  rw [hm, hT (x - y)]
  exact hxy'

private lemma A1_extraction_on_B1_state
    (V_A : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A))
    (V_B : H_B →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))
    (ΔA1 : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A))
    (ψB1 : H_A ⊗[ℂ] H_B) (err0 : Real)
    (hψB1 : ψB1 = ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B1) S.psi)
    (hΔdef : ΔA1 = ((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ∘ₗ V_A) - (V_A ∘ₗ S.A1))
    (hΔnorm : ‖((ΔA1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi)‖ ≤ err0)
    (hVB_iso : Isometry V_B) :
    let V :
        (H_A ⊗[ℂ] H_B) →ₗ[ℂ] ((Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B)) :=
      (V_A ⊗ₗ V_B)
    let XA : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) :=
      (pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A))
    let idQB : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B) := LinearMap.id
    ‖V ((S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψB1) - (XA ⊗ₗ idQB) (V ψB1)‖ ≤ err0 := by
  classical
  dsimp
  have hB1_iso : Isometry S.B1 := isometry_of_isBinaryObservable (A := S.B1)
  have hnorm_id_B1 (x : (Qubit ⊗[ℂ] H_A) ⊗[ℂ] H_B) :
      ‖(((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ S.B1) x)‖ = ‖x‖ := by
    simpa using
      (tensor_map_norm_eq
        (f := (LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)))
        (g := S.B1)
        linearMap_id_isometry hB1_iso x)
  have hCommΔ :
      ((ΔA1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ∘ₗ
          ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B1))
        =
      ((((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ S.B1) ∘ₗ
          (ΔA1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)))) := by
    ext x y
    simp [LinearMap.comp_apply, TensorProduct.map_tmul]
  have hΔnorm_ψB1 :
      ‖((ΔA1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψB1)‖ ≤ err0 := by
    have happ := congrArg (fun F => F S.psi) hCommΔ
    have hEq :
        ((ΔA1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψB1)
          =
        (((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ S.B1)
          (((ΔA1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi))) := by
      simpa [hψB1, LinearMap.comp_apply] using happ
    have hEqNorm :
        ‖((ΔA1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψB1)‖
          =
        ‖((ΔA1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi)‖ := by
      calc
        ‖((ΔA1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψB1)‖
            =
          ‖(((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ S.B1)
            (((ΔA1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi)))‖ := by
              rw [hEq]
        _ = ‖((ΔA1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi)‖ := hnorm_id_B1 _
    rw [hEqNorm]
    exact hΔnorm
  have hnorm_id_VB (x : (Qubit ⊗[ℂ] H_A) ⊗[ℂ] H_B) :
      ‖(((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ V_B) x)‖ = ‖x‖ := by
    simpa using
      (tensor_map_norm_eq
        (f := (LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)))
        (g := V_B)
        linearMap_id_isometry hVB_iso x)
  have hCompDelta :
      (ΔA1 ⊗ₗ V_B)
        =
      ((((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ V_B) ∘ₗ
          (ΔA1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)))) := by
    ext x y
    simp [LinearMap.comp_apply, TensorProduct.map_tmul]
  have hNormTransport :
      ‖(ΔA1 ⊗ₗ V_B) ψB1‖ = ‖((ΔA1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψB1)‖ := by
    have happ := congrArg (fun F => F ψB1) hCompDelta
    calc
      ‖(ΔA1 ⊗ₗ V_B) ψB1‖
          =
        ‖(((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ V_B)
          (((ΔA1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψB1)))‖ := by
            simpa [LinearMap.comp_apply] using congrArg (fun z => ‖z‖) happ
      _ = ‖((ΔA1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψB1)‖ := hnorm_id_VB _
  let P : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) :=
    ((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ∘ₗ V_A)
  let Q : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) := (V_A ∘ₗ S.A1)
  have hDiff :
      ((V_A ⊗ₗ V_B) ((S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψB1))
        - (((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
            (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))) ((V_A ⊗ₗ V_B) ψB1))
        = -((ΔA1 ⊗ₗ V_B) ψB1) := by
    have hLeftMap :
        ((V_A ⊗ₗ V_B) ∘ₗ (S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))) = (Q ⊗ₗ V_B) := by
      ext x y
      simp [Q, LinearMap.comp_apply, TensorProduct.map_tmul]
    have hRightMap :
        (((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
              (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))) ∘ₗ
            (V_A ⊗ₗ V_B)) = (P ⊗ₗ V_B) := by
      ext x y
      simp [P, LinearMap.comp_apply, TensorProduct.map_tmul]
    have hLeft :
        (V_A ⊗ₗ V_B) ((S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψB1) = ((Q ⊗ₗ V_B) ψB1) := by
      simpa [LinearMap.comp_apply] using congrArg (fun F => F ψB1) hLeftMap
    have hRight :
        (((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
            (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))) ((V_A ⊗ₗ V_B) ψB1))
          = ((P ⊗ₗ V_B) ψB1) := by
      simpa [LinearMap.comp_apply] using congrArg (fun F => F ψB1) hRightMap
    have hΔapply : (ΔA1 ⊗ₗ V_B) ψB1 = ((P ⊗ₗ V_B) ψB1) - ((Q ⊗ₗ V_B) ψB1) := by
      have hmap_sub : (ΔA1 ⊗ₗ V_B) = (P ⊗ₗ V_B) - (Q ⊗ₗ V_B) := by
        ext x y
        simp [hΔdef, P, Q, sub_eq_add_neg, TensorProduct.map_tmul,
          TensorProduct.add_tmul, TensorProduct.neg_tmul]
      simp [hmap_sub]
    calc
      (V_A ⊗ₗ V_B) ((S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψB1)
          - (((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
              (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))) ((V_A ⊗ₗ V_B) ψB1))
          = ((Q ⊗ₗ V_B) ψB1) - ((P ⊗ₗ V_B) ψB1) := by
              rw [hLeft, hRight]
      _ = -(((P ⊗ₗ V_B) ψB1) - ((Q ⊗ₗ V_B) ψB1)) := by
            abel
      _ = -((ΔA1 ⊗ₗ V_B) ψB1) := by
            rw [hΔapply]
  calc
    ‖(V_A ⊗ₗ V_B) ((S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψB1)
        - (((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
            (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))) ((V_A ⊗ₗ V_B) ψB1))‖
        = ‖-((ΔA1 ⊗ₗ V_B) ψB1)‖ := by
            simp [hDiff]
    _ = ‖(ΔA1 ⊗ₗ V_B) ψB1‖ := by
          exact norm_neg ((ΔA1 ⊗ₗ V_B) ψB1)
    _ = ‖((ΔA1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψB1)‖ := hNormTransport
    _ ≤ err0 := hΔnorm_ψB1

end LinkHelpers

set_option maxHeartbeats 1200000 in
-- This proof does substantial tensor-product bookkeeping; increasing heartbeats avoids timeouts.
theorem chsh_to_K_expectation
    (hBias : chshBias S ≥ 2 * Real.sqrt 2 - ε) :
    let V_A : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) := VA (H := H_A) S.A0 S.A1
    let V_B : H_B →ₗ[ℂ] (Qubit ⊗[ℂ] H_B) := VB (H := H_B) S.B0 S.B1
    let Ψ : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B) := regSwap ((V_A ⊗ₗ V_B) S.psi)
    Complex.re
        (⟪Ψ, ((K ⊗ₗ (LinearMap.id : (H_A ⊗[ℂ] H_B) →ₗ[ℂ] (H_A ⊗[ℂ] H_B))) Ψ)⟫_ℂ)
      ≥ 2 * Real.sqrt 2 - delta ε := by
  classical
  dsimp
  set V_A : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) := VA (H := H_A) S.A0 S.A1 with hV_A
  set V_B : H_B →ₗ[ℂ] (Qubit ⊗[ℂ] H_B) := VB (H := H_B) S.B0 S.B1 with hV_B
  set Ψ : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B) :=
    regSwap ((V_A ⊗ₗ V_B) S.psi) with hΨ

  -- Local abbreviations.
  let idJ : (H_A ⊗[ℂ] H_B) →ₗ[ℂ] (H_A ⊗[ℂ] H_B) := LinearMap.id
  let err0 : Real := Real.sqrt (cConst * ε)
  let err : Real := 4 * err0

  -- The pushed CHSH-action vector on the extracted state.
  let CHSHphys :
      (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B) :=
    regSwap
      ((V_A ⊗ₗ V_B)
        ((CHSH_op (H_A := H_A) (H_B := H_B) S.A0 S.A1 S.B0 S.B1) S.psi))

  -- The ideal CHSH-action vector (which equals `(K ⊗ I) Ψ` after rewriting `K`).
  let CHSHideal :
      (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B) :=
    (((CHSH_op (H_A := Qubit) (H_B := Qubit) pauliZ pauliX Hadamard pauliZHZ) ⊗ₗ idJ) Ψ)

  -- Step 0: the pushed CHSH action has the same expectation as the original bias.
  have hCHSHphys_re :
      Complex.re (⟪Ψ, CHSHphys⟫_ℂ) = chshBias S := by
    simpa [hV_A, hV_B, hΨ, CHSHphys] using
      (chshBias_eq_re_inner_regSwap_isometryV (S := S))

  -- Step 1: rewrite `K` as the ideal CHSH operator on the two extracted qubits.
  have hCHSHideal_eq_K :
      CHSHideal = ((K ⊗ₗ idJ) Ψ) := by
    simpa [CHSHideal] using
      (ideal_CHSH_action_eq_K (idJ := idJ) (Ψ := Ψ))

  -- Step 2: decompose both action vectors term-by-term.
  -- Physical terms.
  let v00 :=
    regSwap ((V_A ⊗ₗ V_B) ((S.A0 ⊗ₗ S.B0) S.psi))
  let v01 :=
    regSwap ((V_A ⊗ₗ V_B) ((S.A0 ⊗ₗ S.B1) S.psi))
  let v10 :=
    regSwap ((V_A ⊗ₗ V_B) ((S.A1 ⊗ₗ S.B0) S.psi))
  let v11 :=
    regSwap ((V_A ⊗ₗ V_B) ((S.A1 ⊗ₗ S.B1) S.psi))
  -- Ideal terms.
  let w00 := (((pauliZ ⊗ₗ Hadamard) ⊗ₗ idJ) Ψ)
  let w01 := (((pauliZ ⊗ₗ pauliZHZ) ⊗ₗ idJ) Ψ)
  let w10 := (((pauliX ⊗ₗ Hadamard) ⊗ₗ idJ) Ψ)
  let w11 := (((pauliX ⊗ₗ pauliZHZ) ⊗ₗ idJ) Ψ)

  have hCHSHphys_decomp : CHSHphys = v00 + v01 + v10 - v11 := by
    -- Expand `CHSH_op` and use linearity of `regSwap` and `(V_A ⊗ₗ V_B)`.
    -- (In practice: `simp [CHSHphys, CHSH_op, v00, v01, v10, v11]`.)
    classical
    -- Avoid unfolding the (large) definition of `regSwap` by disabling `dsimp`.
    -- After expanding, `abel` handles reassociation/commutation of `+`.
    simp (config := { dsimp := false })
      [CHSHphys, CHSH_op, v00, v01, v10, v11, sub_eq_add_neg]

  have hCHSHideal_decomp : CHSHideal = w00 + w01 + w10 - w11 := by
    -- Expand `CHSH_op` and use linearity.
    -- (In practice: `simp [CHSHideal, CHSH_op, w00, w01, w10, w11]`.)
    classical
    -- Pure bookkeeping: expand and use linearity of `TensorProduct.map` and `LinearMap`.
    -- `abel_nf` cleans up reassociation/commutation of `+`.
    simp [CHSHideal, CHSH_op, w00, w01, w10, w11, sub_eq_add_neg,
      TensorProduct.map_add_left, LinearMap.add_apply]
    abel_nf
    -- Final `-` term bookkeeping: `⊗ₗ` is additive in the left map, so negation pushes through.
    have hneg_map :
        ((-pauliX ⊗ₗ pauliZHZ) ⊗ₗ idJ) =
          -((pauliX ⊗ₗ pauliZHZ) ⊗ₗ idJ) := by
      ext u v
      simp [TensorProduct.neg_tmul]
    simp [hneg_map, LinearMap.neg_apply]



  -- Step 3: extraction bounds, rewritten for our local names.
  let V :
      (H_A ⊗[ℂ] H_B) →ₗ[ℂ] ((Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B)) :=
    (V_A ⊗ₗ V_B)

  have hA0_map :
      (V ∘ₗ (S.A0 ⊗ₗ LinearMap.id)) =
        ((((pauliZ ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
              (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))) ∘ₗ V)) := by
    simpa [V, hV_A, hV_B, VA] using (eq217_A0 (S := S))

  have hB0_map :
      (V ∘ₗ ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B0)) =
        ((((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ
              (Hadamard ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))) ∘ₗ V)) := by
    simpa [V, hV_A, hV_B, VB] using (eq219_B0 (S := S))

  have hA1_approx :
      ‖(((V ∘ₗ (S.A1 ⊗ₗ LinearMap.id)) S.psi)
            - ((((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ⊗ₗ
                  (LinearMap.id : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B))) ∘ₗ V) S.psi))‖
        ≤ err0 := by
    simpa [V, hV_A, hV_B, VA, VB, err0] using
      (eq218_A1_approx (S := S) (epsilon := ε) hBias)

  have hB1_approx :
      ‖(((V ∘ₗ ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B1)) S.psi)
            - ((((LinearMap.id : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A)) ⊗ₗ
                  (pauliZHZ ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))) ∘ₗ V) S.psi))‖
        ≤ err0 := by
    simpa [V, hV_A, hV_B, VA, VB, err0] using
      (eq220_B1_approx (S := S) (epsilon := ε) hBias)

  -- Step 4: triangle inequality to bound the full CHSH-vector difference.
  have hdiff : ‖CHSHideal - CHSHphys‖ ≤ err := by
    classical
    have hIsoX : Isometry (pauliX : Qubit →ₗ[ℂ] Qubit) := PauliX_is_isometry
    have hIsoZ : Isometry (pauliZ : Qubit →ₗ[ℂ] Qubit) := PauliZ_is_isometry
    have hIsoH : Isometry (Hadamard : Qubit →ₗ[ℂ] Qubit) :=
      Hadamard_is_isometry

    -- Abbreviations in the un-swapped extracted space.
    let Ψ0 : (Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B) := V S.psi
    have hΨ0 : Ψ = regSwap (H_A := H_A) (H_B := H_B) Ψ0 := by
      simp [Ψ0, V, hΨ]

    let ZA : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) :=
      (pauliZ ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A))
    let XA : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) :=
      (pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A))
    let HB : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B) :=
      (Hadamard ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))
    let ZHZB : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B) :=
      (pauliZHZ ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))

    -- Isometries of the extracted-side maps and their tensorings with `id`.
    have hIso_ZA : Isometry ZA := by
      simpa [ZA] using
        (tensor_map_isometry (f := (pauliZ : Qubit →ₗ[ℂ] Qubit))
          (g := (LinearMap.id : H_A →ₗ[ℂ] H_A))
          hIsoZ linearMap_id_isometry)
    have hIso_XA : Isometry XA := by
      simpa [XA] using
        (tensor_map_isometry (f := (pauliX : Qubit →ₗ[ℂ] Qubit))
          (g := (LinearMap.id : H_A →ₗ[ℂ] H_A))
          hIsoX linearMap_id_isometry)
    have hIso_HB : Isometry HB := by
      simpa [HB] using
        (tensor_map_isometry (f := (Hadamard : Qubit →ₗ[ℂ] Qubit))
          (g := (LinearMap.id : H_B →ₗ[ℂ] H_B))
          hIsoH linearMap_id_isometry)

    -- Tensor with `id` on the other extracted subsystem.
    let idQA : (Qubit ⊗[ℂ] H_A) →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) := LinearMap.id
    let idQB : (Qubit ⊗[ℂ] H_B) →ₗ[ℂ] (Qubit ⊗[ℂ] H_B) := LinearMap.id

    -- Rewrite each ideal term `wxy` as `regSwap` applied to an un-swapped ideal action on `Ψ0`.
    have hw00 :
        w00 = regSwap (H_A := H_A) (H_B := H_B) (((ZA ⊗ₗ HB) : _ →ₗ[ℂ] _) Ψ0) := by
      have hNat := regSwap_qubit_naturality (H_A := H_A) (H_B := H_B)
        (fA := pauliZ) (fB := Hadamard)
      have hNat' := congrArg (fun F => F Ψ0) hNat
      simpa [w00, hΨ0, ZA, HB, idJ, LinearMap.comp_apply] using hNat'
    have hw01 :
        w01 = regSwap (H_A := H_A) (H_B := H_B) (((ZA ⊗ₗ ZHZB) : _ →ₗ[ℂ] _) Ψ0) := by
      have hNat := regSwap_qubit_naturality (H_A := H_A) (H_B := H_B)
        (fA := pauliZ) (fB := pauliZHZ)
      have hNat' := congrArg (fun F => F Ψ0) hNat
      simpa [w01, hΨ0, ZA, ZHZB, idJ, LinearMap.comp_apply] using hNat'
    have hw10 :
        w10 = regSwap (H_A := H_A) (H_B := H_B) (((XA ⊗ₗ HB) : _ →ₗ[ℂ] _) Ψ0) := by
      have hNat := regSwap_qubit_naturality (H_A := H_A) (H_B := H_B)
        (fA := pauliX) (fB := Hadamard)
      have hNat' := congrArg (fun F => F Ψ0) hNat
      simpa [w10, hΨ0, XA, HB, idJ, LinearMap.comp_apply] using hNat'
    have hw11 :
        w11 = regSwap (H_A := H_A) (H_B := H_B) (((XA ⊗ₗ ZHZB) : _ →ₗ[ℂ] _) Ψ0) := by
      have hNat := regSwap_qubit_naturality (H_A := H_A) (H_B := H_B)
        (fA := pauliX) (fB := pauliZHZ)
      have hNat' := congrArg (fun F => F Ψ0) hNat
      simpa [w11, hΨ0, XA, ZHZB, idJ, LinearMap.comp_apply] using hNat'

    -- Convenience wrappers for the extraction identities/inequalities on vectors.
    have hA0_app (φ : H_A ⊗[ℂ] H_B) :
        V ((S.A0 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) φ) = (ZA ⊗ₗ idQB) (V φ) := by
      have h := congrArg (fun F => F φ) hA0_map
      simpa [LinearMap.comp_apply, ZA, idQB] using h
    have hB0_app (φ : H_A ⊗[ℂ] H_B) :
        V (((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B0) φ) = (idQA ⊗ₗ HB) (V φ) := by
      have h := congrArg (fun F => F φ) hB0_map
      simpa [LinearMap.comp_apply, idQA, HB] using h

    have hA1_vec :
        ‖V ((S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi) - (XA ⊗ₗ idQB) (V S.psi)‖ ≤ err0 := by
      simpa [LinearMap.comp_apply, XA, idQB] using hA1_approx
    have hB1_vec :
        ‖V (((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B1) S.psi) - (idQA ⊗ₗ ZHZB) Ψ0‖ ≤ err0 := by
      simpa [LinearMap.comp_apply, idQA, ZHZB, Ψ0] using hB1_approx

    -- Useful norm preservation facts for isometries.
    have hnorm_ZA_id (x :
        (Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B)) :
        ‖(ZA ⊗ₗ idQB) x‖ = ‖x‖ :=
      tensor_map_norm_eq (f := ZA) (g := idQB) hIso_ZA linearMap_id_isometry x
    have hnorm_XA_id (x :
        (Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B)) :
        ‖(XA ⊗ₗ idQB) x‖ = ‖x‖ :=
      tensor_map_norm_eq (f := XA) (g := idQB) hIso_XA linearMap_id_isometry x
    have hnorm_id_HB (x :
        (Qubit ⊗[ℂ] H_A) ⊗[ℂ] (Qubit ⊗[ℂ] H_B)) :
        ‖(idQA ⊗ₗ HB) x‖ = ‖x‖ :=
      tensor_map_norm_eq (f := idQA) (g := HB) linearMap_id_isometry hIso_HB x

    -- Map decompositions on the extracted space.
    have hZA_HB :
        ((ZA ⊗ₗ idQB) ∘ₗ (idQA ⊗ₗ HB)) = (ZA ⊗ₗ HB) := by
      ext x y
      simp [ZA, HB, idQA, idQB, TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.id_apply]
    have hZA_ZHZB :
        ((ZA ⊗ₗ idQB) ∘ₗ (idQA ⊗ₗ ZHZB)) = (ZA ⊗ₗ ZHZB) := by
      ext x y
      simp [ZA, ZHZB, idQA, idQB, TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.id_apply]
    have hXA_HB :
        ((idQA ⊗ₗ HB) ∘ₗ (XA ⊗ₗ idQB)) = (XA ⊗ₗ HB) := by
      ext x y
      simp [XA, HB, idQA, idQB, TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.id_apply]
    have hXA_ZHZB :
        ((XA ⊗ₗ idQB) ∘ₗ (idQA ⊗ₗ ZHZB)) = (XA ⊗ₗ ZHZB) := by
      ext x y
      simp [XA, ZHZB, idQA, idQB, TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.id_apply]

    -- Bounds on the correlator action vectors in the un-swapped extracted space.
    have hu00_eq : V ((S.A0 ⊗ₗ S.B0) S.psi) = (ZA ⊗ₗ HB) Ψ0 := by
      have hAB :
          (S.A0 ⊗ₗ S.B0) =
            (S.A0 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ∘ₗ
              ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B0) := by
        ext x y
        simp [TensorProduct.map_tmul, LinearMap.comp_apply]
      calc
        V ((S.A0 ⊗ₗ S.B0) S.psi)
            = V ((S.A0 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))
                (((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B0) S.psi)) := by
                simp [hAB, LinearMap.comp_apply]
        _ = (ZA ⊗ₗ idQB) (V (((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B0) S.psi)) := by
              simpa using (hA0_app (φ := (((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B0) S.psi)))
        _ = (ZA ⊗ₗ idQB) ((idQA ⊗ₗ HB) (V S.psi)) := by
              simp [hB0_app]
        _ = (ZA ⊗ₗ HB) (V S.psi) := by
              simpa [LinearMap.comp_apply] using congrArg (fun F => F (V S.psi)) hZA_HB
        _ = (ZA ⊗ₗ HB) Ψ0 := by rfl

    have hu01 :
        ‖(ZA ⊗ₗ ZHZB) Ψ0 - V ((S.A0 ⊗ₗ S.B1) S.psi)‖ ≤ err0 := by
      have hAB :
          (S.A0 ⊗ₗ S.B1) =
            (S.A0 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ∘ₗ
              ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B1) := by
        ext x y
        simp [TensorProduct.map_tmul, LinearMap.comp_apply]
      let ψB1 : H_A ⊗[ℂ] H_B := ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B1) S.psi
      have hB1ψ :
          ‖V ψB1 - (idQA ⊗ₗ ZHZB) Ψ0‖ ≤ err0 := by
        simpa [ψB1] using hB1_vec
      have hideal : (ZA ⊗ₗ ZHZB) Ψ0 = (ZA ⊗ₗ idQB) ((idQA ⊗ₗ ZHZB) Ψ0) := by
        simpa [LinearMap.comp_apply] using congrArg (fun F => F Ψ0) hZA_ZHZB.symm
      have hphys :
          V ((S.A0 ⊗ₗ S.B1) S.psi) = (ZA ⊗ₗ idQB) (V ψB1) := by
        calc
          V ((S.A0 ⊗ₗ S.B1) S.psi)
              = V ((S.A0 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B))
                  ψB1) := by
                    simp [hAB, ψB1, LinearMap.comp_apply]
          _ = (ZA ⊗ₗ idQB) (V ψB1) := by
                simpa using (hA0_app (φ := ψB1))
      have htransport :
          ‖(ZA ⊗ₗ idQB) ((idQA ⊗ₗ ZHZB) Ψ0) - (ZA ⊗ₗ idQB) (V ψB1)‖ ≤ err0 := by
        simpa using
          (dist_le_of_transport (T := (ZA ⊗ₗ idQB)) (hT := hnorm_ZA_id)
            (x := ((idQA ⊗ₗ ZHZB) Ψ0)) (y := V ψB1) hB1ψ)
      calc
        ‖(ZA ⊗ₗ ZHZB) Ψ0 - V ((S.A0 ⊗ₗ S.B1) S.psi)‖
            = ‖(ZA ⊗ₗ idQB) ((idQA ⊗ₗ ZHZB) Ψ0) - (ZA ⊗ₗ idQB) (V ψB1)‖ := by
                rw [hideal, hphys]
        _ ≤ err0 := htransport

    have hu10 :
        ‖(XA ⊗ₗ HB) Ψ0 - V ((S.A1 ⊗ₗ S.B0) S.psi)‖ ≤ err0 := by
      have hAB :
          (S.A1 ⊗ₗ S.B0) =
            ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B0) ∘ₗ
              (S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) := by
        ext x y
        simp [TensorProduct.map_tmul, LinearMap.comp_apply]
      let ψA1 : H_A ⊗[ℂ] H_B := (S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi
      have hA1ψ :
          ‖V ψA1 - (XA ⊗ₗ idQB) Ψ0‖ ≤ err0 := by
        simpa [Ψ0, ψA1] using hA1_vec
      have hideal : (XA ⊗ₗ HB) Ψ0 = (idQA ⊗ₗ HB) ((XA ⊗ₗ idQB) Ψ0) := by
        simpa [LinearMap.comp_apply] using congrArg (fun F => F Ψ0) hXA_HB.symm
      have hphys :
          V ((S.A1 ⊗ₗ S.B0) S.psi) = (idQA ⊗ₗ HB) (V ψA1) := by
        calc
          V ((S.A1 ⊗ₗ S.B0) S.psi)
              = V (((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B0)
                  ψA1) := by
                    simp [hAB, ψA1, LinearMap.comp_apply]
          _ = (idQA ⊗ₗ HB) (V ψA1) := by
                simpa using (hB0_app (φ := ψA1))
      have htransport :
          ‖(idQA ⊗ₗ HB) ((XA ⊗ₗ idQB) Ψ0) - (idQA ⊗ₗ HB) (V ψA1)‖ ≤ err0 := by
        simpa using
          (dist_le_of_transport (T := (idQA ⊗ₗ HB)) (hT := hnorm_id_HB)
            (x := ((XA ⊗ₗ idQB) Ψ0)) (y := V ψA1) hA1ψ)
      calc
        ‖(XA ⊗ₗ HB) Ψ0 - V ((S.A1 ⊗ₗ S.B0) S.psi)‖
            = ‖(idQA ⊗ₗ HB) ((XA ⊗ₗ idQB) Ψ0) - (idQA ⊗ₗ HB) (V ψA1)‖ := by
                rw [hideal, hphys]
        _ ≤ err0 := htransport

    have hu11 :
        ‖(XA ⊗ₗ ZHZB) Ψ0 - V ((S.A1 ⊗ₗ S.B1) S.psi)‖ ≤ 2 * err0 := by
      have hAB :
          (S.A1 ⊗ₗ S.B1) =
            (S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ∘ₗ
              ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B1) := by
        ext x y
        simp [TensorProduct.map_tmul, LinearMap.comp_apply]
      let ψB1 : H_A ⊗[ℂ] H_B := ((LinearMap.id : H_A →ₗ[ℂ] H_A) ⊗ₗ S.B1) S.psi
      have hB1ψ :
          ‖V ψB1 - (idQA ⊗ₗ ZHZB) Ψ0‖ ≤ err0 := by
        simpa [ψB1] using hB1_vec
      have hA1ψB1 :
          ‖V ((S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψB1) - (XA ⊗ₗ idQB) (V ψB1)‖ ≤ err0 := by
        let ΔA1 : H_A →ₗ[ℂ] (Qubit ⊗[ℂ] H_A) :=
          ((pauliX ⊗ₗ (LinearMap.id : H_A →ₗ[ℂ] H_A)) ∘ₗ V_A) - (V_A ∘ₗ S.A1)
        have hVB_iso' : Isometry V_B := by
          simpa [hV_B] using (VB_is_isometry (H := H_B) S.B0 S.B1)
        have hΔsq :
            ‖((ΔA1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi)‖ ^ 2 ≤ cConst * ε := by
          simpa [ΔA1, hV_A] using (eq216 (S := S) (epsilon := ε) hBias)
        have hΔnorm :
            ‖((ΔA1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi)‖ ≤ err0 := by
          simpa [err0] using
            (norm_le_sqrt_of_sq_le
              (x := ((ΔA1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) S.psi))
              (r := cConst * ε) hΔsq)
        simpa [V, XA, idQB] using
          (A1_extraction_on_B1_state (S := S) (V_A := V_A) (V_B := V_B) (ΔA1 := ΔA1)
            (ψB1 := ψB1) (err0 := err0) (hψB1 := rfl) (hΔdef := rfl)
            (hΔnorm := hΔnorm) (hVB_iso := hVB_iso'))

      have hphys :
          V ((S.A1 ⊗ₗ S.B1) S.psi) = V ((S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψB1) := by
        simp [ψB1, hAB, LinearMap.comp_apply]
      have hideal : (XA ⊗ₗ ZHZB) Ψ0 = (XA ⊗ₗ idQB) ((idQA ⊗ₗ ZHZB) Ψ0) := by
        simpa [LinearMap.comp_apply] using congrArg (fun F => F Ψ0) hXA_ZHZB.symm

      -- Triangle inequality: B1 extraction then A1 extraction.
      have h1 :
          ‖(XA ⊗ₗ idQB) ((idQA ⊗ₗ ZHZB) Ψ0) - (XA ⊗ₗ idQB) (V ψB1)‖ ≤ err0 := by
        simpa using
          (dist_le_of_transport (T := (XA ⊗ₗ idQB)) (hT := hnorm_XA_id)
            (x := ((idQA ⊗ₗ ZHZB) Ψ0)) (y := V ψB1) hB1ψ)
      have h2 :
          ‖(XA ⊗ₗ idQB) (V ψB1) - V ((S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψB1)‖ ≤ err0 := by
        simpa [norm_sub_rev] using hA1ψB1

      have :
          ‖(XA ⊗ₗ ZHZB) Ψ0 - V ((S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψB1)‖ ≤ 2 * err0 := by
        have hmid :
            ‖(XA ⊗ₗ idQB) ((idQA ⊗ₗ ZHZB) Ψ0) -
                V ((S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψB1)‖ ≤ 2 * err0 := by
          exact
            norm_sub_le_two_mul_of_intermediate
              ((XA ⊗ₗ idQB) ((idQA ⊗ₗ ZHZB) Ψ0))
              ((XA ⊗ₗ idQB) (V ψB1))
              (V ((S.A1 ⊗ₗ (LinearMap.id : H_B →ₗ[ℂ] H_B)) ψB1))
              err0 h1 h2
        simpa [hideal] using hmid

      have hu11' :
          ‖(XA ⊗ₗ ZHZB) Ψ0 - V ((S.A1 ⊗ₗ S.B1) S.psi)‖ ≤ 2 * err0 := by
        simpa [hphys] using this
      exact hu11'

    -- Now transport the four correlator bounds to the swapped space and sum them.
    have h00 : ‖w00 - v00‖ = 0 := by
      have hw00v00 : w00 = v00 := by
        calc
          w00 = regSwap (H_A := H_A) (H_B := H_B) ((ZA ⊗ₗ HB) Ψ0) := hw00
          _ = regSwap (H_A := H_A) (H_B := H_B) (V ((S.A0 ⊗ₗ S.B0) S.psi)) := by
                simp [hu00_eq]
          _ = v00 := by simp [v00, V]
      simp [hw00v00]

    have h01 : ‖w01 - v01‖ ≤ err0 := by
      have hdist :=
        regSwap_dist_eq (H_A := H_A) (H_B := H_B)
          (x := (ZA ⊗ₗ ZHZB) Ψ0) (y := V ((S.A0 ⊗ₗ S.B1) S.psi))
      have : ‖regSwap (H_A := H_A) (H_B := H_B) ((ZA ⊗ₗ ZHZB) Ψ0)
            - regSwap (H_A := H_A) (H_B := H_B) (V ((S.A0 ⊗ₗ S.B1) S.psi))‖ ≤ err0 := by
        -- Rewrite the goal using `hdist` and apply `hu01`.
        rw [hdist]
        exact hu01
      -- Rewrite `w01`/`v01` and apply the bound.
      rw [hw01]
      simpa [v01, V] using this

    have h10 : ‖w10 - v10‖ ≤ err0 := by
      have hdist :=
        regSwap_dist_eq (H_A := H_A) (H_B := H_B)
          (x := (XA ⊗ₗ HB) Ψ0) (y := V ((S.A1 ⊗ₗ S.B0) S.psi))
      have : ‖regSwap (H_A := H_A) (H_B := H_B) ((XA ⊗ₗ HB) Ψ0)
            - regSwap (H_A := H_A) (H_B := H_B) (V ((S.A1 ⊗ₗ S.B0) S.psi))‖ ≤ err0 := by
        rw [hdist]
        exact hu10
      rw [hw10]
      simpa [v10, V] using this

    have h11 : ‖w11 - v11‖ ≤ 2 * err0 := by
      have hdist :=
        regSwap_dist_eq (H_A := H_A) (H_B := H_B)
          (x := (XA ⊗ₗ ZHZB) Ψ0) (y := V ((S.A1 ⊗ₗ S.B1) S.psi))
      have : ‖regSwap (H_A := H_A) (H_B := H_B) ((XA ⊗ₗ ZHZB) Ψ0)
            - regSwap (H_A := H_A) (H_B := H_B) (V ((S.A1 ⊗ₗ S.B1) S.psi))‖ ≤ 2 * err0 := by
        rw [hdist]
        exact hu11
      rw [hw11]
      simpa [v11, V] using this

    -- Now combine the four terms.
    have hrewrite :
        CHSHideal - CHSHphys =
          (w00 - v00) + (w01 - v01) + (w10 - v10) - (w11 - v11) := by
      rw [hCHSHideal_decomp, hCHSHphys_decomp]
      simp [sub_eq_add_neg]
      abel
    -- Triangle inequality over the four summands.
    have hsum :
        ‖(w00 - v00) + (w01 - v01) + (w10 - v10) - (w11 - v11)‖
          ≤ ‖w00 - v00‖ + ‖w01 - v01‖ + ‖w10 - v10‖ + ‖w11 - v11‖ := by
      simpa [add_assoc] using
        (four_term_norm_sub_le
          (a := w00 - v00) (b := w01 - v01) (c := w10 - v10) (d := w11 - v11))
    -- Finish.
    have h00' : ‖w00 - v00‖ = 0 := h00
    have h11' : ‖w11 - v11‖ ≤ 2 * err0 := h11
    have h01' : ‖w01 - v01‖ ≤ err0 := h01
    have h10' : ‖w10 - v10‖ ≤ err0 := h10
    -- Apply the bounds to the sum.
    have :
        ‖CHSHideal - CHSHphys‖ ≤ 4 * err0 := by
      calc
        ‖CHSHideal - CHSHphys‖
            = ‖(w00 - v00) + (w01 - v01) + (w10 - v10) - (w11 - v11)‖ := by
                simp [hrewrite]
        _ ≤ ‖w00 - v00‖ + ‖w01 - v01‖ + ‖w10 - v10‖ + ‖w11 - v11‖ := hsum
        _ ≤ 0 + err0 + err0 + (2 * err0) := by
              have :
                  (0 : ℝ) + ‖w01 - v01‖ + ‖w10 - v10‖ + ‖w11 - v11‖ ≤
                    (0 : ℝ) + err0 + err0 + (2 * err0) := by
                gcongr
              simpa [h00', add_assoc] using this
        _ = 4 * err0 := by ring
    simpa [err] using this

  -- Step 5: turn vector closeness into expectation closeness.
  have hΨnorm : ‖Ψ‖ = 1 := by
    have hVA : Isometry V_A := by
      simpa [hV_A] using
        (VA_is_isometry S.A0 S.A1)
    have hVB : Isometry V_B := by
      simpa [hV_B] using
        (VB_is_isometry S.B0 S.B1)
    simpa [hΨ] using
      (extracted_state_norm_one (S := S) (V_A := V_A) (V_B := V_B) hVA hVB)

  have hRe_bookkeeping :
      Complex.re (⟪Ψ, CHSHideal⟫_ℂ) ≥ Complex.re (⟪Ψ, CHSHphys⟫_ℂ) - err := by
    simpa using
      (re_inner_ge_sub_norm_of_diff (x := Ψ) (y := CHSHideal) (z := CHSHphys)
        (err := err) hΨnorm hdiff)

  -- Put everything together.
  have hCompare :
      Complex.re (⟪Ψ, ((K ⊗ₗ idJ) Ψ)⟫_ℂ) ≥ chshBias S - err := by
    -- Rewrite `CHSHideal` as `(K ⊗ I) Ψ` and `CHSHphys` expectation as `chshBias`.
    -- (Use `hCHSHideal_eq_K`, `hCHSHphys_re`, and `hRe_bookkeeping`.)
    -- The proof is a chain of `simp` + `linarith`.
    have hK :
        Complex.re (⟪Ψ, ((K ⊗ₗ idJ) Ψ)⟫_ℂ) = Complex.re (⟪Ψ, CHSHideal⟫_ℂ) := by
      -- Use `CHSHideal = (K ⊗ I) Ψ`.
      simp [hCHSHideal_eq_K]
    -- Now use the bookkeeping inequality and identify the physical expectation with `chshBias S`.
    have hPhys :
        Complex.re (⟪Ψ, CHSHphys⟫_ℂ) = chshBias S := by
      exact hCHSHphys_re
    -- Combine.
    linarith [hRe_bookkeeping, hK, hPhys]

  -- Final step: combine with the CHSH bias assumption and rewrite the error as `delta ε`.
  have :
      Complex.re (⟪Ψ, ((K ⊗ₗ idJ) Ψ)⟫_ℂ) ≥ 2 * Real.sqrt 2 - (ε + err) := by
    linarith [hCompare, hBias]
  simpa [delta, err] using this

end Link

end Approximate_Rigidity
