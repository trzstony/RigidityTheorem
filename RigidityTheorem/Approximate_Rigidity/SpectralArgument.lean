import Quantum.Bell
import Approximate_Rigidity.Isometries
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis


open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Quantum

namespace Approximate_Rigidity

open Module

/-!
Spectral argument for the two-qubit CHSH operator.

This file corresponds to Sections 11.4-11.5 of the notes, including the
eigenvalue computation for K and the projection-to-distance estimate.
-/



variable {H_A H_B : Type*}
variable [NormedAddCommGroup H_A] [NormedAddCommGroup H_B]
variable [InnerProductSpace ℂ H_A] [InnerProductSpace ℂ H_B]
variable (Ψ : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] (H_A ⊗[ℂ] H_B))
variable (delta : Real)

section Decomposition

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℂ J]

/-- A `Finsupp` representation of `Ψ` along the Bell basis of `Qubit ⊗ Qubit`. -/
noncomputable def bellDecompositionFinsupp
    (Ψ : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] J) : Fin 4 →₀ J :=
  Classical.choose (TensorProduct.eq_repr_basis_left (ℬ := bellBasis) (x := Ψ))

theorem bellDecompositionFinsupp_spec
    (Ψ : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] J) :
    ((bellDecompositionFinsupp (J := J) Ψ).sum fun i n => (bellBasis i) ⊗ₜ[ℂ] n) = Ψ :=
  Classical.choose_spec (TensorProduct.eq_repr_basis_left (ℬ := bellBasis) (x := Ψ))

/-- The `J`-components of `Ψ` along the Bell basis of `Qubit ⊗ Qubit`. -/
noncomputable def bellDecomposition
    (Ψ : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] J) : Fin 4 → J :=
  fun i => bellDecompositionFinsupp (J := J) Ψ i

theorem sum_bellBasis_tmul_bellDecomposition
    (Ψ : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] J) :
    (∑ i : Fin 4, (bellBasis i) ⊗ₜ[ℂ] (bellDecomposition (J := J) Ψ i)) = Ψ := by
  -- Rewrite the `Finsupp`-sum as a `Fintype`-sum (zeros are allowed).
  simpa [bellDecomposition, Finsupp.sum_fintype] using
    (bellDecompositionFinsupp_spec (J := J) Ψ)

/-- The squared norm of `∑ᵢ bellBasisᵢ ⊗ ηᵢ` is the sum of the squared
norms of the junk components `ηᵢ`. -/
theorem norm_sq_sum_tmul_eq_sum_norm_sq (η : Fin 4 → J) :
    ‖(∑ i : Fin 4, (bellBasis i) ⊗ₜ[ℂ] (η i))‖ ^ 2 = ∑ i : Fin 4, ‖η i‖ ^ 2 := by
  classical
  -- Rewrite the sum as a `Finset.univ` sum so we can use `sum_inner` / `inner_sum`.
  let s : Finset (Fin 4) := Finset.univ
  let f : Fin 4 → (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] J := fun i => (bellBasis i) ⊗ₜ[ℂ] (η i)
  set x : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] J := ∑ i ∈ s, f i with hx
  have hx' : (∑ i : Fin 4, (bellBasis i) ⊗ₜ[ℂ] (η i)) = x := by
    simp [x, s, f]
  -- Compute `⟪x,x⟫` using orthonormality of the Bell basis.
  have hδ : ∀ i j : Fin 4, ⟪bellVec i, bellVec j⟫_ℂ = if i = j then (1 : ℂ) else (0 : ℂ) :=
    orthonormal_iff_ite.mp bellVec_orthonormal
  have hinner : ⟪x, x⟫_ℂ = ∑ i ∈ s, ⟪η i, η i⟫_ℂ := by
    -- Expand into a double sum.
    have hdouble : ⟪x, x⟫_ℂ = ∑ i ∈ s, ∑ j ∈ s, ⟪f i, f j⟫_ℂ := by
      rw [hx]
      -- Expand the left argument of the inner product.
      rw [sum_inner (𝕜 := ℂ) (s := s) (f := f) (x := ∑ j ∈ s, f j)]
      -- Expand the right argument inside the sum.
      simp [inner_sum (𝕜 := ℂ) (s := s) (f := f)]
    -- Simplify the summand using `TensorProduct.inner_tmul` and orthonormality.
    calc
      ⟪x, x⟫_ℂ = ∑ i ∈ s, ∑ j ∈ s, ⟪f i, f j⟫_ℂ := hdouble
      _ = ∑ i ∈ s, ∑ j ∈ s, (if i = j then ⟪η i, η j⟫_ℂ else 0) := by
            simp [f, TensorProduct.inner_tmul (𝕜 := ℂ), bellBasis_apply, hδ, ite_mul]
      _ = ∑ i ∈ s, ⟪η i, η i⟫_ℂ := by
            -- For each fixed `i`, only the `j = i` term survives.
            -- `Finset.sum_ite_eq` evaluates the inner sum.
            simp [Finset.sum_ite_eq, s]
  -- Apply `re` (as an additive monoid hom) and use `re ⟪x,x⟫ = ‖x‖^2`.
  let reHom : ℂ →+ ℝ := RCLike.re
  have hre0 : reHom ⟪x, x⟫_ℂ = reHom (∑ i ∈ s, ⟪η i, η i⟫_ℂ) := congrArg reHom hinner
  have hre : reHom ⟪x, x⟫_ℂ = ∑ i ∈ s, reHom ⟪η i, η i⟫_ℂ := by
    -- Push `re` through the finite sum.
    -- (We keep this as a separate step so we can rewrite with `map_sum`.)
    have := hre0
    rw [map_sum (g := reHom) (f := fun i : Fin 4 => ⟪η i, η i⟫_ℂ) (s := s)] at this
    simpa using this
  have : ‖x‖ ^ 2 = ∑ i ∈ s, ‖η i‖ ^ 2 := by
    calc
      ‖x‖ ^ 2 = reHom ⟪x, x⟫_ℂ := (inner_self_eq_norm_sq (𝕜 := ℂ) x).symm
      _ = ∑ i ∈ s, reHom ⟪η i, η i⟫_ℂ := hre
      _ = ∑ i ∈ s, ‖η i‖ ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) (η i))
  -- Rewrite back from `x` to the original sum.
  simpa [hx', hx, s, f] using this


/-- For a unit vector `Ψ`, the decomposition probabilities `pᵢ := ‖ηᵢ‖^2` sum to `1`. -/
theorem decomposition_probs_sum_eq_one
    (Ψ : (Qubit ⊗[ℂ] Qubit) ⊗[ℂ] J)
    (hΨ : ‖Ψ‖ = 1) :
      (∑ i : Fin 4, ‖bellDecomposition Ψ i‖ ^ 2) = 1 := by
  have hsum :
      (∑ i : Fin 4, (bellBasis i) ⊗ₜ[ℂ] (bellDecomposition (J := J) Ψ i)) = Ψ :=
    sum_bellBasis_tmul_bellDecomposition (J := J) Ψ
  have hnorm : ‖Ψ‖ ^ 2 = ∑ i : Fin 4, ‖bellDecomposition (J := J) Ψ i‖ ^ 2 := by
    calc
      ‖Ψ‖ ^ 2 =
          ‖(∑ i : Fin 4, (bellBasis i) ⊗ₜ[ℂ] (bellDecomposition (J := J) Ψ i))‖ ^ 2 := by
            exact (congrArg (fun z => ‖z‖ ^ 2) hsum).symm
      _ = ∑ i : Fin 4, ‖bellDecomposition (J := J) Ψ i‖ ^ 2 :=
          norm_sq_sum_tmul_eq_sum_norm_sq (J := J) (bellDecomposition (J := J) Ψ)
  calc
    (∑ i : Fin 4, ‖bellDecomposition (J := J) Ψ i‖ ^ 2) = ‖Ψ‖ ^ 2 := by
      simpa using hnorm.symm
    _ = (1 : ℝ) := by simp [hΨ]


end Decomposition


end Approximate_Rigidity
