# Entropy_Bound/RigidityToPguess.lean

## Namespace note
- This file lives in the namespace `RigidityToPguess`, not `Entropy_Bound`.
- It develops the trace-norm tools needed for the measurement-contract step used later in the entropy-bound pipeline.

## Public theorems

## Theorem ([partial_trace_contractive](../Entropy_Bound/RigidityToPguess.lean#L18))
- Theorem:
  $$
  \|\operatorname{Tr}_S(H)\|_1 \le \|H\|_1.
  $$
- Hypotheses:
  1. `R` and `S` are finite-dimensional complex Hilbert spaces.
  2. `H : Operator (R ⊗ S)`.
- Proof outline:
  rewrite the left-hand side using `trace_variational`, identify each variational term with
  `Tr((U_R \otimes I_S)H)` via `trace_comp_partialTraceRight`, and bound it by `traceNorm H`
  using an eigenbasis/singular-value argument plus norm preservation of `U_R ⊗ I_S`.
- Proof script present: ✅
- Verified by current Lean file: ❌

## Theorem ([partial_trace_contractive_left](../Entropy_Bound/RigidityToPguess.lean#L84))
- Theorem:
  $$
  \|\operatorname{Tr}_R(H)\|_1 \le \|H\|_1.
  $$
- Hypotheses:
  1. `R` and `S` are finite-dimensional complex Hilbert spaces.
  2. `H : Operator (R ⊗ S)`.
- Proof outline:
  same strategy as the previous theorem, now using `trace_mul_partialTraceLeft` and norm preservation of `I_R \otimes U_S`.
- Proof script present: ✅
- Verified by current Lean file: ❌

## Theorem ([isometry_trace_norm](../Entropy_Bound/RigidityToPguess.lean#L149))
- Theorem:
  if `W† ∘ W = id`, then
  $$
  \|W X W^\dagger\|_1 = \|X\|_1.
  $$
- Hypotheses:
  1. `H` and `K` are finite-dimensional complex Hilbert spaces.
  2. `W : H →ₗ[ℂ] K`.
  3. `LinearMap.adjoint W ∘ₗ W = LinearMap.id`.
  4. `X : Operator H`.
- Proof outline:
  prove the Gram identity for `(W X W†)†(W X W†)`, show operator square roots intertwine with isometric conjugation, then use trace cyclicity to recover `traceNorm X`.
- Proof script present: ✅
- Verified by current Lean file: ❌

## Theorem ([measure_contract](../Entropy_Bound/RigidityToPguess.lean#L616))
- Theorem:
  for the measurement-and-discard map `rhoXE_from_ABE`,
  $$
  \|\rho_{XE}(\rho_{ABE}) - \rho_{XE}(\sigma_{ABE})\|_1
  \le
  \|\rho_{ABE} - \sigma_{ABE}\|_1.
  $$
- Hypotheses:
  1. `E` is finite-dimensional.
  2. `ρABE` and `σABE` are density operators on `ABESystem E`.
- Proof outline:
  first prove linearity of `rhoXE_from_ABE`, reducing the difference to a single operator `Δ`;
  then apply `trace_variational` to `rhoXE_from_ABE Δ`, build an effective contraction `W` on `ABE`, prove the trace identity
  `Tr(u · rhoXE_from_ABE Δ) = Tr(W · Δ)`, and conclude from a contraction trace bound.
- Proof script present: ✅
- Verified by current Lean file: ❌

## Public helper lemmas

## Lemma ([mc_kP_idem](../Entropy_Bound/RigidityToPguess.lean#L304))
- Statement:
  `keyProjector x ∘ keyProjector x = keyProjector x`.
- Role:
  projector algebra for the measurement channel decomposition.

## Lemma ([mc_kP_sum](../Entropy_Bound/RigidityToPguess.lean#L375))
- Statement:
  `∑ x : Fin 2, keyProjector x = id`.
- Role:
  decomposition of the `ABE` space into the two key branches.

## Lemma ([mc_kP_sa](../Entropy_Bound/RigidityToPguess.lean#L399))
- Statement:
  `keyProjector x` is self-adjoint.
- Role:
  used to derive orthogonality and contraction estimates for the branch projectors.

## Internal proof structure
- `mc_norm_trace_contraction_le` generalizes the usual unitary trace bound to arbitrary contractions.
- `mc_kP_cross`, `mc_kP_cross'`, `mc_kP_norm_le`, `mc_kP_orth`, and `mc_kP_parseval` build the orthogonal-projector calculus for `keyProjector`.
- `mc_cL_norm_le` proves that contracting against a classical basis ket is norm-nonincreasing.
- `mc_idtensor_contraction_le` lifts a contraction on `E` to a contraction on `H ⊗ E`.
- These lemmas feed directly into the contraction operator `W` used in `measure_contract`.

## File status
- The current file has 4 public theorems and 3 additional public lemmas.
- `rg` finds no active `sorry` in the source.
- A fresh `lake env lean Entropy_Bound/RigidityToPguess.lean` run on March 13, 2026 fails.
- The first failure is around [RigidityToPguess.lean](/Volumes/Files/Research_New_chapter/Rigidity_Theorem_copy2/Entropy_Bound/RigidityToPguess.lean#L304), where `mc_kP_idem` triggers invalid argument-name and synthesis errors; downstream failures then follow in the `mc_kP_*` and `measure_contract` blocks.
- The older explanation was obsolete: it referred to a nonexistent theorem `chsh_to_pGuess_bound_measure_contract_discharged` and line numbers from a different file version.
