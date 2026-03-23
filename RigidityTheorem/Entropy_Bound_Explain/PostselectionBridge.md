# Entropy_Bound/PostselectionBridge.lean

## Main definitions

### Definition ([postselectProjector](../Entropy_Bound/PostselectionBridge.lean#L12))
- Definition:
  `postselectProjector` is the Bell projector on `AB` tensored with the identity on `E`:
  `|Φ⁺⟩⟨Φ⁺| ⊗ I_E`.
- Meaning:
  this is the operator used to postselect onto the ideal Bell branch.

### Definition ([postselectUnnormalized](../Entropy_Bound/PostselectionBridge.lean#L17))
- Definition:
  `postselectUnnormalized ρABE = Π ρABE Π`, where `Π = postselectProjector`.
- Meaning:
  this is the raw, unnormalized postselected operator.

### Definition ([postselectSuccessC](../Entropy_Bound/PostselectionBridge.lean#L23))
- Definition:
  `postselectSuccessC ρABE = Tr(Π ρABE)`.
- Meaning:
  this is the complex-valued postselection success quantity whose real part is the success probability used later.

### Definition ([postselectState](../Entropy_Bound/PostselectionBridge.lean#L32))
- Definition:
  `postselectState ρABE = (postselectSuccessC ρABE)⁻¹ • postselectUnnormalized ρABE`.
- Meaning:
  this is the normalized Bell-postselected state, assuming the success value is nonzero.

### Definition ([bellPartialElement](../Entropy_Bound/PostselectionBridge.lean#L102))
- Definition:
  `bellPartialElement ρABE` is
  `(⟨Φ⁺| ⊗ I_E) ρABE (|Φ⁺⟩ ⊗ I_E)` as an operator on `E`.
- Meaning:
  this is the `E`-system operator extracted by Bell postselection, and it is the tensor factor appearing in the factorization theorems.

## Public theorems

## Theorem ([trace_postselectUnnormalized](../Entropy_Bound/PostselectionBridge.lean#L64))
- Theorem:
  $$
  \operatorname{Tr}(\Pi \rho \Pi)=\operatorname{Tr}(\Pi \rho).
  $$
- Hypotheses:
  1. `E` is finite-dimensional.
  2. `ρABE : Operator (ABESystem E)`.
- Proof outline:
  use cyclicity of trace and the idempotence of the Bell projector `Π`.
- Proved or not: ✅

## Theorem ([trace_postselectState_eq_one](../Entropy_Bound/PostselectionBridge.lean#L86))
- Theorem:
  if `postselectSuccessC ρABE ≠ 0`, then
  $$
  \operatorname{Tr}(\mathrm{postselectState}(\rho)) = 1.
  $$
- Hypotheses:
  1. `E` is finite-dimensional.
  2. `ρABE : Operator (ABESystem E)`.
  3. `postselectSuccessC ρABE ≠ 0`.
- Proof outline:
  pull the scalar normalization factor outside the trace and substitute `trace_postselectUnnormalized`.
- Proved or not: ✅

## Theorem ([postselectUnnormalized_eq_bellTensor](../Entropy_Bound/PostselectionBridge.lean#L132))
- Theorem:
  $$
  \Pi \rho_{ABE} \Pi
  =
  |\Phi^+\rangle\!\langle\Phi^+| \otimes
  \bigl((\langle \Phi^+| \otimes I)\rho_{ABE}(|\Phi^+\rangle \otimes I)\bigr).
  $$
- Hypotheses:
  1. `E` is finite-dimensional.
  2. `ρABE : Operator (ABESystem E)`.
- Proof outline:
  factor the Bell projector as `tensorLeft Φ_plus ∘ contractLeft Φ_plus`, then compare both sides on pure tensors using tensor-extensionality.
- Proved or not: ✅

## Theorem ([postselectState_eq_bellTensor](../Entropy_Bound/PostselectionBridge.lean#L151))
- Theorem:
  $$
  \mathrm{postselectState}(\rho_{ABE})
  =
  |\Phi^+\rangle\!\langle\Phi^+|
  \otimes
  \Bigl(
    (\operatorname{Tr}(\Pi \rho_{ABE}))^{-1}
    (\langle \Phi^+| \otimes I)\rho_{ABE}(|\Phi^+\rangle \otimes I)
  \Bigr).
  $$
- Hypotheses:
  1. `E` is finite-dimensional.
  2. `ρABE : Operator (ABESystem E)`.
- Proof outline:
  rewrite `postselectState` via `postselectUnnormalized_eq_bellTensor` and move the scalar normalization into the `E` tensor factor.
- Proved or not: ✅

## Theorem ([gentle_postselection_bound](../Entropy_Bound/PostselectionBridge.lean#L1023))
- Theorem:
  letting
  `p = Re (postselectSuccessC ρABE)`, one has
  $$
  \|\rho_{ABE} - \widetilde{\rho}_{ABE}\|_1
  \le
  2\sqrt{1-p} + 2(1-p),
  $$
  where `\widetilde{\rho}_{ABE} = postselectState ρABE`.
- Hypotheses:
  1. `E` is finite-dimensional.
  2. `ρABE` is a density operator on `ABESystem E`.
  3. `postselectSuccessC ρABE ≠ 0`.
- Proof outline:
  split the argument into two pieces:
  first bound `‖ρ - ΠρΠ‖₁` by decomposing with the complementary projector `Π⊥ = I - Π` and controlling cross terms by a square-root estimate;
  then compute `‖ΠρΠ - \widetildeρ‖₁ = 1-p`;
  a final triangle inequality yields the stated bound.
- Proved or not: ✅

## Internal proof structure
- The factorization results rely on the private projector lemmas
  `bellProjector_idempotent`,
  `postselectProjector_idempotent`, and
  `postselectProjector_factored`.
- The gentle bound is supported by the private trace-norm lemmas
  `traceNorm_le_re_trace_of_isPositive`,
  `norm_trace_le_traceNorm`,
  `traceNorm_eq_re_trace_of_isPositive`, and
  `isPositive_real_smul`.
- The main technical core is the pair of cross-term estimates
  `traceNorm_cross_le_sqrt_trace` and
  `traceNorm_cross_rev_le_sqrt_trace`.
- The final theorem is assembled from the two bridge pieces
  `traceNorm_rho_sub_postselectUnnormalized_le` and
  `traceNorm_postselectUnnormalized_sub_state_eq`.

## File status
- Public API currently consists of 5 definitions and 5 public theorems.
- All 5 public theorems are proved.
- The older explanation mentioning `distance_bound_from_chsh_measure_gentle` and compile-time type mismatches is obsolete; that theorem is not in the current file.
- I also found no active `sorry` token in the current source.
