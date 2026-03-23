# Entropy_Bound/GuessingLemmas.lean

## Main definitions

### Definition ([guessFunctional](../Entropy_Bound/GuessingLemmas.lean#L15))
- Definition:
  for a classical-quantum operator `ρXE` and a POVM `M : POVM X E`,
  `guessFunctional ρXE M` is the real trace of the decision operator
  `∑ x, |x⟩⟨x| ⊗ M.effect x` against `ρXE`.
- Meaning:
  this is the guessing success value achieved by the particular measurement `M`.

### Definition ([pGuess](../Entropy_Bound/GuessingLemmas.lean#L28))
- Definition:
  `pGuess ρXE` is the supremum of `guessFunctional ρXE M` over all POVMs on Eve's system.
- Meaning:
  this is Eve's optimal guessing probability for the classical register.

### Definition ([liftedDecisionOpFromABE](../Entropy_Bound/GuessingLemmas.lean#L38))
- Definition:
  a binary POVM on `E` is lifted to an operator on `ABE` by sandwiching
  `I_AB ⊗ M.effect x` with the key projector for outcome `x` and summing over `x`.
- Meaning:
  this packages a guessing measurement on `E` into the `ABE` picture used later in the bridge argument.

## Public theorems

## Theorem ([pGuess_continuity](../Entropy_Bound/GuessingLemmas.lean#L200))
- Theorem:
  $$
  p_{\mathrm{guess}}(\rho_{XE})
  \le
  p_{\mathrm{guess}}(\sigma_{XE}) + D(\rho_{XE},\sigma_{XE}).
  $$
- Hypotheses:
  1. `E` is finite-dimensional.
  2. `ρXE` is a density operator on `Qubit ⊗ E`.
  3. `σXE` is a density operator on `Qubit ⊗ E`.
- Proof outline:
  first prove the binary-register statement for each fixed POVM, then pass to suprema over POVMs; the public theorem is obtained by rewriting `Qubit` as `Fin 2`.
- Proved or not: ✅

## Theorem ([ideal_bell_induces_uniform_independent_bit](../Entropy_Bound/GuessingLemmas.lean#L387))
- Theorem:
  $$
  \mathrm{IsUniformBitIndependent}(\sigma_{XE})
  \Longrightarrow
  p_{\mathrm{guess}}(\sigma_{XE})=\frac12.
  $$
- Hypotheses:
  1. `E` is finite-dimensional.
  2. `σXE : Operator (Qubit ⊗ E)`.
  3. `σXE` has the ideal form of a uniform classical bit tensored with an Eve state.
- Proof outline:
  show that every binary POVM has guessing value exactly `1/2` on the ideal tensor state, then identify the supremum set with the singleton `{1/2}`.
- Proved or not: ✅

## Theorem ([chsh_to_pGuess_bound](../Entropy_Bound/GuessingLemmas.lean#L426))
- Theorem:
  if
  $$
  D(\rho_{XE},\sigma_{XE})
  \le
  \sqrt{\frac{\varepsilon}{2\sqrt 2}}+\frac{\varepsilon}{2\sqrt 2}
  $$
  and `σXE` is ideal, then
  $$
  p_{\mathrm{guess}}(\rho_{XE})
  \le
  \frac12 + \sqrt{\frac{\varepsilon}{2\sqrt 2}}+\frac{\varepsilon}{2\sqrt 2}.
  $$
- Hypotheses:
  1. `ρXE` and `σXE` are density operators on `Qubit ⊗ E`.
  2. `ε : Real`.
  3. `IsUniformBitIndependent σXE`.
  4. The stated trace-distance bound holds.
- Proof outline:
  combine `pGuess_continuity` with `ideal_bell_induces_uniform_independent_bit`, then substitute the explicit distance estimate.
- Proved or not: ✅

## Theorem ([chsh_to_pGuess_bound_of_measure_contract_and_gentle](../Entropy_Bound/GuessingLemmas.lean#L723))
- Theorem:
  from a CHSH lower bound on the `AB` marginal of `ρABE`, derive the explicit guessing bound
  $$
  p_{\mathrm{guess}}(\rho_{XE})
  \le
  \frac12 + \sqrt{\frac{\varepsilon}{2\sqrt 2}}+\frac{\varepsilon}{2\sqrt 2},
  $$
  where `ρXE = rhoXE_from_ABE ρABE`.
- Hypotheses:
  1. `ρABE` is a density operator on `ABE`.
  2. `ε : Real`.
  3. `ε ≤ 2 * sqrt 2 - 2`.
  4. The CHSH score satisfies
     `2 * sqrt 2 - ε ≤ Re(tr(canonicalCHSH · ρAB))`.
- Proof outline:
  define the measured state `ρXE`, construct the postselected Bell-reference state `σXE`, prove `σXE` is ideal, bound `D(ρXE,σXE)` using measurement contraction and gentle postselection, convert Bell infidelity to the explicit `ε` bound, and finish with `chsh_to_pGuess_bound`.
- Proved or not: ✅

## Internal proof structure
- The binary continuity argument is implemented through the private lemmas
  `guessFunctional_perturbation_bound_fin2`,
  `guessFunctional_le_one_fin2`, and
  `pGuess_continuity_fin2`.
- The ideal-state `1/2` value is reduced to the private lemma
  `guessFunctional_const_of_uniform_bit_tensor`.
- The final CHSH wrapper uses a substantial private bridge layer:
  `trace_rankOne_comp`,
  `partialTraceLeft_tensor_pureOp`,
  `conj_pureOp_of_adjoint_eq`,
  `keyProjector_apply_tmul`,
  `bell_branch0_AB`,
  `bell_branch1_AB`,
  `rhoECond_bellTensor_bit0`,
  `rhoECond_bellTensor_bit1`,
  and
  `re_postselectSuccessC_eq_bellOverlapAB`.

## File status
- Public API currently consists of 3 definitions and 4 public theorems.
- All 4 public theorems are proved.
- The source still contains a historical docstring saying “the only `sorry`”, but the current file body has no active `sorry`.
