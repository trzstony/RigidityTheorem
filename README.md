# RigidityTheorem

Lean 4 formalization of a CHSH rigidity / entropy-bound project.

The repository currently has two main threads:

- A `CHSH -> Bell overlap -> postselection -> trace-distance -> guessing probability` pipeline for qubit systems.
- An approximate-rigidity development for CHSH strategies, including extracted isometries, Bell-basis spectral arguments, and operator-extraction statements.

## Main content

- [RigidityTheorem/Quantum](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Quantum) contains the reusable quantum library: qubits, Pauli operators, Bell states, density operators, partial trace, trace norm / trace distance, and POVMs.
- [RigidityTheorem/Entropy_Bound](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Entropy_Bound) contains the CHSH-to-guessing-probability formalization.
  Key files are:
  [Setup.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Entropy_Bound/Setup.lean),
  [CHSHBound.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Entropy_Bound/CHSHBound.lean),
  [PostselectionBridge.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Entropy_Bound/PostselectionBridge.lean),
  [RigidityToPguess.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Entropy_Bound/RigidityToPguess.lean),
  and [GuessingLemmas.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Entropy_Bound/GuessingLemmas.lean).
- [RigidityTheorem/Approximate_Rigidity](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Approximate_Rigidity) develops the approximate CHSH rigidity side: basic definitions, isometry constructions, approximate anti-commutation estimates, spectral decomposition, and theorem statements for state/operator extraction. The top-level theorem file currently notes placeholder proofs for some final statements.
- [RigidityTheorem/blueprint](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/blueprint) contains the paper-style blueprint. The current chapter is “From CHSH to guessing probability.”
- [RigidityTheorem/Entropy_Bound_Explain](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Entropy_Bound_Explain) contains short proof outlines and file guides for the entropy-bound modules.

## Main theorem direction

The blueprint and entropy-bound files formalize the implication

\[
\operatorname{Tr}(\rho_{AB}\,\mathrm{CHSH}) \ge 2\sqrt{2} - \varepsilon
\quad\Longrightarrow\quad
p_{\mathrm{guess}}(X \mid E)_\rho \le \tfrac12 + O(\sqrt{\varepsilon}),
\]

for Alice and Bob qubits, where `X` is Alice's key-basis measurement outcome.