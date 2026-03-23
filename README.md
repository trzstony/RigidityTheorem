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

### From CHSH to guessing probability

The blueprint and entropy-bound files formalize the implication

$$
\text{Tr}(\rho_{AB}\,\mathrm{CHSH}) \ge 2\sqrt{2} - \varepsilon
\quad\Longrightarrow\quad
p_{\mathrm{guess}}(X \mid E)_\rho \le \tfrac12 + O(\sqrt{\varepsilon}),
$$

for Alice and Bob qubits, where $X$ is Alice's key-basis measurement outcome.

### Approximate CHSH rigidity

The approximate-rigidity files also target the standard CHSH rigidity direction: if an entangled strategy

$$
\left(|\psi\rangle, A_0, A_1, B_0, B_1\right)
$$

with local dimension $d$ achieves CHSH success probability at least

$$
\frac{1 + 1/\sqrt{2} - \epsilon}{2},
$$

then there exist local isometries

$$
V_A, V_B : \mathbb{C}^d \to \mathbb{C}^2 \otimes \mathbb{C}^d
$$

and a junk state

$$
|\Phi_{\mathrm{junk}}\rangle \in \mathbb{C}^d \otimes \mathbb{C}^d
$$

such that, up to $O(\sqrt{\epsilon})$ error,

- $(V_A \otimes V_B)|\psi\rangle$ is close to $\frac{1}{\sqrt{2}}(|00\rangle + |11\rangle) \otimes |\Phi_{\mathrm{junk}}\rangle$.
- $(V_A \otimes V_B)(A_0 \otimes I)|\psi\rangle$ is close to $(Z \otimes I)\left(\frac{1}{\sqrt{2}}(|00\rangle + |11\rangle)\right) \otimes |\Phi_{\mathrm{junk}}\rangle$.
- $(V_A \otimes V_B)(A_1 \otimes I)|\psi\rangle$ is close to $(X \otimes I)\left(\frac{1}{\sqrt{2}}(|00\rangle + |11\rangle)\right) \otimes |\Phi_{\mathrm{junk}}\rangle$.
- $(V_A \otimes V_B)(I \otimes B_0)|\psi\rangle$ is close to $(I \otimes H)\left(\frac{1}{\sqrt{2}}(|00\rangle + |11\rangle)\right) \otimes |\Phi_{\mathrm{junk}}\rangle$.
- $(V_A \otimes V_B)(I \otimes B_1)|\psi\rangle$ is close to $(I \otimes (Z H Z))\left(\frac{1}{\sqrt{2}}(|00\rangle + |11\rangle)\right) \otimes |\Phi_{\mathrm{junk}}\rangle$.

This is the rigidity statement developed in [RigidityTheorem.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Approximate_Rigidity/RigidityTheorem.lean) together with the supporting files in [Approximate_Rigidity](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Approximate_Rigidity).
