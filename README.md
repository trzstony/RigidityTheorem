# RigidityTheorem

Lean 4 formalization of CHSH rigidity and related quantum-information lemmas.

The repository currently has three main components:

- A reusable `Quantum` library for qubits, Pauli operators, Bell states, density operators, trace-distance machinery, and POVMs.
- An `Approximate_Rigidity` development for CHSH strategies, including extracted isometries, approximate operator relations, Bell-basis spectral arguments, and the main rigidity theorem statements.
- A Lean-style blueprint for the current robust CHSH rigidity chapter.

## Main content

- [RigidityTheorem/Quantum](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Quantum) contains the reusable quantum library:
  [Qubit.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Quantum/Qubit.lean),
  [Pauli.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Quantum/Pauli.lean),
  [Bell.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Quantum/Bell.lean),
  [Density.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Quantum/Density.lean),
  [TraceNorm.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Quantum/TraceNorm.lean),
  [TraceDistance.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Quantum/TraceDistance.lean),
  and [POVM.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Quantum/POVM.lean).
- [RigidityTheorem/Approximate_Rigidity](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Approximate_Rigidity) contains the CHSH-rigidity development:
  [BasicDefs.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Approximate_Rigidity/BasicDefs.lean),
  [Isometries.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Approximate_Rigidity/Isometries.lean),
  [IsometriesApprox.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Approximate_Rigidity/IsometriesApprox.lean),
  [SpectralArgument.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Approximate_Rigidity/SpectralArgument.lean),
  [chsh_link.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Approximate_Rigidity/chsh_link.lean),
  [Junk.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Approximate_Rigidity/Junk.lean),
  and [RigidityTheorem.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Approximate_Rigidity/RigidityTheorem.lean).
- [RigidityTheorem/blueprint](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/blueprint) contains a Lean-style blueprint for the current robust CHSH rigidity development, organized around the dependency flow in `Approximate_Rigidity`.

## Main theorem direction

### Approximate CHSH rigidity

The main theorem direction in the current repository is the standard CHSH rigidity statement: if an entangled strategy

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

This is the rigidity statement developed in
[RigidityTheorem.lean](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Approximate_Rigidity/RigidityTheorem.lean)
together with the supporting files in
[Approximate_Rigidity](/Volumes/Files/Research_New_chapter/RigidityTheorem/RigidityTheorem/Approximate_Rigidity).
The top-level theorem file currently still contains placeholder proofs for some final statements.
