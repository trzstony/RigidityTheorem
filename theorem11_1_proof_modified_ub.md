# Detailed proof of Theorem 11.1 (Robust rigidity of CHSH)

This file is a structured write-up of the proof of Theorem 11.1 as presented in the **QIC 890 lecture notes (Apr 22, 2019)**, Section 11.2–11.5 (with supporting lemmas from Section 11.1), with **Bob’s canonical-form unitary $U_B$ rewritten** to match the convention
$$
A_0=\sigma_z,\quad A_1=\sigma_x,\qquad
B_0=\frac{\sigma_z+\sigma_x}{\sqrt2},\quad
B_1=\frac{\sigma_z-\sigma_x}{\sqrt2}.
$$

---

## Theorem 11.1 ([14]) — Robust rigidity of CHSH

Let $(|\psi\rangle, A_0, A_1, B_0, B_1)$ be an entangled strategy for the CHSH game with local dimension $d$, where
- $|\psi\rangle\in \mathbb{C}^d\otimes \mathbb{C}^d$ is a bipartite state,
- $A_0,A_1,B_0,B_1\in \mathbb{C}^{d\times d}$ are observables (Hermitian, eigenvalues in $\{\pm 1\}$).

Define the **CHSH value**
$$
\beta \,:=\, \langle \psi| A_0\otimes B_0 + A_0\otimes B_1 + A_1\otimes B_0 - A_1\otimes B_1 |\psi\rangle,
\qquad
\beta \ge 2\sqrt{2}-\varepsilon.
$$

Write $Z:=\sigma_z$, $X:=\sigma_x$ and define
$$
H:=\frac{Z+X}{\sqrt2},\qquad H':=\frac{Z-X}{\sqrt2}.
$$

Then there exist local isometries $V_A,V_B:\mathbb{C}^d\to \mathbb{C}^2\otimes \mathbb{C}^d$ and a state $|\Phi_{\text{junk}}\rangle\in \mathbb{C}^d\otimes \mathbb{C}^d$ such that (with $\varepsilon_{\mathrm{norm}}:=\varepsilon/4$, $c:=16\sqrt2$, and
$$
\delta:=\varepsilon_{\mathrm{norm}}+\sqrt{c\varepsilon_{\mathrm{norm}}}=\frac{\varepsilon}{4}+\sqrt{4\sqrt2\,\varepsilon}
$$
):

1. **State extraction**
$$
\|(V_A\otimes V_B)|\psi\rangle - |\Phi^+\rangle\otimes |\Phi_{\text{junk}}\rangle\|
\le \sqrt{2\sqrt2\,\delta},
\qquad
|\Phi^+\rangle:=\frac{|00\rangle+|11\rangle}{\sqrt2}.
$$

2. **Operator extraction (Alice)**
$$
\|(V_A\otimes V_B)(A_0\otimes I)|\psi\rangle - (Z\otimes I)|\Phi^+\rangle\otimes |\Phi_{\text{junk}}\rangle\|
\le \sqrt{2\sqrt2\,\delta},
$$
$$
\|(V_A\otimes V_B)(A_1\otimes I)|\psi\rangle - (X\otimes I)|\Phi^+\rangle\otimes |\Phi_{\text{junk}}\rangle\|
\le \sqrt{c\varepsilon_{\mathrm{norm}}}+\sqrt{2\sqrt2\,\delta}.
$$

3. **Operator extraction (Bob)**
$$
\|(V_A\otimes V_B)(I\otimes B_0)|\psi\rangle - (I\otimes H)\,|\Phi^+\rangle\otimes |\Phi_{\text{junk}}\rangle\|
\le \sqrt{2\sqrt2\,\delta},
$$
$$
\|(V_A\otimes V_B)(I\otimes B_1)|\psi\rangle - (I\otimes H')\,|\Phi^+\rangle\otimes |\Phi_{\text{junk}}\rangle\|
\le \sqrt{c\varepsilon_{\mathrm{norm}}}+\sqrt{2\sqrt2\,\delta}.
$$

---

## Roadmap

1. **Approximate algebra (11.2).** Near-optimal CHSH implies $A_0,A_1$ and $B_0,B_1$ approximately anti-commute on the support of the reduced state.
2. **Local isometries (11.3).** Build $V_A,V_B$ extracting a qubit on which Alice behaves like $(Z,X)$ and Bob behaves like $(H,H')$.
3. **State identification (11.4–11.5).** The extracted two-qubit state must be close to a max-eigenvector of the 2-qubit CHSH operator, hence close to $|\Phi^+\rangle$ (up to a local rotation on Bob).

---

## Preliminaries: state-dependent norms (11.1)

Let
$$
\sigma := \mathrm{Tr}_2(|\psi\rangle\langle\psi|)
$$
be Alice’s reduced density matrix. For operators $M,N\in\mathbb{C}^{d\times d}$ define
$$
\langle M,N\rangle_\sigma := \mathrm{Tr}(M^{*}N\,\sigma),\qquad
\|M\|_\sigma := \sqrt{\langle M,M\rangle_\sigma}.
$$
Key identity (used repeatedly): for any $M$,
$$
\|M\|_\sigma^2=\langle\psi|(M^*M\otimes I)|\psi\rangle=\|(M\otimes I)|\psi\rangle\|^2.
$$

**Lemma 11.6 (overlap vs distance).** If $U,V$ are isometries/unitaries then
$$
\Re\langle U,V\rangle_\sigma = 1-\frac12\|U-V\|_\sigma^2.
$$

---

## Part I — Approximate anti-commutation from CHSH (11.2)

Let $\beta_{\mathrm{norm}}:=\beta/4$ so that the hypothesis becomes
$$
\beta_{\mathrm{norm}}\ge \frac1{\sqrt2}-\varepsilon_{\mathrm{norm}},\qquad \varepsilon_{\mathrm{norm}}:=\varepsilon/4.
$$

**Theorem 11.7 (notes).**
$$
\|A_1A_0 + A_0A_1\|_\sigma^2 \le 32\sqrt2\,\varepsilon_{\mathrm{norm}},
\qquad
\|B_0B_1 + B_1B_0\|_\sigma^2 \le 32\sqrt2\,\varepsilon_{\mathrm{norm}}.
$$

**Corollary 11.8 (notes).** Using Lemma 11.6,
$$
\Re\langle -A_1A_0,\;A_0A_1\rangle_\sigma \ge 1-16\sqrt2\,\varepsilon_{\mathrm{norm}},
\qquad
\Re\langle -B_1B_0,\;B_0B_1\rangle_\sigma \ge 1-16\sqrt2\,\varepsilon_{\mathrm{norm}}.
$$

**Lemma 11.10 (notes).**

**Pure algebraic derivation of $E = U_A^*(X \otimes I) U_A$ (no matrix blocks)**

Let the ancilla be a qubit with:
- $P_0 := |0\rangle \langle 0|$, $P_1 := |1\rangle \langle 1|$
- $X := |0\rangle \langle 1| + |1\rangle \langle 0|$
- $Z := P_0 - P_1$
- Hadamard $H$ such that $H X H = Z$ and $H Z H = X$

For any reflection/observable $A$ with $A^2 = I$ and $A^* = A$, define the controlled gate as:
$$
C_A := P_0 \otimes I + P_1 \otimes A
$$

Assume the circuit form used in Lemma 11.10:
$$
U_A := (H \otimes I)\, C_{A_0} \, (H \otimes I)\, C_{A_1}
$$
Then
$$
E := U_A^* (X \otimes I)\, U_A
$$


⸻

Step 1: Conjugation by a controlled observable
Using only $P_iP_j=\delta_{ij}P_i$ and $P_0XP_0=P_1XP_1=0$, $P_0XP_1=|0\rangle\langle 1|$, $P_1XP_0=|1\rangle\langle 0|$:
$$
\begin{aligned}
C_A(X\otimes I)C_A
&=(P_0\otimes I + P_1\otimes A)(X\otimes I)(P_0\otimes I + P_1\otimes A)\\
&=(P_0XP_1)\otimes (IA) + (P_1XP_0)\otimes (AI)\\
&=X\otimes A.\tag{1}
\end{aligned}
$$


⸻

**Step 2: Conjugate $X$ through $U_A$ (work from inside out):**

1. **Conjugate by $C_{A_1}$ using (1):**
   $$
   \begin{aligned}
   C_{A_1}(X \otimes I) C_{A_1} &= X \otimes A_1
   \end{aligned}
   $$

2. **Conjugate by $(H \otimes I)$:**
   $$
   (H \otimes I)(X \otimes A_1)(H \otimes I) = (H X H) \otimes A_1 = Z \otimes A_1
   \tag{3}
   $$

3. **Conjugate by $C_{A_0}$ (projector algebra):**
   $$
   \begin{aligned}
   C_{A_0} (Z \otimes A_1) C_{A_0}
   &= (P_0 \otimes I + P_1 \otimes A_0) \big( (P_0 - P_1) \otimes A_1 \big) (P_0 \otimes I + P_1 \otimes A_0) \\
   &= P_0 \otimes A_1 - P_1 \otimes (A_0 A_1 A_0)
   \end{aligned}
   \tag{4}
   $$

4. **Conjugate by the outer $(H \otimes I)$, using**
   $$
   H P_0 H = \frac{I + X}{2}, \qquad H P_1 H = \frac{I - X}{2}
   \tag{5}
   $$
   Thus,
   $$
   \begin{aligned}
   E
   &= (H \otimes I) \Big[ P_0 \otimes A_1 - P_1 \otimes (A_0 A_1 A_0) \Big] (H \otimes I) \\
   &= \frac{I + X}{2} \otimes A_1 - \frac{I - X}{2} \otimes (A_0 A_1 A_0)
   \end{aligned}
   \tag{6}
   $$

---

**Final simplified form:**

Expanding (6):
$$
E = \frac{1}{2}\Big( I \otimes (A_1 - A_0 A_1 A_0) + X \otimes (A_1 + A_0 A_1 A_0) \Big)
\tag{7}
$$

This matches the block-matrix expansion, obtained purely from algebraic identities of $P_0, P_1, X, Z, H$, and the definition of $C_A$.


---

## Part II — Constructing the local isometries $V_A,V_B$ (11.3)

We build isometries
$$
V_A,V_B:\mathbb{C}^d\to \mathbb{C}^2\otimes\mathbb{C}^d
$$
by first defining unitaries $U_A,U_B$ on $\mathbb{C}^2\otimes\mathbb{C}^d$ and then setting the embeddings
$$
S:=|0\rangle\otimes I_d,\qquad
S_{\mathrm{aux}}:=|\mathrm{aux}\rangle\otimes I_d,
$$
and
$$
V_A:=U_A S,\qquad V_B:=U_B S_{\mathrm{aux}}.
$$
Let $|\Psi\rangle:=(V_A\otimes V_B)|\psi\rangle$.

### Alice: $U_A$ (as in the notes)

Define the padded state on $\mathbb{C}^2\otimes\mathbb{C}^d$:
$$
\rho:=|0\rangle\langle0|\otimes \sigma.
$$
The notes define a unitary $E$ (built from $A_0,A_1$ and a Hadamard on the ancilla) such that
$$
\Re\langle E,\; I\otimes A_1\rangle_\rho
= \frac12 + \frac12\,\Re\langle -A_1A_0,\;A_0A_1\rangle_\sigma
\ge 1-\frac{c\varepsilon_{\mathrm{norm}}}{2},
\quad c=16\sqrt2,
$$
and hence by Lemma 11.6
$$
\|E-I\otimes A_1\|_\rho^2\le c\varepsilon_{\mathrm{norm}}.
$$
From this they build $U_A$ and obtain the **vector-action** relations (Eqs. (217)–(220) of the notes):
$$
(V_A\otimes V_B)(A_0\otimes I)|\psi\rangle
= ((Z\otimes I_d)\otimes(I\otimes I_d))|\Psi\rangle,
$$
$$
\|(V_A\otimes V_B)(A_1\otimes I)|\psi\rangle
- ((X\otimes I_d)\otimes(I\otimes I_d))|\Psi\rangle\|
\le \sqrt{c\varepsilon_{\mathrm{norm}}}.
$$

### Bob: rewritten $U_B$ matching $(B_0,B_1)=(H,H')$ and using an auxiliary embedding

We now rewrite Bob’s canonical-form unitary so that **$B_0$ corresponds exactly to $H$** and **$B_1$ is close to $H'$**.

Let
$$
R:=\sin(\pi/8)X + \cos(\pi/8)Z
$$
so that
$$
R Z R^* = H,\qquad R X R^* = H'.
$$
Define the controlled-$B_0$ unitary on $\mathbb{C}^2\otimes\mathbb{C}^d$:
$$
C_{B_0}:=|0\rangle\langle0|\otimes I_d + |1\rangle\langle1|\otimes B_0.
$$
Then set
$$
U_B \;:=\; (R\otimes I_d)\, (C_{B_1} (H\otimes I_d) C_{B_0} (H\otimes I_d))\, (R^*\otimes I_d).
$$

#### Conjugation identities (the point of this choice)

Since 
$$
U_A^* (Z\otimes I_d) U_A = Z\otimes A_0,
$$
and the construction of $U_B$ is nothing but conjugating by $R$ and $R^*$, we have
$$
(R\otimes I_d) U_A^* (Z\otimes I_d) U_A (R^*\otimes I_d) = (R\otimes I_d) (Z\otimes A_0) (R^*\otimes I_d),
$$
$$
\implies (R\otimes I_d) U_A^* (R^*\otimes I_d) (R\otimes I_d) (Z\otimes I_d) (R^*\otimes I_d) (R\otimes I_d) U_A (R^*\otimes I_d) = (R\otimes I_d) (Z\otimes A_0) (R^*\otimes I_d),
$$
$$
\implies U_B^* (H\otimes I_d) U_B = H\otimes B_0,
$$

#### Choice of embedding $S_{\mathrm{aux}}$ so that $B_0$ is exact as $H$
To obtain an **exact** vector-action identity for $B_0$ with the target operator $H$ on the extracted qubit, we choose the auxiliary ancilla state
$$
|\mathrm{aux}\rangle:=R|0\rangle,
$$
and define
$$
S_{\mathrm{aux}}:=|\mathrm{aux}\rangle\otimes I_d,\qquad V_B:=U_B S_{\mathrm{aux}}.
$$
Then we have the intertwining relation
$$
(H\otimes I_d)\,V_B \;=\; V_B(B_0).
$$

#### Why $B_1$ becomes close to $H'$
The overlap bound for Bob (Corollary 11.8) is used in the notes exactly as for Alice: it produces a unitary $E_B$ on the padded space such that
$$
\|E_B - I\otimes B_1\|_\rho^2 \le c\varepsilon_{\mathrm{norm}}.
$$


### Summary of extracted vector-action relations (Eqs. (217)–(220))

Let $|\Psi\rangle=(V_A\otimes V_B)|\psi\rangle$. Then:
- **Exact for $A_0$:**
$$
\|(V_A\otimes V_B)(A_0\otimes I)|\psi\rangle
- ((Z\otimes I_d)\otimes(I\otimes I_d))|\Psi\rangle\|=0.
$$
- **Approximate for $A_1$:**
$$
\|(V_A\otimes V_B)(A_1\otimes I)|\psi\rangle
- ((X\otimes I_d)\otimes(I\otimes I_d))|\Psi\rangle\|
\le \sqrt{c\varepsilon_{\mathrm{norm}}}.
$$
- **Exact for $B_0$:**
$$
\|(V_A\otimes V_B)(I\otimes B_0)|\psi\rangle
- ((I\otimes I_d)\otimes(H\otimes I_d))|\Psi\rangle\|=0.
$$
- **Approximate for $B_1$:**
$$
\|(V_A\otimes V_B)(I\otimes B_1)|\psi\rangle
- ((I\otimes I_d)\otimes(H'\otimes I_d))|\Psi\rangle\|
\le \sqrt{c\varepsilon_{\mathrm{norm}}}.
$$

These relations are what let us replace the physical CHSH correlators by ideal correlators on the first two extracted qubits.


---

## Part III — Identifying the extracted two-qubit state (11.4)

### Step 1: translate CHSH value into a 2-qubit operator bound

Define the 2-qubit CHSH operator with the canonical choice
$$
A_0 = Z,\quad A_1 = X,\qquad
B_0 = \frac{Z+X}{\sqrt2}=H,\quad
B_1 = \frac{Z-X}{\sqrt2}=H'.
$$
Set
$$
K:=A_0\otimes B_0 + A_0\otimes B_1 + A_1\otimes B_0 - A_1\otimes B_1
= \sqrt2\,(Z\otimes Z + X\otimes X).
$$

Let $\widehat A_x:=V_AA_xV_A^*$ and $\widehat B_y:=V_BB_yV_B^*$ be the pushed observables on the enlarged spaces. Since $V_A,V_B$ are isometries, for all $x,y$,
$$
\langle\psi|A_x\otimes B_y|\psi\rangle=\langle\Psi|\widehat A_x\otimes\widehat B_y|\Psi\rangle.
$$
Using the vector-action bounds from Part II and a term-by-term replacement estimate (triangle inequality + Cauchy–Schwarz), we obtain
$$
\langle\Psi|\,(K\otimes I_{d^2})\,|\Psi\rangle
\ge 2\sqrt2 - 4\varepsilon_{\mathrm{norm}} - 4\sqrt{c\varepsilon_{\mathrm{norm}}},
\qquad c=16\sqrt2,
$$
equivalently
$$
\langle\Psi|\,(K\otimes I_{d^2})\,|\Psi\rangle
\ge 2\sqrt2 - \varepsilon - 2\sqrt{c\varepsilon}.
$$

### Step 2: spectral analysis of $K$ and the $v_1,v_2,v_3,v_4$

The Bell basis is
$$
|\Phi^\pm\rangle:=\frac{|00\rangle\pm |11\rangle}{\sqrt2},\qquad
|\Psi^\pm\rangle:=\frac{|01\rangle\pm |10\rangle}{\sqrt2}.
$$
For $K=\sqrt2\,(Z\otimes Z + X\otimes X)$, one checks
$$
K|\Phi^+\rangle=2\sqrt2\,|\Phi^+\rangle,\qquad
K|\Psi^-\rangle=-2\sqrt2\,|\Psi^-\rangle,\qquad
K|\Phi^-\rangle=0,\qquad
K|\Psi^+\rangle=0.
$$
So we take the orthonormal eigenbasis
$$
v_1:=|\Phi^+\rangle=\frac{|00\rangle+|11\rangle}{\sqrt2},\quad
v_2:=|\Phi^-\rangle=\frac{|00\rangle-|11\rangle}{\sqrt2},\quad
v_3:=|\Psi^+\rangle=\frac{|01\rangle+|10\rangle}{\sqrt2},\quad
v_4:=|\Psi^-\rangle=\frac{|01\rangle-|10\rangle}{\sqrt2}.
$$

### Step 3: from near-maximal expectation to closeness in norm

Using tensor reassociation
$$
(\mathbb{C}^2\otimes\mathbb{C}^d)\otimes(\mathbb{C}^2\otimes\mathbb{C}^d)
\cong (\mathbb{C}^2\otimes\mathbb{C}^2)\otimes(\mathbb{C}^d\otimes\mathbb{C}^d),
$$
we may write
$$
|\Psi\rangle = v_1\otimes|\eta_1\rangle + v_2\otimes|\eta_2\rangle + v_3\otimes|\eta_3\rangle + v_4\otimes|\eta_4\rangle,
$$
with $|\eta_j\rangle$ in the “junk” space, and set $p_j:=\|\eta_j\|^2$ so that $\sum_j p_j=1$. Then
$$
\langle\Psi|(K\otimes I)|\Psi\rangle = 2\sqrt2\,(p_1-p_4).
$$
If $\langle\Psi|(K\otimes I)|\Psi\rangle \ge 2\sqrt2-4\delta$ then
$$
p_1-p_4\ge 1-\sqrt2\,\delta
\quad\Rightarrow\quad
p_4\le \sqrt2\,\delta
\quad\Rightarrow\quad
p_1\ge 1-\sqrt2\,\delta.
$$

Let $\Pi:=|v_1\rangle\langle v_1|\otimes I$ and define the normalized junk state
$$
|\Phi_{\text{junk}}\rangle := \frac{(\langle v_1|\otimes I)|\Psi\rangle}{\|(\langle v_1|\otimes I)|\Psi\rangle\|}.
$$
Then $\|\Pi|\Psi\rangle\|^2=p_1$ and
$$
\||\Psi\rangle - v_1\otimes|\Phi_{\text{junk}}\rangle\|
\le \sqrt{2(1-p_1)}
\le \sqrt{2\sqrt2\,\delta}.
$$

**Concise justification of the factor $\sqrt{2(1-p_1)}$.**  
Let $|w\rangle:=v_1\otimes|\Phi_{\text{junk}}\rangle=\Pi|\Psi\rangle/\|\Pi|\Psi\rangle\|$. Then $\|w\|=\|\Psi\|=1$ and $\langle\Psi,w\rangle=\|\Pi|\Psi\rangle\|=\sqrt{p_1}$, hence
$$
\|\Psi-w\|^2 = \|\Psi\|^2+\|w\|^2-2\Re\langle\Psi,w\rangle
=2-2\sqrt{p_1}\le 2(1-p_1).
$$

Finally, we plug in $\delta=\varepsilon_{\mathrm{norm}}+\sqrt{c\varepsilon_{\mathrm{norm}}}$ coming from Step 1 to obtain the claimed $\sqrt{2\sqrt2\,\delta}$ bound in Theorem 11.1.

### Step 4: remove the residual local rotation on Bob (standard)

More generally, for other optimal CHSH measurement directions, the max-eigenvector can be $(I\otimes R_0)|\Phi^+\rangle$ for a single-qubit unitary $R_0$ on Bob’s extracted qubit. Absorb this by redefining Bob’s isometry as
$$
\widetilde V_B := (R_0^*\otimes I_d)V_B.
$$

---

## Part IV — Operator bullets (11.5 assembly)

From Part II we already have state-dependent relations on $|\psi\rangle$ (and similarly for Bob):
$$
(V_A\otimes V_B)(A_0\otimes I)|\psi\rangle
= ((Z\otimes I_d)\otimes(I\otimes I_d))|\Psi\rangle,
$$
$$
\|(V_A\otimes V_B)(A_1\otimes I)|\psi\rangle
- ((X\otimes I_d)\otimes(I\otimes I_d))|\Psi\rangle\|
\le \sqrt{c\varepsilon_{\mathrm{norm}}}.
$$
Combine these with the state-extraction bound
$$
\||\Psi\rangle-|\Phi^+\rangle\otimes|\Phi_{\text{junk}}\rangle\|\le \sqrt{2\sqrt2\,\delta}
$$
and triangle inequality. For example:
$$
\begin{aligned}
&\|(V_A\otimes V_B)(A_1\otimes I)|\psi\rangle - (X\otimes I)|\Phi^+\rangle\otimes|\Phi_{\text{junk}}\rangle\|\\
&\quad\le
\|(V_A\otimes V_B)(A_1\otimes I)|\psi\rangle - ((X\otimes I_d)\otimes(I\otimes I_d))|\Psi\rangle\|
+
\|((X\otimes I_d)\otimes(I\otimes I_d))\bigl(|\Psi\rangle-|\Phi^+\rangle\otimes|\Phi_{\text{junk}}\rangle\bigr)\|.
\end{aligned}
$$
The second term equals $\||\Psi\rangle-|\Phi^+\rangle\otimes|\Phi_{\text{junk}}\rangle\|$ because the operator is unitary, giving the theorem’s final constants. The other bullets are identical.
