# Detailed Proof of Robust CHSH Rigidity


In this file, we formalize the robust CHSH rigidity theorem in detail, our proof follows Cleve's notes with some modifications.

**Theorem (Robust CHSH rigidity).**

Let $S = (|\psi\rangle, A_0, A_1, B_0, B_1)$ be an entangled strategy for the CHSH game.

Let $\varepsilon\ge 0$ be sufficiently small, suppose the bias satisfies
$$
\beta(S) \ge 2\sqrt{2}-\varepsilon.
$$

Then there exist local isometries $V_A:H_A\to \mathbb{C}^2\otimes H_A$ and $V_B:H_B\to \mathbb{C}^2\otimes H_B$ and a state $|\Phi_{\text{junk}}\rangle\in H_A\otimes H_B$ such that:
1. **State extraction.**
$$
\|(V_A\otimes V_B)|\psi\rangle - |\Phi^+\rangle\otimes |\Phi_{\text{junk}}\rangle\|
\in O(\sqrt\varepsilon),
\qquad
|\Phi^+\rangle:=\frac{|00\rangle+|11\rangle}{\sqrt2}.
$$

2. **Operator extraction for Alice.**
$$
\|(V_A\otimes V_B)(A_0\otimes I)|\psi\rangle - (Z\otimes I)|\Phi^+\rangle\otimes |\Phi_{\text{junk}}\rangle\|
\in O(\sqrt\varepsilon),
$$
$$
\|(V_A\otimes V_B)(A_1\otimes I)|\psi\rangle - (X\otimes I)|\Phi^+\rangle\otimes |\Phi_{\text{junk}}\rangle\|
\in O(\sqrt\varepsilon).
$$

3. **Operator extraction for Bob.**
$$
\|(V_A\otimes V_B)(I\otimes B_0)|\psi\rangle - (I\otimes H)\,|\Phi^+\rangle\otimes |\Phi_{\text{junk}}\rangle\|
\in O(\sqrt\varepsilon),
$$
$$
\|(V_A\otimes V_B)(I\otimes B_1)|\psi\rangle - (I\otimes H')\,|\Phi^+\rangle\otimes |\Phi_{\text{junk}}\rangle\|
\in O(\sqrt\varepsilon).
$$
The formalization proves explicit inequalities with concrete constants (omitted here for readability).



This is the robust self-testing statement for CHSH.  In the abstract CHSH framework, a strategy
is just a state together with four binary observables.

 The rigidity theorem specializes this
framework to the canonical target strategy
$$
A_0=Z,\qquad A_1=X,\qquad
B_0=H,\qquad B_1=H',
$$
and asserts that every near-optimal strategy must simulate this one approximately.

## Setup: Construction of the local isometries $V_A$ and $V_B$


Let the ancilla be a qubit with:
$$P_0 := |0\rangle \langle 0|, \quad P_1 := |1\rangle \langle 1|$$
Then $X := |0\rangle \langle 1| + |1\rangle \langle 0|,$ $Z = P_0 - P_1$
Hadamard $H$ satisfies $H X H = Z$ and $H Z H = X$.

For any gate $A$, define the controlled gate $C_A$ as:
$$
C_A := P_0 \otimes I + P_1 \otimes A.
$$


Define unitaries
$$
U_A=C_{A_1}(H\otimes I)C_{A_0}(H\otimes I),
\qquad
U_B=(R\otimes I)\,C_{B_1}(H\otimes I)C_{B_0}(H\otimes I)\,(R^{\dagger}\otimes I),
$$
Then the isometries $V_A : H_A \to \mathbb C^2\otimes H_A$ and $V_B : H_B \to \mathbb C^2\otimes H_B$ are constructed as:
$$
V_A:=U_A(\ket0\otimes I_{H_A}),
$$
$$
V_B:=U_B(\ket{\mathrm{aux}}\otimes I_{H_B}),
$$
where
$$
R=\sin(\pi/8)\,X+\cos(\pi/8)\,Z,
\qquad
RZR^{\dagger}=H,
\qquad
RXR^{\dagger}=H',
\qquad
\ket{\mathrm{aux}}=R\ket0.
$$
---

## Expansion of $V_A$ and $V_B$

### Setup


### Expansion of $V_A$

This follows directly from the definition
$$
V_A=U_A(\ket0\otimes I),
\qquad
U_A=C_{A_1}(H\otimes I)C_{A_0}(H\otimes I),
$$
by expanding the circuit step by step.

Here $\ket0\otimes M$ means the map
$$
x \mapsto \ket0\otimes Mx,
$$
and similarly for $\ket1\otimes M$.

Also recall
$$
C_A=|0\rangle\langle 0|\otimes I+|1\rangle\langle 1|\otimes A,
$$
so it acts trivially on the $\ket0$ branch and applies $A$ on the $\ket1$ branch.

Now compute:

$$
V_A
=
C_{A_1}(H\otimes I)C_{A_0}(H\otimes I)(\ket0\otimes I).
$$

First,
$$
(H\otimes I)(\ket0\otimes I)
=
H\ket0\otimes I
=
\frac{1}{\sqrt2}(\ket0+\ket1)\otimes I
=
\frac{1}{\sqrt2}\bigl(\ket0\otimes I+\ket1\otimes I\bigr).
$$

Then apply $C_{A_0}$:
$$
C_{A_0}\Bigl(\frac{1}{\sqrt2}(\ket0\otimes I+\ket1\otimes I)\Bigr)
=
\frac{1}{\sqrt2}\bigl(\ket0\otimes I+\ket1\otimes A_0\bigr).
$$

Now apply $H\otimes I$ again. Using
$$
H\ket0=\frac{\ket0+\ket1}{\sqrt2},
\qquad
H\ket1=\frac{\ket0-\ket1}{\sqrt2},
$$
we get
$$
(H\otimes I)(\ket0\otimes I)
=
\frac{1}{\sqrt2}(\ket0\otimes I+\ket1\otimes I),
$$
$$
(H\otimes I)(\ket1\otimes A_0)
=
\frac{1}{\sqrt2}(\ket0\otimes A_0-\ket1\otimes A_0).
$$
So
$$
(H\otimes I)C_{A_0}(H\otimes I)(\ket0\otimes I)
=
\frac12\Bigl(
\ket0\otimes(I+A_0)+\ket1\otimes(I-A_0)
\Bigr).
$$

Finally apply $C_{A_1}$. It leaves the $\ket0$ part unchanged and applies $A_1$ to the $\ket1$ part:
$$
V_A
=
\frac12\left(
\ket0\otimes(I+A_0)+\ket1\otimes A_1(I-A_0)
\right).
$$

This is exactly the expanded form of the circuit definition of $V_A$.


**Corollary.** By using the expansion of $V_A$, one can prove:
$$
(Z \otimes I) V_A=V_A A_0.
$$

---

### Expansion of $V_B$


Let
$$
U_A(B_0,B_1):=C_{B_1}(H\otimes I)C_{B_0}(H\otimes I),
\qquad
V_0:=U_A(B_0,B_1)(\ket0\otimes I).
$$
Then $V_B$ is obtained from $V_0$ by the rotation $R$:
$$
U_B=(R\otimes I)\,U_A(B_0,B_1)\,(R^\dagger\otimes I),
\qquad
V_B=U_B(\ket{\mathrm{aux}}\otimes I),
\qquad
\ket{\mathrm{aux}}=R\ket0.
$$

Since
$$
(R^\dagger\otimes I)(\ket{\mathrm{aux}}\otimes I)=\ket0\otimes I,
$$
we get
$$
V_B=(R\otimes I)V_0.
$$

So the real calculation is to expand $V_0=U_A(B_0,B_1)(\ket0\otimes I)$.

First,
$$
(H\otimes I)(\ket0\otimes I)
=\frac1{\sqrt2}\bigl(\ket0\otimes I+\ket1\otimes I\bigr).
$$

Apply $C_{B_0}$:
$$
C_{B_0}(H\otimes I)(\ket0\otimes I)
=\frac1{\sqrt2}\bigl(\ket0\otimes I+\ket1\otimes B_0\bigr).
$$

Apply $H\otimes I$ again:
$$
(H\otimes I)\frac1{\sqrt2}\bigl(\ket0\otimes I+\ket1\otimes B_0\bigr)
=
\frac12\Bigl(
\ket0\otimes(I+B_0)+\ket1\otimes(I-B_0)
\Bigr).
$$

Finally apply $C_{B_1}$:
$$
V_0
=
\frac12\Bigl(
\ket0\otimes(I+B_0)+\ket1\otimes B_1(I-B_0)
\Bigr).
$$

Therefore

$$
V_B=(R\otimes I)\,\left(\frac12\left(\ket0\otimes(I+B_0)+\ket1\otimes B_1(I-B_0)\right)\right).
$$

**Corollary.** By using the expansion of $V_B$, one can prove:
$$
(H \otimes I) V_B=V_B B_0.
$$

---




It remains to construct the state $\ket{\Phi_{\text {junk }}}$ and prove that $V_A, V_B$, and $\ket{\Phi_{\text {junk }}}$ satisfy the approximate relations.

From
$$
\beta:=\langle\psi|A_0\otimes B_0+A_0\otimes B_1+A_1\otimes B_0-A_1\otimes B_1|\psi\rangle
\ge 2\sqrt2-\varepsilon
$$
Let $c:=128\sqrt2$. Then we can obtain
$$
\bra{\psi}(A_0A_1+A_1A_0)^2\otimes I \ket{\psi} \le c\,\varepsilon,
\qquad
\bra{\psi}I \otimes (B_0B_1+B_1B_0)^2\ket{\psi} \le c\,\varepsilon.
$$

**(1) State extraction.**
Set
$$
\ket{\Psi}:=\operatorname{regSwap}\bigl((V_A\otimes V_B)\ket{\psi}\bigr)
\in (\mathbb C^2\otimes\mathbb C^2)\otimes(H_A\otimes H_B),
$$
where $\operatorname{regSwap}$ is the canonical linear isomorphism that regroups the tensor
factors.  This is needed because $(V_A\otimes V_B)\ket{\psi}$ naturally lies in
$(\mathbb C^2\otimes H_A)\otimes(\mathbb C^2\otimes H_B)$, whereas
$\ket{\Phi^+}\otimes\ket{\Phi_{\mathrm{junk}}}$ lies in
$(\mathbb C^2\otimes\mathbb C^2)\otimes(H_A\otimes H_B)$.

Let
$$
K=(Z\otimes H)+(Z\otimes H')+(X\otimes H)-(X\otimes H').
$$
This is exactly the canonical two-qubit CHSH operator introduced above, now acting on the
extracted qubit registers.
$$
\operatorname{CHSH}_{\mathrm{phys}}
:=\operatorname{regSwap}\bigl((V_A\otimes V_B)\operatorname{CHSH}\ket{\psi}\bigr),
\qquad
\operatorname{CHSH}_{\mathrm{ideal}}:=(K\otimes I)\ket{\Psi}.
$$
Term-by-term, one has
$$
\|\operatorname{CHSH}_{\mathrm{ideal}}-\operatorname{CHSH}_{\mathrm{phys}}\|
\le 4\sqrt{c\varepsilon},
$$
Indeed, writing both vectors as sums of the four CHSH correlator terms, the contributions are:
$$
\|w_{00}-v_{00}\|=0,\qquad
\|w_{01}-v_{01}\|\le \sqrt{c\varepsilon},
$$
$$
\|w_{10}-v_{10}\|\le \sqrt{c\varepsilon},\qquad
\|w_{11}-v_{11}\|\le 2\sqrt{c\varepsilon}.
$$

Here is what that line means mathematically.

Let
$$
\ket{\Psi_0}:=(V_A\otimes V_B)\ket{\psi}
\in (\mathbb C^2\otimes H_A)\otimes(\mathbb C^2\otimes H_B),
$$
and let
$$
\ket{\Psi}:=\operatorname{regSwap}\ket{\Psi_0}
\in (\mathbb C^2\otimes\mathbb C^2)\otimes(H_A\otimes H_B).
$$

Then the two CHSH-action vectors are:

$$
\operatorname{CHSH}_{\mathrm{phys}}
=
\operatorname{regSwap}\bigl((V_A\otimes V_B)\operatorname{CHSH}\ket{\psi}\bigr),
$$
and
$$
\operatorname{CHSH}_{\mathrm{ideal}}
=
(K\otimes I)\ket{\Psi}.
$$

Now decompose both into the four CHSH correlator terms.

$$
\operatorname{CHSH}_{\mathrm{phys}}=v_{00}+v_{01}+v_{10}-v_{11},
$$
where
$$
v_{00}:=\operatorname{regSwap}\bigl((V_A\otimes V_B)(A_0\otimes B_0)\ket{\psi}\bigr),
$$
$$
v_{01}:=\operatorname{regSwap}\bigl((V_A\otimes V_B)(A_0\otimes B_1)\ket{\psi}\bigr),
$$
$$
v_{10}:=\operatorname{regSwap}\bigl((V_A\otimes V_B)(A_1\otimes B_0)\ket{\psi}\bigr),
$$
$$
v_{11}:=\operatorname{regSwap}\bigl((V_A\otimes V_B)(A_1\otimes B_1)\ket{\psi}\bigr).
$$

And
$$
\operatorname{CHSH}_{\mathrm{ideal}}=w_{00}+w_{01}+w_{10}-w_{11},
$$
where
$$
w_{00}:=((Z\otimes H)\otimes I)\ket{\Psi},
\quad
w_{01}:=((Z\otimes H')\otimes I)\ket{\Psi},
$$
$$
w_{10}:=((X\otimes H)\otimes I)\ket{\Psi},
\quad
w_{11}:=((X\otimes H')\otimes I)\ket{\Psi}.
$$

The estimate is obtained by bounding each difference $w_{xy}-v_{xy}$.

**1. The $(0,0)$ term**
$$
\|w_{00}-v_{00}\|=0.
$$

Why: both $A_0$ and $B_0$ are extracted exactly:
$$
(Z\otimes I)V_A=V_AA_0,
\qquad
(H\otimes I)V_B=V_BB_0.
$$
So the ideal and physical vectors coincide exactly.

**2. The $(0,1)$ term**
$$
\|w_{01}-v_{01}\|\le \sqrt{c\varepsilon}.
$$

Why: $A_0$ is exact, but $B_1$ is only approximate. First apply the Bob approximation
$$
\|(H'\otimes I)V_B - V_BB_1\|_\tau \le \sqrt{c\varepsilon}.
$$
Then transport this through the exact/isometric $Z$-action on Alice. Since applying $Z$ does not change norms, the same error bound remains.

So this term costs one copy of $\sqrt{c\varepsilon}$.

**3. The $(1,0)$ term**
$$
\|w_{10}-v_{10}\|\le \sqrt{c\varepsilon}.
$$

Why: $B_0$ is exact, but $A_1$ is only approximate. First use
$$
\|(X\otimes I)V_A - V_AA_1\|_\sigma \le \sqrt{c\varepsilon},
$$
then transport through the exact/isometric $H$-action on Bob. Again the norm is preserved.

So this term also costs one copy of $\sqrt{c\varepsilon}$.

**4. The $(1,1)$ term**
$$
\|w_{11}-v_{11}\|\le 2\sqrt{c\varepsilon}.
$$

Why: now both sides are only approximate, so you pay twice.

A convenient intermediate vector is
$$
(X\otimes I)\bigl((I\otimes H')\ket{\Psi_0}\bigr).
$$
Then:
- replacing the physical $B_1$ by ideal $H'$ costs $\sqrt{c\varepsilon}$,
- replacing the physical $A_1$ by ideal $X$ costs another $\sqrt{c\varepsilon}$.

By triangle inequality,
$$
\|w_{11}-v_{11}\|
\le \sqrt{c\varepsilon}+\sqrt{c\varepsilon}
=2\sqrt{c\varepsilon}.
$$

**5. Sum the four bounds**

Now
$$
\operatorname{CHSH}_{\mathrm{ideal}}-\operatorname{CHSH}_{\mathrm{phys}}
=
(w_{00}-v_{00})+(w_{01}-v_{01})+(w_{10}-v_{10})-(w_{11}-v_{11}),
$$
so by triangle inequality,
$$
\|\operatorname{CHSH}_{\mathrm{ideal}}-\operatorname{CHSH}_{\mathrm{phys}}\|
\le
\|w_{00}-v_{00}\|
+\|w_{01}-v_{01}\|
+\|w_{10}-v_{10}\|
+\|w_{11}-v_{11}\|.
$$
Substitute the four bounds:
$$
\le 0+\sqrt{c\varepsilon}+\sqrt{c\varepsilon}+2\sqrt{c\varepsilon}
=4\sqrt{c\varepsilon}.
$$

So the whole estimate is really:

- exact term: $0$,
- one Bob-approximate term: $\sqrt{c\varepsilon}$,
- one Alice-approximate term: $\sqrt{c\varepsilon}$,
- one doubly-approximate term: $2\sqrt{c\varepsilon}$,

and these add up to
$$
4\sqrt{c\varepsilon}.
$$



Here $v_{xy}$ denotes the pushed physical term and $w_{xy}$ the corresponding ideal extracted-qubit
term.  The $A_0B_0$ contribution is exact because both $A_0$ and $B_0$ extract exactly; the
$A_0B_1$ and $A_1B_0$ terms each use one approximate extraction bound; and the $A_1B_1$ term
uses both approximate bounds, hence the factor $2$.  Summing these four estimates gives
$0+\sqrt{c\varepsilon}+\sqrt{c\varepsilon}+2\sqrt{c\varepsilon}=4\sqrt{c\varepsilon}$.

Let
$
\delta:=\varepsilon+4\sqrt{c\varepsilon}$.
Since $\ket{\Psi}$ is a unit vector, the preceding norm bound implies
$$
\Re\langle \Psi | \operatorname{CHSH}_{\mathrm{ideal}} \rangle
\ge
\Re\langle \Psi | \operatorname{CHSH}_{\mathrm{phys}} \rangle - 4\sqrt{c\varepsilon}.
$$
Using $\operatorname{CHSH}_{\mathrm{ideal}}=(K\otimes I)\ket{\Psi}$,
$\Re\langle \Psi | \operatorname{CHSH}_{\mathrm{phys}} \rangle=\beta$, and
$\beta\ge 2\sqrt2-\varepsilon$, we obtain
$$
\Re\langle \Psi | (K\otimes I) | \Psi\rangle \ge 2\sqrt2-\delta.
$$
We now expand $\ket{\Psi}$ in the Bell basis and use the spectral decomposition of $K$.
$$
\ket{\Psi}=\sum_{j=0}^3 \ket{\mathrm{Bell}_j}\otimes \eta_j,
\qquad
\Re\langle \Psi | (K\otimes I) | \Psi\rangle
=2\sqrt2\,(\|\eta_0\|^2-\|\eta_3\|^2),
$$
Let $\ket{\Phi_{\mathrm{junk}}}$ be the normalized $0$-th Bell component, so that
$\ket{\Phi^+}\otimes\ket{\Phi_{\mathrm{junk}}}$ is the projection of $\ket{\Psi}$ onto the
$\ket{\Phi^+}$-eigenspace. Since $\|\ket{\Psi}\|=1$ and
$\Re\langle \Psi \mid \Phi^+\otimes\Phi_{\mathrm{junk}}\rangle=\|\eta_0\|$, we have
$$
\|\ket{\Psi}-\ket{\Phi^+}\otimes\ket{\Phi_{\mathrm{junk}}}\|^2
\le 2-2\|\eta_0\|
\le 2(1-\|\eta_0\|^2),
$$
because $0\le \|\eta_0\|\le 1$. Hence
$$
\|\ket{\Psi}-\ket{\Phi^+}\otimes\ket{\Phi_{\mathrm{junk}}}\|
\le \sqrt{2(1-\|\eta_0\|^2)}.
$$
Moreover, from
$$
2\sqrt2\,(\|\eta_0\|^2-\|\eta_3\|^2)\ge 2\sqrt2-\delta
$$
and $\|\eta_3\|^2\ge 0$, we obtain
$$
1-\|\eta_0\|^2 \le \frac{\delta}{2\sqrt2}.
$$
Combining these estimates yields
$$
\|\ket{\Psi}-\ket{\Phi^+}\otimes\ket{\Phi_{\mathrm{junk}}}\|
\le \sqrt{\delta/\sqrt2}.
$$

**(2) Operator extraction for Alice.**
For $A_0$, the intertwining relation is exact, while for $A_1$ we use the approximate
extraction bound coming from the anticommutator estimate.  Applying these identities to
$\ket{\psi}$, and then transporting them through $\operatorname{regSwap}$, gives
$$
(Z\otimes I)V_A = V_AA_0,
\qquad
\Bigl\| \bigl((((X\otimes I)V_A - V_AA_1)\otimes I)\ket{\psi}\bigr) \Bigr\|
\le \sqrt{c\varepsilon}.
$$
Then
$$
\operatorname{regSwap}\bigl((V_A\otimes V_B)(A_0\otimes I)\ket{\psi}\bigr)
=((Z\otimes I)\otimes I)\ket{\Psi},
$$
so in particular the exact extraction error for $A_0$ is
$$
\Bigl\|\operatorname{regSwap}\bigl((V_A\otimes V_B)(A_0\otimes I)\ket{\psi}\bigr)
-((Z\otimes I)\otimes I)\ket{\Psi}\Bigr\|=0.
$$
$$
\Bigl\|\operatorname{regSwap}\bigl((V_A\otimes V_B)(A_0\otimes I)\ket{\psi}\bigr)
-((Z\otimes I)\otimes I)\bigl(\ket{\Phi^+}\otimes\ket{\Phi_{\mathrm{junk}}}\bigr)\Bigr\|
\le \sqrt{\delta/\sqrt2},
$$
$$
\Bigl\|\operatorname{regSwap}\bigl((V_A\otimes V_B)(A_1\otimes I)\ket{\psi}\bigr)
-((X\otimes I)\otimes I)\ket{\Psi}\Bigr\|
\le \sqrt{c\varepsilon},
$$
$$
\|((X\otimes I)\otimes I)(\ket{\Psi}-\ket{\Phi^+}\otimes\ket{\Phi_{\mathrm{junk}}})\|
\le \sqrt{\delta/\sqrt2},
$$
Here the exact identity for $A_0$ gives zero error relative to $\ket{\Psi}$, and the displayed
bound relative to $\ket{\Phi^+}\otimes\ket{\Phi_{\mathrm{junk}}}$ follows by combining this with
the state-extraction estimate.  Likewise, the second and third bounds use the approximate
extraction estimate for $A_1$, together with the fact that $((X\otimes I)\otimes I)$ is an
isometry, and then apply the triangle inequality.
$$
\Bigl\|\operatorname{regSwap}\bigl((V_A\otimes V_B)(A_1\otimes I)\ket{\psi}\bigr)
-((X\otimes I)\otimes I)\bigl(\ket{\Phi^+}\otimes\ket{\Phi_{\mathrm{junk}}}\bigr)\Bigr\|
\le \sqrt{c\varepsilon}+\sqrt{\delta/\sqrt2}.
$$

**(3) Operator extraction for Bob.**
The argument for Bob is identical, with $H$ extracted exactly and $H'$ extracted
approximately.
$$
\!(H\otimes I)V_B = V_BB_0,
\qquad
\Bigl\| \bigl((I\otimes ((H'\otimes I)V_B - V_BB_1))\ket{\psi}\bigr) \Bigr\|
\le \sqrt{c\varepsilon}.
$$
$$
\operatorname{regSwap}\bigl((V_A\otimes V_B)(I\otimes B_0)\ket{\psi}\bigr)
=((I\otimes H)\otimes I)\ket{\Psi},
$$
so in particular the exact extraction error for $B_0$ is
$$
\Bigl\|\operatorname{regSwap}\bigl((V_A\otimes V_B)(I\otimes B_0)\ket{\psi}\bigr)
-((I\otimes H)\otimes I)\ket{\Psi}\Bigr\|=0.
$$
$$
\Bigl\|\operatorname{regSwap}\bigl((V_A\otimes V_B)(I\otimes B_0)\ket{\psi}\bigr)
-((I\otimes H)\otimes I)\bigl(\ket{\Phi^+}\otimes\ket{\Phi_{\mathrm{junk}}}\bigr)\Bigr\|
\le \sqrt{\delta/\sqrt2}.
$$
$$
\Bigl\|\operatorname{regSwap}\bigl((V_A\otimes V_B)(I\otimes B_1)\ket{\psi}\bigr)
-((I\otimes H')\otimes I)\ket{\Psi}\Bigr\|
\le \sqrt{c\varepsilon},
$$
$$
\|((I\otimes H')\otimes I)(\ket{\Psi}-\ket{\Phi^+}\otimes\ket{\Phi_{\mathrm{junk}}})\|
\le \sqrt{\delta/\sqrt2},
$$
Again, the exact identity for $B_0$ gives zero error relative to $\ket{\Psi}$, and the
displayed bound relative to $\ket{\Phi^+}\otimes\ket{\Phi_{\mathrm{junk}}}$ follows by combining
this with the state-extraction estimate.  The $B_1$ bound is then obtained by combining the
approximate extraction estimate with the same closeness bound and applying the triangle inequality.
$$
\Bigl\|\operatorname{regSwap}\bigl((V_A\otimes V_B)(I\otimes B_1)\ket{\psi}\bigr)
-((I\otimes H')\otimes I)\bigl(\ket{\Phi^+}\otimes\ket{\Phi_{\mathrm{junk}}}\bigr)\Bigr\|
\le \sqrt{c\varepsilon}+\sqrt{\delta/\sqrt2}.
$$
Since $\operatorname{regSwap}$ is an isometry, these are equivalent to the four bounds stated in
Theorem~\ref{thm:robust-chsh-rigidity}.
\end{proof}
