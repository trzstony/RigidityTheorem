# Entropy_Bound/Infra.lean

## Theorem ([decisionOp\_isEffect\_fin2](../Entropy_Bound/Infra.lean#L246))
- Theorem:
  $$
  \Pi_M:=\sum_{x\in\{0,1\}} |x\rangle\!\langle x|\otimes M_x
  \quad\text{is an effect, i.e.}\quad
  \Pi_M\succeq 0,\ I-\Pi_M\succeq 0.
  $$
- Hypotheses:
  1. $E$ is finite-dimensional.
  2. $M$ is a binary POVM on $E$.
- Proof outline:
  prove positivity of $\Pi_M$ and positivity of its complement separately, then combine.
- Proved or not: ✅

## Theorem ([re\_trace\_mul\_le\_re\_trace\_of\_isPositive\_of\_isEffectLike](../Entropy_Bound/Infra.lean#L351))
- Theorem:
  $$
  A\succeq 0,\ I-B\succeq 0
  \Longrightarrow
  \operatorname{Re}\operatorname{Tr}(BA)
  \le
  \operatorname{Re}\operatorname{Tr}(A).
  $$
- Hypotheses:
  1. $H$ is finite-dimensional.
  2. $A,B\in\mathcal L(H)$.
  3. $A\succeq 0$.
  4. $I-B\succeq 0$.
- Proof outline:
  show nonnegativity of $\operatorname{Re}\operatorname{Tr}((I-B)A)$, expand linearly, rearrange.
- Proved or not: ✅

## Theorem ([re\_trace\_mul\_le\_traceDistance\_of\_isEffect\_of\_density\_diff](../Entropy_Bound/Infra.lean#L552))
- Theorem:
  $$
  0\preceq B\preceq I
  \Longrightarrow
  \operatorname{Re}\operatorname{Tr}\bigl(B(\rho-\sigma)\bigr)
  \le
  D(\rho,\sigma),
  $$
  for density operators $\rho,\sigma$.
- Hypotheses:
  1. $H$ is finite-dimensional.
  2. $B$ is an effect ($0\preceq B\preceq I$).
  3. $\rho$ and $\sigma$ are density operators on $H$.
- Proof outline:
  set $\Delta=\rho-\sigma$, prove $\Delta$ Hermitian and traceless, apply the internal half-trace-norm bound, rewrite as trace distance.
- Proved or not: ✅

## Theorem ([abs\_re\_trace\_mul\_le\_traceDistance\_of\_isEffect\_of\_density\_diff](../Entropy_Bound/Infra.lean#L590))
- Theorem:
  $$
  \bigl|\operatorname{Re}\operatorname{Tr}(B(\rho-\sigma))\bigr|
  \le D(\rho,\sigma).
  $$
- Hypotheses:
  1. $H$ is finite-dimensional.
  2. $B$ is an effect ($0\preceq B\preceq I$).
  3. $\rho$ and $\sigma$ are density operators on $H$.
- Proof outline:
  prove upper bound directly and lower bound by swapping $\rho$ and $\sigma$; conclude with $|x|\le a\iff -a\le x\le a$.
- Proved or not: ✅

## Theorem ([trace\_variational\_decisionOp\_fin2](../Entropy_Bound/Infra.lean#L653))
- Theorem:
  $$
  \operatorname{Re}\operatorname{Tr}\bigl(\Pi_M(\rho-\sigma)\bigr)
  \le
  \frac12\|\rho-\sigma\|_1,
  $$
  where $\Pi_M=\sum_x |x\rangle\!\langle x|\otimes M_x$.
- Hypotheses:
  1. $E$ is finite-dimensional.
  2. $M$ is a binary POVM on $E$.
  3. $\rho$ and $\sigma$ are density operators on $(\mathbb C^2)\otimes E$.
- Proof outline:
  define $\Delta=\rho-\sigma$, establish Hermitian/traceless properties, use effect property of $\Pi_M$, and apply the generic effect variational bound.
- Proved or not: ✅

## Theorem ([trace\_variational\_decisionOp\_fin2\_abs](../Entropy_Bound/Infra.lean#L703))
- Theorem:
  $$
  \left|\operatorname{Re}\operatorname{Tr}\bigl(\Pi_M(\rho-\sigma)\bigr)\right|
  \le
  \frac12\|\rho-\sigma\|_1.
  $$
- Hypotheses:
  1. $E$ is finite-dimensional.
  2. $M$ is a binary POVM on $E$.
  3. $\rho$ and $\sigma$ are density operators on $(\mathbb C^2)\otimes E$.
- Proof outline:
  combine one-sided bounds for $(\rho,\sigma)$ and $(\sigma,\rho)$.
- Proved or not: ✅

## Theorem ([isometry\_traceNorm](../Entropy_Bound/Infra.lean#L789))
- Theorem:
  $$
  \|eXe^{-1}\|_1=\|X\|_1
  $$
  for a linear isometry equivalence $e$.
- Hypotheses:
  1. $H$ and $K$ are finite-dimensional.
  2. $e:H\simeq K$ is a linear isometry equivalence.
  3. $X\in\mathcal L(H)$.
- Proof outline:
  direct use of the library theorem for trace norm under conjugation by a linear isometry equivalence.
- Proved or not: ✅

## Theorem ([unitary\_traceNorm](../Entropy_Bound/Infra.lean#L803))
- Theorem:
  $$
  \|uXu^\dagger\|_1=\|X\|_1
  $$
  for unitary $u$.
- Hypotheses:
  1. $H$ is finite-dimensional.
  2. $u$ is unitary on $H$.
  3. $X\in\mathcal L(H)$.
- Proof outline:
  direct use of the library theorem for unitary conjugation invariance of trace norm.
- Proved or not: ✅

## File status
- lake env lean -DmaxHeartbeats=4000000 Entropy_Bound/Infra.lean (March 9, 2026): passes.
- lake env lean Entropy_Bound/Infra.lean with default heartbeat budget: fails at line 403 due to heartbeat limit.
- Overall status: theorem scripts are verified when run with a higher heartbeat budget.
