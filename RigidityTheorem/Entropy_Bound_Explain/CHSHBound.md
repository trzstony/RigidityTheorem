# Entropy_Bound/CHSHBound.lean

## Theorem ([bellInfidelityAB\_le\_of\_chsh](../Entropy_Bound/CHSHBound.lean#L97))
- Theorem:
  $$
  2\sqrt 2-\varepsilon\ \le\ \operatorname{Re}\operatorname{Tr}(\mathrm{CHSH}\,\rho_{AB})
  \quad\Longrightarrow\quad
  \delta(\rho_{AB})\le \frac{\varepsilon}{2\sqrt 2},
  $$
  where $\delta(\rho_{AB})=1-\langle\Phi^+|\rho_{AB}|\Phi^+\rangle$.
- Hypotheses:
  1. $\rho_{AB}$ is a density operator on $A\otimes B$.
  2. $\varepsilon\in\mathbb R$.
  3. $2\sqrt 2-\varepsilon\le \operatorname{Re}\operatorname{Tr}(\mathrm{CHSH}\,\rho_{AB})$.
- Proof outline:
  expand $\operatorname{Re}\operatorname{Tr}(\mathrm{CHSH}\,\rho_{AB})$ in the Bell basis;
  write it as $2\sqrt 2\,(p-q)$ with $q\ge 0$;
  drop $q$, divide by $2\sqrt 2$, and rearrange to obtain the bound on $1-p$.
- Proved or not: ✅

## Theorem ([traceDistance\_of\_delta\_bound](../Entropy_Bound/CHSHBound.lean#L158))
- Theorem:
  $$
  D(\rho,\sigma)\le \sqrt\delta+\delta,
  \qquad
  \delta\le \frac{\varepsilon}{2\sqrt 2}
  \quad\Longrightarrow\quad
  D(\rho,\sigma)\le
  \sqrt{\frac{\varepsilon}{2\sqrt 2}}+\frac{\varepsilon}{2\sqrt 2}.
  $$
- Hypotheses:
  1. $H$ is finite-dimensional.
  2. $\rho,\sigma\in\mathcal L(H)$.
  3. $\delta,\varepsilon\in\mathbb R$.
  4. $D(\rho,\sigma)\le \sqrt\delta+\delta$.
  5. $\delta\le \frac{\varepsilon}{2\sqrt 2}$.
- Proof outline:
  use monotonicity of $\sqrt{\cdot}$ on $\mathbb R_{\ge 0}$, then add inequalities and compose with the assumed distance bound.
- Proved or not: ✅

## Theorem ([chsh\_to\_traceDistance\_bound](../Entropy_Bound/CHSHBound.lean#L177))
- Theorem:
  if
  $$
  2\sqrt 2-\varepsilon\le \operatorname{Re}\operatorname{Tr}(\mathrm{CHSH}\,\rho_{AB}),
  \qquad
  D(\rho,\sigma)\le \sqrt{\delta(\rho_{AB})}+\delta(\rho_{AB}),
  $$
  then
  $$
  D(\rho,\sigma)
  \le
  \sqrt{\frac{\varepsilon}{2\sqrt 2}}+\frac{\varepsilon}{2\sqrt 2}.
  $$
- Hypotheses:
  1. $\rho_{AB}$ is a density operator on $A\otimes B$.
  2. $\rho,\sigma$ are operators on a finite-dimensional space.
  3. $\varepsilon\in\mathbb R$.
  4. $2\sqrt 2-\varepsilon\le \operatorname{Re}\operatorname{Tr}(\mathrm{CHSH}\,\rho_{AB})$.
  5. $D(\rho,\sigma)\le \sqrt{\delta(\rho_{AB})}+\delta(\rho_{AB})$.
- Proof outline:
  apply the previous theorem giving $\delta(\rho_{AB})\le \varepsilon/(2\sqrt 2)$, then apply the substitution theorem for $D$.
- Proved or not: ✅

## Theorem ([distance\_bridge\_of\_measure\_contract\_and\_gentle](../Entropy_Bound/CHSHBound.lean#L200))
- Theorem:
  $$
  D(\rho_H,\sigma_H)\le D(\rho_K,\sigma_K),
  \qquad
  D(\rho_K,\sigma_K)\le \sqrt\delta+\delta
  \Longrightarrow
  D(\rho_H,\sigma_H)\le \sqrt\delta+\delta.
  $$
- Hypotheses:
  1. $H$ and $K$ are finite-dimensional.
  2. $\rho_H,\sigma_H\in\mathcal L(H)$ and $\rho_K,\sigma_K\in\mathcal L(K)$.
  3. $\delta\in\mathbb R$.
  4. $D(\rho_H,\sigma_H)\le D(\rho_K,\sigma_K)$.
  5. $D(\rho_K,\sigma_K)\le \sqrt\delta+\delta$.
- Proof outline:
  transitivity of $\le$.
- Proved or not: ✅

## File status
- lake env lean Entropy_Bound/CHSHBound.lean (March 9, 2026): passes.
- Overall status: all public theorems are fully proved.
