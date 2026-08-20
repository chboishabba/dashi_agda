# Yang–Mills Combes–Thomas provenance and scope audit

Date of this audit: 2026-08-06.
## Purpose
This document records the public chronology, source classification, and theorem-scope boundary for DASHI's finite-volume Combes–Thomas work. It is a provenance guard, not an accusation of copying and not a mathematical source.
## Public chronology presently observable
1. The public repository `lluiseriksson/THE-ERIKSSON-PROGRAMME` contains commit `9dd50bbad9f73356c18643a671e197ac430d66a3`, dated 2026-07-12, introducing a physical-cochain Combes–Thomas chain with files such as `PhysicalCoerciveCombesThomas.lean` and later `PhysicalCoerciveCombesThomasInverse.lean`.
2. Lluis Eriksson's *The Volume-Uniform Poincaré Walls: Machine-Checked Obstructions for Flat and Fluctuation-Sector Block-Poincaré Routes to Combes–Thomas Coercivity in Lattice Yang–Mills* was submitted to ai.viXra as `2607.0042` on 2026-07-14. It reports a fixed-volume positive Combes–Thomas substrate and negative results for two particular unscaled volume-uniform Poincaré gates.
3. The first presently located public DASHI commit with “Combes-Thomas” in its commit message is `d87f71494c47e6e96f6b9815a16f7b0a43cc012d`, dated 2026-07-27, titled `Add Combes-Thomas physical Green decay reduction`.
4. Later DASHI rounds replaced the original abstract carrier with exact rational finite-dimensional conjugation, Schur, half-gap, basis-entry, and physical promotion modules.
The public external implementation therefore predates the first presently located public DASHI Combes–Thomas commit. Public dates alone cannot establish either dependence or independence. Any submission-facing account should say exactly that.
## Structural overlap actually observed
The external repository and DASHI both use the standard chain
```text
finite range/locality
→ weighted diagonal conjugation
→ Schur or row-count perturbation bound
→ survival of coercivity under the tilt
→ tilted inverse bound
→ kernel-entry exponential decay.
```
This architecture is already suggested by the classical Combes–Thomas estimate and by Bałaban's propagator programme. Structural convergence on that chain is therefore unsurprising.
The external repository uses identifiers such as:
- `PhysicalCoerciveCombesThomas.lean`;
- `PhysicalCoerciveCombesThomasInverse.lean`;
- `PhysicalShellCombesThomasEndpoint.lean`;
- `flatGaugeFixedCovariance_CT_fixedVolume`.
DASHI uses identifiers such as:
- `BalabanP33FiniteCombesThomasConjugationExact.agda`;
- `BalabanP33PhysicalCombesThomasSchurExact.agda`;
- `BalabanP33PhysicalCombesThomasEntryDecayExact.agda`;
- `BalabanP33PhysicalCombesThomasQuadraticEndgameExact.agda`.
An exact code search on 2026-08-06 found no occurrence of the distinctive DASHI prefix `BalabanP33` in the external repository. This is evidence against direct identifier-level copying, but it is not proof of independent development.
## Source classification
### Primary mathematical authorities
These may support theorem statements and Agda source headers:
- J. M. Combes and L. Thomas, *Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger Operators*, Communications in Mathematical Physics 34 (1973), 251–270. DOI `10.1007/BF01646473`.
- Tadeusz Bałaban, *Propagators and Renormalization Transformations for Lattice Gauge Theories. I*, Communications in Mathematical Physics 95 (1984), 17–40. DOI `10.1007/BF01215753`.
- Tadeusz Bałaban, *Propagators and Renormalization Transformations for Lattice Gauge Theories. II*, Communications in Mathematical Physics 96 (1984), 223–250. DOI `10.1007/BF01240221`.
- Tadeusz Bałaban, *Propagators for Lattice Gauge Theories in a Background Field*, Communications in Mathematical Physics 99 (1985), 389–434. DOI `10.1007/BF01240355`.
- J. Dimock, *The Renormalization Group According to Balaban III. Convergence*, Annales Henri Poincaré 15 (2014), 2133–2175. DOI `10.1007/s00023-013-0303-3`.
- J. Dimock, *Ultraviolet Regularity for QED in d=3*, Journal of Mathematical Physics 59 (2018), 012301. DOI `10.1063/1.5009458`.
### External stress tests only
The Eriksson ai.viXra paper and repository are useful for adversarial comparison, especially their explicit fixed-volume/uniformity guard and square-wave obstruction. They are not used as authority for DASHI theorems. Where they trigger a new DASHI theorem, that fact is disclosed in comments and the theorem is rederived independently over DASHI's exact rational carrier.
Other self-published or rapidly revised claimed Yang–Mills proofs are not accepted as theorem sources merely because they suggest Holley–Stroock, orbit-space curvature, terminal-scale gaps, or a formula such as `m_{n+1}=2m_n`. Each such ingredient remains conditional until connected to the repository's actual RG map.
## Scope correction implemented in round 23
`BalabanP33UnscaledCyclePoincareWallExact.agda` independently constructs the half-period square wave on the even cycle. It proves:
mean = 0,
norm² = 2M,
cyclic nearest-neighbour energy = 8.
For `M=256`, a bare volume-uniform coercivity constant `1/32` would imply `16 ≤ 8`, which is impossible. This blocks only the unscaled bare uniform promotion. It does not invalidate the literal side-four Poincaré theorem or the finite-volume Combes–Thomas theorem.
`BalabanP33TerminalScaleGapPullbackExact.agda` then proves the exact algebra required by a terminal-scale route. Each physical RG step must establish
m_{j+1} ≤ 2 m_j + ε_j.
Only then may one pull back
(m_{j+1}-ε_j)/2 ≤ m_j
and compose the discounted terminal floor and losses. No dynamic mass generation or gap-preservation law is assumed.
## Hopping-parameter expansion
Wilson-fermion hopping-parameter expansions control a fermionic determinant in a small-κ regime. They are legitimate lattice-QCD tools but do not prove the pure-gauge bosonic Hessian estimates currently needed by DASHI. They remain outside the present pure Yang–Mills priority unless dynamical fermions are added.
## Submission-facing rule
A future paper or README should describe DASHI's result as:
> an exact finite-volume rational Combes–Thomas implementation, cross-checked against an external public Lean programme and explicitly prevented from being promoted to a bare volume-uniform gap without an RG-scale transfer theorem.
It should not claim independent discovery solely from public dates, should not imply that the external negative result proves a universal Yang–Mills no-go theorem, and should not cite self-published stress tests in place of Combes–Thomas, Bałaban, or peer-reviewed RG sources.
> an exact finite-volume rational Combes–Thomas implementation, independently checked against an external public Lean programme and explicitly prevented from being promoted to a bare volume-uniform gap without an RG-scale transfer theorem.
