# Horned SU(3) — high-yield physical steelman and regularity Pareto cut
**24 October 2026 | decision-grade cross-PR roadmap**

Primary target [neutrino #1247](https://github.com/chboishabba/dashi_agda/pull/1247);
horn topology owner [#1244](https://github.com/chboishabba/dashi_agda/pull/1244);
KK/holonomy consumer [#1241](https://github.com/chboishabba/dashi_agda/pull/1241).
This replaces "seek any SU(3) representation" as the main physics goal.
Do **not** promote a source-written Agda proof to Agda kernel verification,
nor a toy qutrit transport calculation to a physical neutrino effect.

## Provenance and exact scope

- Alexander (1924) original wild sphere; Hatcher, *Algebraic Topology*
  Example 2B.2 (the original injective binary commutator tower);
  Hatcher's abstract \(G_A\) is not the already-unverified smooth
  geometric three-copy wild exterior.
- Morikuni Gotô (1949), *J. Math. Soc. Japan* **1**, 270–272,
  DOI **10.2969/jmsj/00130270**: each element of ambient connected
  compact semisimple SU(3) is a group commutator. This proves **abstract
  existence**, not global compactness/commutator closure of the
  countable \(SU(3,Q(ζ_3))\) subgroup.
- Wilson, Aharonov–Bohm and non-Abelian gauge holonomy: existing
  canonical DASHI owners `SUNWilsonClassFunction`,
  `SUNWilsonAction`, `CompactLieLatticeGauge`, `SUNMatrixCarrier`.
  The gauge-invariant Wilson class function already exists;
  do NOT implement a new Wilson action.
- **Experimental/engineering precedents—not horned-lepton evidence:**
  non-Abelian gauge field optics, *Nature Communications* (2019),
  https://doi.org/10.1038/s41467-019-10974-8;
  Sugawa et al. *npj Quantum Information* (2021), Wilson/Wilczek–Zee
  measurements in a synthetic SU(2) system,
  https://doi.org/10.1038/s41534-021-00483-2;
  Lucas et al., *Nature Physics* (2026), dynamical Z2 lattice-loop
  Aharonov–Bohm simulation,
  https://doi.org/10.1038/s41567-026-03400-6.
- **Selection donor:** Y. Hosotani, *Annals of Physics* **190**
  (1989), 233, DOI **10.1016/0003-4916(89)90015-8**; Wilson-line
  effective-potential selection requires **matter fields, boundary
  conditions and a renormalized spectrum**. Existing historical
  Hosotani calculations are on specified compact/smooth topologies,
  not automatically on the horned wild complement.
- Existing analysis donor `DASHI/Geometry/FlatFormalDiskHolonomySurface.agda`
  explicitly leaves normed completion, holonomy-to-identity,
  non-Abelian Stokes and regularity statements OPEN; leverage,
  do not promote an imported analytic hypothesis to proof.
  `DASHI/Physics/Closure/AnomalyCancellationTableReceipt.agda`
  also holds **conditional** SM anomaly authority—not a certified
  new chiral flavour-gauge anomaly cancellation.

## Maximum information: three distinct observable thresholds

**T0: nontrivial single-loop class function, not horn-specific.**
For the original POST-HOC leptonic algebraic root
\(W=T(2|u_1\rangle\langle u_1|-I)\), the exact
\(\mathbb Q(ζ_3)\) trace is

```
Tr_3(W) =
 (176093404722400 - 19836986431118 ζ)
 /181846007130841
Tr_{Q(ζ)/Q}(Tr_3 W) =
  372023795875918/181846007130841
Re(Tr_3 W) ≈ 1.0229088934799684
Im(Tr_3 W) ≈ -0.0944718801085063.
```

A **specified** unpolarized vectorlike qutrit, two 50:50 path
interferometer with transports \(U_1=I,U_2=W\),
controlled relative path phase \(\phi\), and identity input
density \(\rho=I/3\) predicts

\[
P_+(\phi)=\tfrac12\big[1+
 \operatorname{Re}(e^{i\phi}\operatorname{tr}W/3)\big].
\]

At \(\phi=0\),

```
P_+(0)=434928608401/648677790003
      ≈0.670484815579995,
fringe visibility |Tr W|/3≈0.342420719208865.
trivial holonomy W=I yields P_+(0)=1.
```

This **is** gauge invariant under simultaneous endpoint gauge
transforms: the loop ratio \(U_1^†U_2\) transforms by conjugation.
It distinguishes **chosen W vs identity**, but NOT W vs
\(TWT^{-1}\), the earlier physical row-rephasing equivalence.
More damaging to any horn-specific inference:
an ordinary annulus/\(\pi_1(S^1)=\mathbb Z\) admits
\(\rho(1)=W\) with the identical single-loop signal.
Thus any purported "horned physics" inferred from ONE Wilson
character is intrinsically underdetermined.

**T1: genuine non-Abelian, but still not wild-specific.**
Choose \(X,Y\in SU(3)\) by Gotô so that \([X,Y]=W\).
Because \(W\ne I\), they **cannot commute**.
Their gauge-invariant commutator-loop character
\(\operatorname{Tr}([X,Y])=\operatorname{Tr}(W)\ne3\).
The original Schur cyclic permutation construction locally
verified this, with \(\|XY-YX\|_{op}\approx1.43818847527\).
This is a legitimate *non-Abelian interferometry* target.
However \(F_2\), the ordinary free group on two loops,
can reproduce ANY pair \(X,Y\) and its commutator.
One stage still does NOT identify a horned embedding.

**T2: horn-specific hierarchy or substantive obstruction.**
Hatcher's source relations require **all** depths:

\[
m_w=[m_{w0},m_{w1}].
\]

To discriminate horn topology from a generic puncture/free group,
demand mutually compatible multi-scale paths and holonomies on an
**identified geometric source**, not merely a finite circuit
satisfying a few commutator equations.

## Strongest new candidate theorem: uniform shrinking horns rule out a bounded connection

For a unitary matrix, let \(d(U)=\|U-I\|_{op}\).
The exact elementary estimate is

\[
d([X,Y])\le 2d(X)d(Y).
\]

If every leaf at depth n obeys \(d(U_w)\le\epsilon_n\),
recursive commutator multiplication yields

\[
\boxed{d(W)\le
 2^{2^n-1}\epsilon_n^{2^n}
 =\tfrac12(2\epsilon_n)^{2^n}.}
\]

Conversely, a **fixed nontrivial root** with \(d(W)=\delta>0\)
requires, at every depth n, *at least one* leaf with

\[
\boxed{d(U_w)\ge
 \tfrac12(2\delta)^{1/2^n}\longrightarrow\tfrac12.}
\]

For the chosen W, independent NumPy operator-norm evaluation yields
\(\delta\approx1.4381884752669252\).
Hence a consistent nontrivial representation has deeply refined
descendants with holonomy uniformly bounded away from identity.

**CONDITIONAL geometric regularity input:** suppose each generator
at depth n has a local loop representative (up to unitary
common-basepoint transport conjugation) of length at most
\(\ell_n\to0\) and a connection bounded by
\(M\) in compatible local trivializations. Then unitary
parallel transport obeys \(d(U_w)\le M\ell_n\).
These hypotheses imply every depth-n leaf is close to I,
contradicting the fixed-root lower bound.

If \(\ell_n\le L_0q^n\), 0<q<1, this requires

\[
M\ge
\frac{(2\delta)^{1/2^n}}{2L_0q^n}
\sim \frac{q^{-n}}{2L_0}.
\]

So either the purported geometric model does NOT have
uniformly shrinking representatives, OR no compatible
uniformly bounded/smooth-extendible connection can carry
this nontrivial root holonomy, OR the proposed exact
commutator identifications/physical loops are wrong.
**The first hypothesis has NOT been proved for the actual
three-copy wild embedding.** This is a conditional, potentially
publishable analytical no-go, not an unconditional impossibility
theorem for all flat holonomies on noncompact manifolds.
It does NOT say a flat exterior connection is necessarily
infinite-energy; singular boundary/defect energy and proper
domains require independent source analysis.

A more invariant formulation emphasizes **uniform small-loop
holonomy tending to identity**, without pretending the
gauge-dependent numerical potential bound is itself observable.

## Why classical flat Yang–Mills does not pay holonomy selection

The classical pure YM action
\(S_{YM}\propto\int\mathrm{tr}(F\wedge *F)\) is zero
on all flat connections \(F=0\).
So the classical local curvature energy and local gauge-field stress
in the exterior cannot choose the selected W over another flat W.
Nor can the flat exterior alone source nonzero local
Einstein/Kaluza–Klein stress there. Nontrivial singular defects
may carry separate physical stress/energy, to be calculated.

**Most promising positive selection route:** a Wilson-line
effective potential/eigenvalue problem of the Hosotani type,
derived from a **specific vectorlike matter representation and
global geometry**, not a hand-picked \(V(W)\).
As a quantitative control, a three-component vectorlike field
on the ordinary circle of circumference L=1 has covariant
Laplacian eigenvalues
\(\lambda_{n,j}=(2\pi n+\theta_j)^2\),
\(e^{i\theta_j}\in\mathrm{spec}(W)\).
With the chosen W, the eigenphases are approximately

```
(-1.50905650,-0.09593953,+1.60499604).
```

Its heat trace at t=0.2 is \(2.25351710695\), vs
\(3.00223408384\) for trivial holonomy. This is a
**sourced synthetic S1 spectrum**, NOT an already-derived
renormalized effective potential, a wild-horn manifold spectrum,
a neutrino mass, or a new physical particle.

Real chiral lepton SU3 gauging also faces representation
content, gauge-anomaly, flavour-changing and mass-generation
constraints; using a vectorlike synthetic qutrit avoids
claiming those are solved. A 2026 family-unification example
explicitly uses added localized fermions for anomaly cancellation
(Prog Theor Exp Phys 2026, 023B05,
DOI 10.1093/ptep/ptag007).

## Pareto outcome scorecard (qualitative, not fabricated probabilities)

| Candidate | Mathematical/empirical value | Biggest blocker | Next decisive acceptance |
| --- | --- | --- | --- |
| **A. Shrinking-loop regularity obstruction** | Highest near-term **mathematics** / links horn topology to gauge regularity and DCHoTT holonomy | Identify *actual* uniformly shrinking loop representatives and physical norm/trivialization | Literal geometry proof and independent analytic bound; otherwise mark conditional |
| **B. Non-Abelian 2-path synthetic SU3** | Highest near-term **engineering demonstration**; existing optics/atoms precedent | Build calibrated qutrit couplings, independent paths and readout | Gauge conjugation invariant `Tr([X,Y])` and fringe; ordinary F2 counterexample |
| **C. Source-derived spectral/Hosotani selection** | Highest potential **physical mechanism** and KK/YM reusability | Source geometry, vectorlike matter, self-adjoint domain, renormalized determinant | Predict preferred conjugacy class without fitting observed PMNS |
| **D. Leptonic SU3 fundamental model** | Highest speculative impact | anomaly-safe chiral currents, mass textures, weak currents, data | Gauge-invariant parameter-limited PMNS/CP prediction & source NuFIT/T2K likelihood |
| **E. Monster/VOA/369 and KK transfer** | Potential later donors only | no same-object map or physical stress/charged current | Explicit exact representation and dynamics; no promotion by analogy |

**Programme phase:** P2 group existence PAID in ordinary mathematics;
P3 topological/analytic embedding and finite-source checks partial;
P4 physical model **not yet source-derived**; P5 actual measured
prediction **open**.

## Deliverable routes and validation

On neutrino PR #1247:
- `DASHI/Physics/QFT/NeutrinoHornedWilsonInterferenceExact.agda`
  records the exact selected Wilson character and a conditional
  unpolarized two-path intensity using canonical SUNWilson owner;
  Agda kernel **NOT RUN**.
- `tests/test_neutrino_horned_wilson_regularization.py`
  contains selected fixed-source and conditional norm-bound probes.
- `scripts/check_neutrino_horned_wilson_spectral_selection.py`
  computes the *ordinary ring* spectrum/heat-trace counterfactual.

On horned PR #1244:
- `scripts/alexander_horned_c3_su3_regularization_no_go_probe.py`
  computes the conditional all-depth defect bounds *without*
  importing the unmerged neutrino branch.
- `DASHI/Geometry/FlatFormalDiskHolonomySurface.agda` remains
  the original analytic/completeness/holonomy-to-identity owner,
  NOT a claimed kernel certificate.

Locally independently executed source-compatible Python tests:
8/8 new test functions PASS on the full implementation (previous
36/36 pass), plus independent numeric ring heat-trace checks.
The committed new 6-test wrapper and horn probe have no separately
asserted exact-Git-blob execution receipt at the time this
document was authored. No CI work and no experimental run.
