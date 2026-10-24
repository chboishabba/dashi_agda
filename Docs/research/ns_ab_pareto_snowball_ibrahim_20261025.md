# Navier–Stokes A/B — Pareto, citation snowball and Ibrahim attribution audit (25 October 2026)

## Scope and source policy

Goal: advance the original **unforced** Clay A/B programme, especially
`NSClayFacingAPhysicalSameObjectCutExact` / Bishop A1–A3 and the original
R735 W1/W2 shared weighted controls. Do not import a claimed global
regularity proof by citation. Use the repository's existing
`DASHI/Core/SnowballAttributionProvenanceInvariantExact.agda` and
`DASHI/Wikimedia/IbrahimSnowballParetoFrontierExact.agda` as shared
provenance/priority policies, **not** as evidence for a PDE theorem.

Do not conflate: (1) the repository's Ibrahim-named first-link
snowball/Pareto provenance framework; (2) **Sage A. Ibrahim**,
coauthor of the Permana–Lathief–Ibrahim NS preprint. They are
different referents. Authorship, dated manuscript version, original
source root, derivative/revision relationship, mathematical hypothesis,
claimed conclusion, physical validation, formalization, and
independent kernel proof must each retain distinct coordinates.

The source URLs below are external original publications/manuscripts.
A preprint page or repository code is not independent peer validation.

## Highest-alpha physical result (DASHI original exact witness)

The 2026 Permana–Lathief–Ibrahim Zenodo v3 (DOI
10.5281/zenodo.19632058, April 17, 2026) abstract advertises a
De Giorgi–Nash–Moser-produced high-vorticity direction-curvature bound
  |grad xi| <= C_nu |omega|^(1/2).
The older original `NSTriadKNPermanaAlignmentRateAudit.agda`
already checks a trace-free strain sign counterexample and
non-invariance of the proposed T3 on finite carriers; retain it.

NEW actual **unforced Navier–Stokes** smooth periodic heat field, for
each positive integer n and A,nu>0:
  u_n(t,x,y,z)=(A/n) exp(-nu*n²*t) (0,sin(nx),cos(nx)).
Its divergence is 0; its advective nonlinearity vanishes because
u_x=0 and all components depend only on x. Thus the exact solution
of unforced NS satisfies du/dt = nu Δu, with constant pressure.
  omega_n=curl u_n =
     A exp(-nu*n²*t) (0,sin(nx),cos(nx)).
  |omega_n|=A exp(-nu*n²*t) at **every point**.
  xi_n=(0,sin(nx),cos(nx)), |grad xi_n|=n at **every point**.
At t_n=1/(nu*n²)>0:
  |omega_n(t_n)|=A/e,
  |grad xi_n(t_n)|/|omega_n(t_n)|^(1/2)
     = n sqrt(e/A) -> infinity as n->infinity.
Choose A>e Omega for ANY fixed high-vorticity threshold Omega: the
ENTIRE domain lies in the purported active high-intensity region.
The family even has normalized initial kinetic energy A²/n² and
initial enstrophy A². Therefore an estimate with C_nu independent of
initial-data frequency, geometry and Sobolev norms CANNOT be deduced
solely from the Navier–Stokes dynamics and positive viscosity.
This does NOT refute a version where C_nu hides dependence on
an evolving T3, higher initial norms, a separate alignment
hypothesis, or some other explicitly named scale-dependent control.

Executable: `tests/test_ns_permana_ibrahim_direction_rigidity_heat_shear.py`,
4 locally passing SymPy tests, including the global-constant-magnitude
example. Neither these tests nor the comments in the original Agda
owner constitute a kernel proof of an unbounded-function theorem.

## Source genealogy: separate ROOTS, not independent votes

| Root/source | Dated provenance | Literal relevant contribution | Proof-status and A/B role |
|---|---|---|---|
| Peter Constantin and Charles Fefferman | *Direction of Vorticity and the Problem of Global Regularity for the Navier–Stokes Equations*, Indiana Univ. Math. J. 42(3), 775–789 (1993), https://iumj.org/article/3627/ | Regularity conditional on vorticity-direction coherence in intense regions | Established source of geometric criterion, not unconditional propagation |
| Hugo Beirão da Veiga and Luigi C. Berselli | *On the regularizing effect of the vorticity direction in incompressible viscous flows*, Differential and Integral Equations 15(3), 345–356 (2002), DOI 10.57262/die/1356060864 | Weaker conditional directional regularity | Authoritative prior art; still needs hypothesis producer |
| Alexey Cheskidov and Mimi Dai | *Regularity criteria for the 3D Navier–Stokes and MHD equations*, Proc. Edinburgh Math. Soc. 68 (2025), 1262–1296, DOI 10.1017/S0013091525100813 | Conditional smallness of dyadic high-frequency vorticity-integral near possible blowup time | Strong, explicit continuum continuation CONSUMER for A3/B7; not an energy-derived unconditional producer |
| Zoran Grujić | *Logarithmic Depletion of Vortex Stretching and Singularity Evasion in the 3D Navier–Stokes Equations*, arXiv:2607.08866, revised 15 October 2026 | Theorem 7.4 assumes critical vorticity concentration in L∞_t L^{3/2,∞} and direction in L∞_t bmo_{1/|log r|}; derives nonblowup on that hypothesis | Distinct conditional preprint route, not universal proof; cites Constantin–Fefferman and Berselli |
| Zoran Grujić | *On Decay of the Local Mean Oscillations of the Vorticity Direction in Critical Navier–Stokes Flows*, arXiv:2609.05720v2, September 2026 | Analyzes direction PDE and conditional control of phase oscillation from temporal modulus + tangential strain in critical spatial point profile | Companion of same-author work; NOT independent corroboration; sharpen production obligation |
| Mojtaba Jalali Koutanaei | *On the Classification of Initial Data...*, Zenodo 21943563, 15 August 2026 | Conditional LP geometric-depletion criterion and explicit missing global propagation step | Useful mathematical negative-control/consumer mapping; not a general proof |
| Bryan P. Permana, Sage A. Ibrahim, Hanif A. Lathief | SSRN 6557718 (written 11 April, posted 30 April 2026); Zenodo v3 19632058 (17 April); related v4 20049273 (6 May) | Claims direction-curvature rigidity/T3 and initially universal regularity; later v4 abstract instead states conditional small-data regularity | One related author/revision FAMILY; not multiple independent proof roots. Original Agda audit already identifies deeper T3 strain issues; new physical witness excludes viscosity-only unconditional rigidity |

The first two are pre-existing original mathematical regularity roots;
Grujić 2026 explicitly cites both. Cheskidov–Dai is a distinct
dyadic continuation root. The two Grujić 2026 papers are
closely-related same-author companion pieces. The Permana variants
have shared authors/objects and differ in claims; Zenodo's
resource-type or review metadata is not a substitute for external
expert assessment. The DASHI counterexamples are **independent
calculations**, not copies of the authors' testimony.

## Pareto cut on SURVIVING unproved A/B obligations

1. **B / R735 W1 and W2, high leverage**: obtain physical
   cutoff-uniform signed commutator payment and a strict augmented
   critical estimate, on the same real trajectory. R691/R699/R735
   are already proof compilers; reuse. Known no-go witnesses prohibit
   energy-only W1, padding-dependent R236, universal R823 reserve,
   outputwise R690 positivity, and now viscosity-only direction
   rigidity. Do not produce a new compiler with an uninhabited
   premise renamed. Grujić's tangential-strain formulation is an
   *interesting conditional comparison*, not an already-paid W2
   estimate.
2. **A / A1 same-object Bishop heat-frequency representation**:
   use existing `BishopPositiveCrossReciprocalUpperExact`,
   `BishopStrictRatioInterpolationExact` and physical positive
   rational SHELL-floor constructors, not impossible rational
   equality to an arbitrary Bishop-real ν|xi|². Transfer the
   actual real resolvent inequality and physical kernel to A1.
3. **A / A2+A3**: prove same-solution signed low/high majorant
   domination and a noncircular scale-critical continuation
   quantity. The Cheskidov–Dai dyadic-vorticity criterion is a
   high-value published consumer but the required smallness at
   all arbitrarily high dyadic scales is NOT a consequence of the
   elementary Leray energy inequality.
4. **Literature checks (opportunistic only)**: sample later Grujić
   propositions and Koutanaei's conditional depletion for a
   genuine SAME object and quantifier improvement, not simply
   because their titles mention Navier–Stokes or regularity.

## Operational acceptance and stop rules

For any candidate payment require: exact authorship/date/title DOI,
source theorem quantifiers, no forced-to-unforced transfer, same
physical operator/velocity/solution, uniform-in-cutoff constants,
correct Navier–Stokes scaling, signed compensation, a non-circular
estimate from energy/geometry actually proved rather than assumed,
a connection to B7/A3, and (for "formal proof") cumulative Agda/Lean
kernel verification. Explicitly test on all existing adverse
shears/zero-padding and the rotating constant-vorticity-magnitude
field above. If a candidate violates one, preserve its true local
content but exclude the failed global implication. No 3D unforced
Clay result is claimed here.
