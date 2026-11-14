# 2026-10-25 HIGHEST-ALPHA ORIGINAL-SOURCE T3 AUDIT — BELTRAMI KERNEL AND STATED POSTULATES

## Original source roots and evidence distinctions
Permana, Ibrahim and Lathief (May 6, 2026 author-uploaded manuscript,
related to Zenodo v4 DOI 10.5281/zenodo.20049273), *Quantitative
Regularity ... Geometric Depletion, Fractal Bounds, and Topological
Damping*, §2.1 Eq (3), §2.2 Definitions 2.1/Lemma 2.2/Remark 2.3,
§3.2 Definitions 3.1--3.3 and Remark 3.7:
https://www.researchgate.net/publication/403818610_Quantitative_Regularity_of_the_3D_Incompressible_Navier-Stokes_Equations_on_the_Periodic_Torus_Geometric_Depletion_Fractal_Bounds_and_Topological_Damping
This author-uploaded long-form source has more usable theorem text
than the Zenodo v4 ABSTRACT. Preserve original author ownership.
The earlier Zenodo v3 record (17 April 2026, DOI
10.5281/zenodo.19632058) claims unrestricted global regularity in
its abstract, while the related v4 says conditional small-data.
Zenodo v3 metadata spells Hanif A. *Lathif*; v4 long form spells
Hanif A. *Lathief*. Record them as source-written version variants
rather than imagining independent witnesses or reassigning authorship.

The original v4 Eq (3) defines
  J=curl(omega cross u), T3(t)=integral_(T³) |J|² dx.
It describes T3 as 'globally positive-definite'. Our mathematical
check shows **nonnegative but not positive definite** on
nonzero, mean-zero, smooth divergence-free physical velocity fields.
More seriously, v4 Remark 3.7 asserts that elliptic regularity from
T3 controls the homogeneous H² norm of velocity and direction
curvature. Neither follows: the operator u↦curl(curl(u)×u) has a large
Beltrami kernel. This is a direct SAME-DEFINITION counterexample,
not a claim about a different invented 'topological invariant'.

For every integer N>0, positive viscosity ν and amplitude A,
  u_N(t,x,y,z)=(A/N)e^(-νN²t)(0,sin Nx,cos Nx)
solves the FULL unforced incompressible NS equation with constant
pressure. It is real, smooth, mean-zero and divergence-free on T³.
  omega_N=curl u_N=N u_N,
  omega_N×u_N=0, J=0 and T3(t)=0 at EVERY t.
At t_N=1/(νN²)>0:
  |omega_N|=A/e everywhere,
  |grad xi_N|=N everywhere,
  ||omega_N||²_2=A²/e²,
  ||Delta u_N||²_2=A² N²/e²,
  ||u_N||²_2=A²/(e²N²)   [normalized torus].
Thus:
  (i) T3=0 does not imply zero nontrivial velocity/enstrophy/H²;
  (ii) no universal H² estimate ||Delta u||²_2 ≤ C*T3;
  (iii) no universal curvature estimate
        ||grad xi||_∞ ≤ Cν * sqrt(||omega||)
       with Cν depending only on viscosity;
  (iv) no universal bound ||omega||²_2 ≤ C(Ekin+T3).
No finite fixed C pays these as N→∞.
The genuine full-field identity is classical Beltrami theory
(original mathematical phenomenon, not attributed as a Permana
or DASHI discovery). The particular explicit parametric
counterexample and its application to Eq (3)/Remark 3.7 are DASHI
original analysis.

**Critical attribution restraint:** The original v4 has
Definition 2.1 *Topological Invariant Conservation Hypothesis
(TICH)*, assuming nonlinear T3 terms are a divergence;
Remark 2.3 explicitly calls proving that identity an OPEN CONJECTURE.
Lemma 2.2's exponential T3 decay is CONDITIONAL on TICH.
Definition 3.1's TAH alignment damping, Definition 3.2's
DGMICH Muckenhoupt-A2 weight, and Definition 3.3's
T3-curvature bound are other HYPOTHESES, not consequences
already proved for all unforced NS data. Remark 3.7 explicitly
labels its T3 curvature interpretation heuristic motivation for a
formal postulate. Source page text alone does not grant these premises.
On our Beltrami datum <xi,S[u]xi>=0, so the proposed T3-weighted
*alignment* inequality is 0≤0, NOT contradicted. It is the
claimed **general topological/coercive control** and any universal
curvature production inference that the test excludes.
This distinction protects genuinely conditional lemmas.

The original 2026 Grujic direction PDE sources are a separate
conditional geometric route. On this Beltrami field
S[u]xi=0, grad(log|omega|)=0,
Delta xi+|grad xi|²xi=0:
harmonic-map heat terms cancel, despite arbitrarily large
|grad xi|. This is a physical negative control against assuming
viscosity alone produces conditional direction regularity; it does
not falsify Grujic's assumptions, Constantin--Fefferman (1993),
or Beirao da Veiga--Berselli (2002).

## Formal/algorithmic receipt, highest-alpha action
Existing reusable Agda owners:
`NSTriadKNRationalLerayProjectionExact`,
`NSTriadKNFourierBiotSavartExact`,
`NSTriadKNFourierSelfModeVortexStretchingNoGoRound78Exact`.
The ORIGINAL `NSTriadKNPermanaAlignmentRateAudit.agda`
now contains a source-written exact rational cross-product theorem
`beltramiLambVectorZero` (if omega=lambda*u then omega×u=0),
and the manuscript's real proof-status boundary as comments.
This is a polynomial algebra lemma, not a proof of the full
real-trigonometric time-evolution theorem in Agda.

`tests/test_ns_ibrahim_beltrami_T3_noncoercivity.py`:
**6 locally executed SymPy tests passed** (exact unforced heat PDE,
curl eigenrelation, T3 zero, active-region direction, H²/
enstrophy noncoercivity, strain alignment zero). The committed
source is a matching independent test; no exact-PR-head CI run
nor cumulative Agda kernel certificate was available.
The separate A1 improvement in
`NSClayFacingAPhysicalSameObjectCutExact.agda`
now returns a **genuine ℚᵘ witness** from Bishop rational density
rather than erasing it to the ambient real, enabling a future
constructive shell/resolvent attachment; kernel checking remains open.

## POSITIVE SAME-SOURCE T3 ↔ SIGNED VORTICITY PRODUCTION

For divergence-free u on T³, classical vector calculus gives
J=curl(omega×u)=(u·grad)omega-(omega·grad)u.
The UNFORCED vorticity equation gives the SAME physical source identity
  J=nu Delta omega-partial_t omega.
Thus the author-defined T3=||J||²_2 is the **squared nonlinear
vorticity-source norm**, not a norm coercing omega or normalized
vorticity direction. Periodic integration by parts yields
  P_enstrophy_nonlinear = 2<omega,(omega·grad)u>
    = -2<omega,J>
and Cauchy--Schwarz gives the valid bound
  |P_enstrophy_nonlinear|² <=4||omega||²_2 T3.
This is reusable analytic prior art if T3 is controlled separately,
NOT a W1/W2 payment or estimate of T3 from energy.

The existing REAL transverse six-mode B datum
p=(1,0,0),q=(0,1,2),k=(1,1,2), coefficients
u_p=(0,1,1),u_q=(1,0,0),u_k=±i(1,-1,0),
conjugate negatives, has physical nonlinear enstrophy rates
+8 and -8. Independently computing J=curl(omega×u) gives
-2<omega,J>=±8, ||omega||²_2=38, and identical
strictly POSITIVE T3 for both orientations. So T3 does not encode
the sign of physical production.
New `tests/test_ns_T3_physical_vorticity_source_signed_work.py`
checks this exact finite Fourier identity, quartic T3 vs cubic
stretching amplitude scaling, and the signed Cauchy inequality.
Together with Beltrami tests, **9 independently locally executed
SymPy checks passed**; no exact-head Agda/Lean kernel certificate.
Original NS vector identity remains classical; DASHI owns the
independent exact regression; manuscript authors own the T3
definition, not this source identity.

## SAME PHYSICAL FIELD / ORIGINAL B R735 MIXED-CARRIER KERNEL

The same real Beltrami field is **positive helicity** at both signed
Fourier frequencies (no free helical scalar assumption).
At k=±(N,0,0), `(i k×)u_k=N u_k`, hence
`H+_k u_k=u_k` and `H-_k u_k=0`.
Consequently every mixed incidence of R735 W1's original carrier
`A_(p,q)=(H+_p u_p)×(H-_q u_q)` vanishes, and
`M_k=Σ A_(p,q)=0` for all outputs/cutoffs. W1 mixed energy and
rate vanish even though at t_N the enstrophy is A²/e²,
homogeneous velocity H² squared is A²N²/e², and normalized
direction gradient is N everywhere.

This is an acceptance test: **W1 mixed-mass coercivity alone is
false** on the physical solution class, and the full B continuation
must retain W2 and separately typed same-helicity physical
channels. This does NOT refute a complete signed combined
W1/W2 scheme or any claim that W1 has a cutoff-independent
upper bound on a restricted data class.

The same six locally passing exact SymPy tests include an
independent physical Fourier projector calculation, reusing the
historical helical eigenspace theorem and the repository's
`NSTriadKNPeriodicHelicalFourierInfrastructure` convention.

**Pareto decision:** exclude T3 *as a coercive quantity* and
TICH/TAH/DGMICH assumptions as unpaid. Do not snowball more
same-author publication or citation count as independent evidence.
The positive B route is still actual R735 W1 signed global
nonlinear commutator + W2 augmented critical payment, tested
against earlier zero-padding, R823, output-sign and this field.
The positive A route still requires the Bishop-real same-solution
resolvent inequality, A2 physical signed majorant and A3
unconditional continuation. The present counterexamples do
not imply unrestricted 3D NS failure or its regularity.

---

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

**Exact Grujić direction-equation cross-pollination.** On the same
field the symmetric physical strain annihilates the unit direction,
`S[u_n]xi_n=0`. Because `|omega_n|` is spatially constant,
`grad(log|omega_n|)=0`. Moreover
`Delta xi_n=-n² xi_n` while `|grad xi_n|²=n²`, so
`Delta xi_n+|grad xi_n|² xi_n=0`.
Thus every tangential strain, magnitude-gradient cross-diffusion,
and harmonic-map heat contribution in the vorticity-direction
equation cancels. The normalized direction is EXACTLY independent
of time while the magnitude decays exponentially. This shows
viscous damping does not by itself regularize all normalized
direction oscillations, but does NOT refute Grujić's *conditional*
critical-profile logarithmic-BMO analysis or any separately proved
tangential-strain/phase hypothesis.

Executable: `tests/test_ns_permana_ibrahim_direction_rigidity_heat_shear.py`,
**6 locally passing SymPy tests**, including the high-vorticity
full-domain witness, independent kinetic/enstrophy normalizations
and exact harmonic-map cancellation. Neither these tests nor the
comments in the original Agda owner constitute an Agda kernel
proof of the universal quantified mathematical statement.

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
