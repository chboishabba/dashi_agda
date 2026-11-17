# Hatcher source F₂ versus metric Hopf-clasp Z²: exact bidirectional discriminator
Date: 2026-10-27 Australia/Brisbane.
Primary branch owners: Agda hyperfabric #1249, Lean conditional consumer #84.
Prior genuine horn geometry owner: Agda #1244.

## Original mathematical source lineage — no borrowed priority

- J. W. Alexander (1924), original horned sphere DOI 10.1073/pnas.10.1.8.
- Allen Hatcher, **Algebraic Topology**, Example 2B.2 pp.171–172,
  https://pi.math.cornell.edu/~hatcher/AT/AT.pdf, visually
  inspected original PDF pages 179 and 180 of this edition.
  The attached piece Z has π₁(Z)=F₂ on actual loops α₁,α₂
  linking two HORN HANDLES and the attaching annulus generator
  α maps to nonzero [α₁,α₂]. The source's assertion that
  Z−A is homeomorphic to an open ball with two straight
  tubes deleted is topological: NO Euclidean bi-Lipschitz
  bound, actual local meridian size, or ambient infinite
  Hatcher stage coordinate map is furnished.
- Stefan Friedl, **Topology / Knot Theory** lecture notes,
  2024, Lemma 3.13 (Hopf Link Lemma), source PDF
  https://friedl.app.uni-regensburg.de/papers/2024_knot-theory-final.pdf
  p.44 (PDF p43): Hopf complement S³\H diffeomorphic to
  T²×(-1,1), hence π₁=ℤ². This is LATER EVIDENCE
  for a CLASSICAL Hopf complement theorem, not original
  invention of link groups by Friedl.
- Actual rational linked circle formulas and C3 placement
  were previously authored/implemented on horn **PR #1244**:
  `scripts/alexander_horned_clopen_linking_impasse_probe.py`,
  `scripts/alexander_horned_three_sector_geometric_vankampen_probe.py`.
  They already establish core linking lk=−1, optional
  translated unlinked control and C3 satellite spacing.
  We DO NOT reassign that prior source to #1249.
- Neutrino Agda **#1247** owns the SAME illustrative W;
  Agda #1249 / Lean #84 already own the original selected
  exact W squared norm >517/250 and child-gap >781/1000.
  The classical abelian-complement no-go and new metric
  transverse-meridian certificate are **derived consumers**,
  not a new neutrino prediction, wave/TOE theory or a proof
  of a novel wild embedding.

## A genuine finite geometric POSITIVE meridian certificate

Original #1244 local embedded prototype core circles:

    C1(t)=(2 cos t,2 sin t,0)
    C2(t)=(1,1+cos t,sin t).

The original C1 spanning disk meets C2 at
(1,0,0) INSIDE disk radius 2 and (1,2,0)
OUTSIDE. Therefore their oriented core linking is ±1,
with #1244's convention −1.

We now give explicit transverse round meridian curves
with radius rho=1/8 AROUND THOSE SAME CORES:

    M1(t)=(2+rho cos t,0,rho sin t)
    M2(t)=(1+rho cos t,rho sin t,0).

The disk spanned by M1 at y=0 intersects C1 exactly
once at (2,0,0), with tangent along y and independent
crossing; C2 is entirely disjoint from it. Hence
|lk(M1,C1)|=1 and lk(M1,C2)=0.
The disk spanned by M2 at z=0 meets C2 once at
(1,0,0); C1 misses the whole disk because its nearest
point to (1,0,0) is distance 1>rho. Hence
|lk(M2,C2)|=1 and lk(M2,C1)=0.

Distances: every point of M1 has EXACT Euclidean
distance rho to C1; every M2 point has EXACT
distance rho to C2. Foreign core distances
are at least 1−rho=7/8. Thus both meridians
remain disjoint from radius a=1/32 THICKENINGS
of either core with positive gaps rho−a=3/32,
foreign gap >=27/32.

The two cores themselves are separated.
For C2 y=u=1+cos t in [0,2], distance squared to
C1 is 5+2u−4sqrt(1+u²). By the convexity
of Euclidean norm
sqrt(1+u²) <= (1−u/2)+(u/2)sqrt(5),
so dist² >=1+(4−2sqrt5)u >=
9−4sqrt5=(sqrt5−2)².
As sqrt5>11/5 by exact 5>(11/5)²,
the core distance >1/5>2a, proving
the THICKENED closed cores do not intersect.

Furthermore this PARTICULAR pair is Hopf (rather
than only a link of numerical linking ±1).
A smooth disjoint isotopy of the second circle is

    C2_s(t)=(1−s,1+s+cos t,sin t),   s∈[0,1].

Its two intersections with z=0 have projected
xy-radius squares (1−s)²+s²<=2<4 (inside C1
disk) and (1−s)²+(2+s)²>=5>4
(outside). The circles never intersect.
At s=1 they are the standard orthogonal
round-circle Hopf presentation; by standard
isotopy extension their complementary group
is the classical Hopf ℤ².

The already OWNED #1244 local affine C3 map is

    F_c(p)=9 e_c + R^c((1/4,0,0)+(1/8)p),

R(x,y,z)=(z,x,y), R³=Id.
Each mapped meridian lies in the radius-one
SATELLITE REFERENCE ENVELOPE, with strict
clearance from the inward connector cap.
It is an explicit loop in the COMPLEMENT OF
THE TWO FINITE MODEL CORE TUBES. It is NOT
certified to avoid the ACTUAL infinite Hatcher
stage solid in #1244's wild embedding.

The local Euclidean length after 1/8 scale is

    Length(F_c(M_i))=2π*(1/8)*(1/8)=π/32
                   <11/112≈0.098214286.

The inequality uses classical π<22/7;
the exact rational model is **far below**
the source-selected threshold 781/1000
when synthetic gauge M=1. This finite positive
metric result is real geometry, not just
Cantor address or numerical sketch.

## THE DECISIVE NEGATIVE: this is NOT Hatcher's F₂ source

For this actual closed Hopf pair,

    π₁(S³−(C1∪C2)) ≅ ℤ²,

the two meridians commute. Therefore under
ANY flat homomorphism into SU3,

    ρ([M1,M2])=I.

Compare original Hatcher attachment

    π₁(Z)≅F₂,  α ↦ [α₁,α₂] ≠1.

The F₂ word [a,b]=aba⁻¹b⁻¹ is a nonempty
freely reduced word. Its nontriviality
has an exact SU3 POSITIVE CONTROL:
A=iσ_x ⊕1, B=iσ_y ⊕1,
det(A)=det(B)=1 and

    [A,B]=diag(−1,−1,1) ≠I.

In stark contrast, the Hopf group forces
all abelianized source commutators to identity.
Therefore the small linked comparator loops
**CANNOT BE the two Hatcher child generators
in the required relative Z-annulus source map**,
even though all their linking, C3, metric,
clearance, and local Euclidean properties pass.

This is a much stronger FALSE-POSITIVE FIREWALL
than the old warning 'linking number is insufficient'.
It also demonstrates that a pairwise-linking
observation / abelian topology cannot certify
the nonabelian incoming annulus word.

## Code / verification / acceptance status

New AGDA-branch Python:
`scripts/check_horn_linked_clasp_metric_vs_hatcher_f2.py`.

- Exact Fraction-certified link intersection, core
  thickening/clearance, original C3 satellite map,
  two meridian lengths π/32<11/112, 101 rational
  isotopy-parameter samples backed by UNIVERSAL
  polynomial inequalities, and noncommutative free
  word source contrast.
- Optional independent exact SymPy SU3
  nonabelian receiver verifies
  [iσx,iσy]⊕1=diag(-1,-1,1).
- A locally independently reconstructed suite of
  the exact rational geometry and SU3 calculation PASSED.
  Committed GitHub script exists; byte-identical
  GitHub-blob execution of this NEW file has NOT
  been separately achieved in the local container.
- NEW SOURCE-WRITTEN Lean mirror on PR #84:
  `Integration/DASHITOE/HornHopfClaspVsHatcherF2NoGoCut.lean`.
  For every `CommGroup` source H and every
  monoid/group homomorphism `rho:H→*G`, the
  commutator of two meridian images is 1.
  It rejects the source-selected W via its original
  nonzero squared operator norm bound. Lean/Lake
  **NOT** typechecked, and 3D isotopy/Hopf source
  is an EXTERNAL classical premise.
- No locally run Agda kernel, source-linked wild
  Hatcher generator, Stokes surface, physical
  measurement or gauge-field anomaly inference.

## Pareto / Ibrahim / snowball: final two-gate stop

**P0 — ACTUAL SOURCE TYPE FIRST.**
The new exact metric clasp certificate is disqualified
from the Hatcher meridian consumer by its ℤ² source.
The highest-fanout missing object remains the
SATELLITE RELATIVE HATCHER GROUP EQUIVALENCE that
takes the *punctured-torus* annulus-boundary commutator
in Z (F₂), carries both actual named meridians into
the wild exterior group at the chosen finite stage,
and preserves based orientation/conjugation.
The already-source-written #1244
`ThreeArmSourceGroupCertificates.member_group`
is the canonical destination. A Hopf link group
or a tree of merely tame balls must FAIL that interface.

**P1 — SAME SOURCE METRIC SECOND.**
Once P0 identifies the actual linked Hatcher
meridian representative in the source ambient E,
obtain its Euclidean arclength or a concrete
uniform/branch-specific chart distortion
Lambda_w such that L<=2πLambda_w*b_w.
Then existing first-child W cutoff
M L<=781/1000 or every-branch
systole bound 31/(60M) may consume it.
A homeomorphism F₂-equivalence with no metric
control is insufficient; conversely a very
short Hopf model loop with wrong group is
insufficient. These independent counterexamples
make both implications nonpromoting.

Source root web verification: Hatcher original
PDF page image, Friedl 2024 Lemma 3.13.
No fabricated QID/DDC or false authorship
by newer expository/implementation authors.
