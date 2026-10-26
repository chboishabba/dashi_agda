# Source-linked Hatcher horn: peripheral localisation, marked systoles and gauge regularity MAX-CUT
Date: 2026-10-26 (Brisbane). Agda PR #1249; Lean scalar-interface PR #84.

## Attribution, precise source identity and verification
* J. W. Alexander, 1924, original wild sphere, DOI 10.1073/pnas.10.1.8.
* Allen Hatcher, *Algebraic Topology*, **Example 2B.2**, printed pp. 171–172, original author PDF https://pi.math.cornell.edu/~hatcher/AT/AT.pdf: nested X_(n+1)⊂X_n, complement Y_n, F_(2^n) basis consisting of loops linking the stage handles, and the parent-meridian commutator of child meridians. Original PDF pages 171–172 independently viewed as images. **No Euclidean length bounds** supplied by this source.
* Franca Lippert, *The Alexander Horned Sphere and Bing's Hooked Rug*, §§2.1–2.3, separate supported pillbox/linked tori exposition (later mathematical source, not an independent discovery of the original Alexander embedding); no uniform length/bi-Lipschitz constant claimed to have been read or computed from this exposition.
* Agda horn **PR #1244** owns all SAME-OBJECT C3 satellite coordinates, the paper-level central tame-tree π1=1 argument, explicit pierced radial-shell chart, C3-equivariant paths x0→p_i, chronological Hatcher cylinder reconciliation, and tame C3×Cantor negative control. Existing Deicyde/hatcher-at/Jack McCarthy van Kampen and three-arm cover Lean sources remain owners. We do NOT mutate #1244 or duplicate its code.
* Agda neutrino **PR #1247** owns SAME exact illustrative selected W and P(phi), not the present metric bridge.
* Agda #1249 / Lean #84 already derive exact W squared norm >517/250, flat selected child gaps >781/1000, the sharp sibling coefficient c²(e)=4e²-e⁴, and the conditional curved defect budget eta<=23/500. This cut composes those previously accepted *conditional* theorems with the actual cover geometry and defines the still-missing metric source object.
* Exotic topology Agda **#1254** / Lean **#86** own the generic chronological prepend-vs-append event and tame-versus-wild linking nonpromotion. Do not identify the TAME C3 Cantor comparator with Hatcher linked X_n.

New computational sources are byte-for-byte locally executed, Git SHA1 blob matched and both PASS:
- `scripts/check_horn_peripheral_localization_maxcut.py` blob `9fff0ab312aa0f2993ebd19b3ae237a0334d231c`.
- `scripts/check_horn_marked_systolic_tree_cut.py` blob `e99f62379696803c2d24ded671686ef547092a3e`.
New Lean `Integration/DASHITOE/HornPeripheralLocalitySystoleCut.lean` is SOURCE-WRITTEN; Lean/Lake/Agda kernel and CI NOT RUN. Real wild-horn geometry, physical field and measurement NOT certified.

## P0a: forced peripheral entry for ANY nontrivial flat root

Use the ACTUAL three-sector owner #1244 coordinates:
x0=(20,20,20), c0=(9,0,0), c1=(0,9,0), c2=(0,0,9),
r_-=15/4, r_+=17/4. Let E=R³\B and

    C={x∈E: |x-c_i|>15/4 for i=0,1,2}.

For the #1244 chosen same-object central tame-tree geometry,
π1(C,x0)=1 on paper; the analytic claim in this paragraph is
CONDITIONAL ON THAT SOURCE-IDENTIFICATION and a FLAT connection.

If based loop gamma at x0 has flat holonomy !=I, it cannot lie
entirely in C. Thus its trace must meet some CLOSED inner cut
ball |q-c_i|<=15/4. Exact Euclidean source equalities:

    |x0-c_i|²=(20-9)²+20²+20²=921,
    (303/10)²=918.09 < 921.

Take ANY such q on a rectifiable based loop gamma, and let a be
the length of the outward part gamma:x0→q. Triangle inequality
gives a>=|x0-q|>=sqrt(921)-15/4; the return arc has at
least the same length. Therefore

    Length(gamma)>=2(sqrt(921)-15/4)>531/10=53.1.

This is a REAL exact rational necessary metric consequence of
the paper-level same-object central pi1 input. It does NOT prove
that an actual Hatcher meridian is geometrically short; indeed
it shows a root loop measured from the far-away common basepoint
CANNOT be short in the chosen coordinates.

Existing #1244 has explicit C3-invariant global-to-shell whiskers
gamma_i from x0=(20,20,20) to p_i=13e_i; the latter points have
|p_i-c_i|=4 strictly between 15/4 and 17/4. Their LENGTHS are
long: |x0-p_i|²=(-7)²+20²+20²=849. The correct bounded-gauge
small-loop test is the **local FREE-HOMOTOPY meridian**, because
holonomy based via a long whisker is unitary-conjugate and
d(U)=||U-I||op does not change. Do not insert based length>53.1
into ML<=781/1000.

### Flat overlap exclusion and curved negative control

The ACTUAL owner chart shows each pierced-shell overlap
C∩S_i ≅ (15/4,17/4)×open(D²), with p_i=(r,y)=(4,0)
as a chart-fixed basepoint and explicit contraction
H_s(r,y)=((1-s)r+4s,(1-s)y). A loop lying ENTIRELY in this
overlap is contractible, so its flat holonomy is I. In particular
a nontrivial *flat* Hatcher meridian cannot be represented wholly
in the overlap shell: the source loop must actually access the
satellite interior, not merely its tame spoke/collar.

The word **FLAT** is essential: on the shell chart's open disk,
consider the smooth SU3-valued commuting connection form

    A=(i/2)diag(1,-1,0)(x dy-y dx).

Its curvature is i diag(1,-1,0) dx∧dy. On the contractible
circle x²+y²=1/4 the flux is ±π/4 and holonomy has eigenvalues
e^(±iπ/4),1, hence is NONTRIVIAL despite loop nullhomotopy.
This is a synthetic exact-source-coordinate CURVED negative
control, not a Hatcher source field. For a physical curved
consumer, construct the actual based Stokes surface/eta instead.

The local script checks the exact C3 centre distances, the
strict rational sqrt921 comparison, all three source p_i shell
positions, five rational radial contractions of a based polygon,
and the diagonal-curvature negative control.

## P0b: marked systole is the precise geometric missing object

Let m_w be Hatcher's ORIGINAL generator class at the selected
finite stage, viewed up to coherent free conjugation/inversion.
Define its **Euclidean marked free systole**

    ell(m_w)=inf{Length(gamma):
      gamma is rectifiable, lies in the SAME exterior E,
      and represents the free-homotopy class of m_w}.

This is an INFIMUM OVER GEOMETRIC CURVES, not a Cantor-cylinder
diameter, a group word's combinatorial length, a finite tame link
drawing, nor the long based x0-loop length.

For a fixed genuine flat SU3 connection in a gauge with UNIFORM
operator coefficient bound ||A||<=M, standard unitary
parallel transport gives, for EVERY such gamma,

    d(Hol(gamma))<=∫||A(gamma')||dt<=M Length(gamma).

Flat holonomy of conjugate/reversed loop classes has the same
d; taking the infimum yields

    d(rho(m_w))<=M ell(m_w).                         (SYS)

For the EXISTING selected W first-stage source proof, both truly
marked child gaps exceed 781/1000, so necessarily

    M ell(m_child)>781/1000.

One real source-class representative satisfying M*Length<=781/1000
would contradict the selected flat W **immediately**. Actual
meridian/connection inputs not constructed in this PR.

### Every infinite branch: exact rational threshold without radicals

The earlier #1249/#84 sharp sibling multiplier satisfies

    c(31/60)²=12914879/12960000 <1.

Fix ANY infinite marked branch of Hatcher's SOURCE group tree.
If its sibling gaps were <=31/60 eventually, repeated direct
sharp commutator multiplication, with unitary terminal cap 2,
would force its ancestral/root gap to zero. Therefore for
EVERY infinite branch of ANY nontrivial root representation,
there are INFINITELY MANY sibling indices k with

    d(rho(m_sibling,k))>31/60.

For a globally bounded M>0, (SYS) implies infinitely many k
along each branch with

    ell(m_sibling,k)>31/(60M).                      (BRANCH)

Thus if actual SAME-OBJECT source geometry proves that the
marked sibling systoles tend to zero along even one correctly
marked branch, there exists NO globally bounded compatible gauge
realising that nontrivial flat root. More strongly, if all sibling
systoles uniformly vanish with stage, every branch is obstructed.

This is **gauge-invariant as a statement of the nonexistence
of ANY globally uniformly bounded representative in the gauge
equivalence class**, although an individual potential coefficient
||A|| is gauge dependent. Do NOT promote it to a curvature,
energy-density or spacetime singularity: every flat
representative has F_A=0 on E.

### Finite-branch geometry and the missing quantitative link

A useful purely topological DONOR theorem: suppose nested nonempty
COMPACT metric sets K_w are indexed by finite binary words, with
K_(wb)⊆K_w, and each infinite branch has singleton intersection.
Then max_{|w|=n} diam(K_w)→0. Proof by contradiction: a positive
diameter threshold at arbitrarily deep nodes produces, by
finite-branch König's lemma, a branch whose nested compact sets
all have diameter at least that threshold; compactness implies
their intersection still has positive diameter, contradicting
the singleton branch limit.

This theorem can consume Hatcher's linked-handle source ONLY once
the literal K_w nesting and unique single-point intersection
properties are identified on his ACTUAL embedding. #1244's tame
Cantor comparator already has a quantitative 3^-n diameter
formula, but does NOT identify the wild Hatcher handle K_w.

**Diameter shrinking still does NOT pay the marked systole.**
A strong negative control within the SAME once-winding loop class
in the punctured plane is

    r_n(theta)=3^-n(1+(1/4)sin(3^n theta)),  0<=theta<=2π.

The curve is simple and winds ONCE. Its image diameter is
at most (5/2)3^-n→0, but its radial total variation is
4*3^n*(3^-n/4)=1, so its rectifiable length is >=1.
This does not imply the *systole* is >=1: the round circle
in the same class is a short representative. It proves
why ONE small-diameter loop cannot be used as a length certificate
without a controlled choice of representative.

A sufficient measurable SOURCE DONOR would be:
(1) correctly marked exterior meridians gamma_w with entire
stage X_|w| avoidance, and (2) a UNIFORM quantitative local
collar/round-meridian bound
    Length(gamma_w)<=C diam(K_w)
independent of n and w. Combined with uniformly shrinking
wild-source K_w this pays actual ell(m_w)→0 and rejects
every bounded-gauge realisation of the nontrivial root.
Even weaker source-specific L(gamma_w)→0 along ONE
marked infinite branch also suffices. **Neither geometrical
quantity is yet supplied by original #1244 / Hatcher / Lippert
source in checked files.**

## Pareto / snowball / Ibrahim: highest-value actual remaining deliverable

P0: instantiate original Hatcher's stage linked pillbox/tube
K_w as an actual named subset of the SAME #1244 wild
satellite. Certify compact nesting, free-group meridian
marking, all-stage exterior avoidance, and at least a single
branch of short local representatives. First inspect/reuse
#1244's supported-satellite and #1254's ambient-linking
negative controls; not another ternary/VOA Cantor codec.

P1: consume the local length witness through
`Integration/DASHITOE/HornPeripheralLocalitySystoleCut.lean`
and existing exact W theorem in #84. Resolve kernel API
only after identifying geometric source data; don't mistake
rational conditional Lean for a wild 3-manifold theorem.

P2: for a CURVED connection, supply the actual based source
parent-to-child commutator homotopy, operator curvature
bound and transported area eta. Original exact curved
selected-W acceptance remains one child d<=3/4 plus
eta<=23/500. Contractible-shell CURVED holonomy example
is a negative control, not an eta source.

P3: only then evaluate source gauge action, finite
regularization and physical observables. Abstract
SU3 representation and flat-connection existence are
NOT experimental monodromy and not neutrino mass predictions.

All source claims keep original-author priority, paper
versus implementation versus executable local test versus
Lean/Agda kernel proof versus measured physics separate.
No QID/DDC invented. This is a geometry/source wall,
not a request for user approval.
