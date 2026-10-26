# Sharp SU(3) spectral-arc holonomy + stage-persistent geometric acceptance
Date: 2026-10-25. Existing draft owners: dashi_agda PR #1249, dashi_lean4 PR #84.
**Source types remain distinct:** original mathematics; derived inequalities; local exact computational audit; source-written conditional Agda/Lean; actual Hatcher Euclidean geometry; physical gauge model.

## Attribution and exact source roots

- J. W. Alexander, *An Example of a Simply Connected Surface Bounding a Region which is not Simply Connected* (1924), DOI **10.1073/pnas.10.1.8**: original wild sphere.
- Allen Hatcher, *Algebraic Topology*, Example 2B.2, printed pp.171–172, original PDF https://pi.math.cornell.edu/~hatcher/AT/AT.pdf : source for **nested** X_(n+1) subset X_n, B=intersection X_n, exterior free-group stages, generator word m_w=[m_w0,m_w1]. PDF page images independently inspected. Hatcher does not certify numerical arclengths or nonflat curvature areas.
- Morikuni Gotô, *A Theorem on compact semi-simple groups*, *J. Math. Soc. Japan* **1** (1949), 270–272, DOI **10.2969/jmsj/00130270**: original compact semisimple commutator-surjectivity, independent of the elementary operator norm result below.
- Existing Agda horn **PR #1244** owns the C3-equivariant paper-level three-satellite gluing, exact rigid rotation and finite collar/separator atlas. The **geometry source object** is #1244, not a new field configuration in this PR.
- Existing Agda neutrino **PR #1247** owns the separately selected infinite-order W, exact cyclotomic trace and pre-existing abstract horn representation using Gotô/Hatcher. No new neutrino prediction here.
- Existing Agda **PR #1249** / Lean **PR #84** already establish the conditional unitary sibling estimate 2*min(1,d(B)), curvature eta envelopes, optimal prefix stops and qualitative tail. The sharper arc theorem below is a NEW derivation from standard unitary algebra, NOT a prior Gotô theorem or a claim of original Hatcher geometry.

## Exact sharper operator-norm theorem

For arbitrary unitary matrices A,B, let d(U)=||U-I||op, delta=d(B).
For 0<=delta<=sqrt(2), let lambda=1-delta^2/2>=0.
From (B-I)^*(B-I)<=delta^2 I and B^*B=I,

    B+B^* >= (2-delta^2) I = 2 lambda I.

Therefore

    (B-lambda I)^*(B-lambda I)
      <= (1-lambda^2) I
       = (delta^2-delta^4/4) I.

Since AB-BA = [(A-I),(B-lambda I)] as an ADDITIVE commutator,
unitary multiplication preserves the operator norm and yields

    d([A,B]) <= c_arc(delta)*d(A),
    c_arc(delta)=2*delta*sqrt(1-delta^2/4).      [0<=delta<=sqrt(2)]

For delta>=sqrt(2) retain the universal c<=2 by choosing lambda=0.
On [0,sqrt(2)] c_arc is increasing (the squared function has positive
derivative), so a real source cap delta<=epsilon transfers directly.

**SHARPNESS within SU(3) at every 0<delta<=sqrt(2):** choose
B=diag(e^(i alpha), e^(-i alpha),1), delta=2 sin(alpha/2), and
A_t=exp(i t sigma_x) direct-summed with 1 (SU3). Direct 2x2
commutator calculation gives

    ||[A_t,B]-I||/||A_t-I||
      = 2 sin(alpha)*cos(t/2)
      -> 2 delta sqrt(1-delta^2/4) as t->0.

This is sharp as a universal SINGLE-STAGE multiplier; it does not
prove independent sharpness of the entire geometric horn obstruction.

The coefficient is strictly <1 iff

    delta < delta_star = sqrt(2-sqrt(3)) = 0.5176380902...

in the relevant interval. Thus all sufficiently deep sibling gaps
<=epsilon<delta_star along ONE truly marked FLAT branch force
the root identity. For any nontrivial root the NECESSARY condition is

    limsup_k d(B_k) >= delta_star

along every marked branch. This sharpens the previous threshold 1/2;
the existing source geometry and physical selections remain unproved.

## Exact rational tests and stronger finite acceptance

New locally executed AND Git-blob-byte-matched committed Agda script:
`scripts/check_horn_su3_sharp_sibling_arc_cut.py`
blob SHA `c436fb6870c453abd83ae21b0b4a15830172aaca`.

- epsilon=1/2: **c_arc²=15/16**, first exact squared root budget
  4*(15/16)^n<=1 at **n=22**.
- epsilon=31/60 (>1/2): **c_arc²=12914879/12960000 < 1**, first
  exact squared budget crosses at **n=398**. This is a new finite
  witness in the regime where the old 2 epsilon coefficient >1
  cannot contract.
- epsilon=13/25: c_arc²>1, deliberate boundary negative control.
- Symbolically **delta_star²=2-sqrt(3)** solves c_arc²=1.
- Explicit SU(3) matrices verified numerically at five rational gaps,
  for two values of the sharpness parameter t. Mathematical proof
  is the operator identity above, not the sampled matrices.
- Curved-source conservative rational cap:
  if source gives sibling gap<=31/60 then c_arc<=999/1000.
  For a hypothetical source eta_k=10^-6 and n=1400, the recurrence
  `u_k<=eta+(999/1000)*u_(k+1)`, terminal cap 2,
  gives root bound <1. **This does not construct real H_k
  homotopies, physical curvature or observed signal.**
- Both old and new bounds correctly fail closed for d(B)=2.
- Existing uploaded `horn_sibling_optimal_stopping_audit.py` was
  executed locally: all exact Fraction acceptance tests PASS. It is
  corroborating user-provided source, not ours to re-attribute.

Lean PR #84 new `Integration/DASHITOE/HornSharpSiblingArcCut.lean`:
source-written exact coefficient-square arithmetic, rational cap,
finite 22-stage and selected-root conditional rejection. The
full SU3 spectral/operator-norm bridge is presented as a clearly
EXTERNAL analytical premise; no Lean/Lake typecheck was available.
This avoids promoting a rational computation into a kernel proof of
SU3 matrix inequalities.

## Geometry: stronger same-object clearance and C3 donor

Hatcher explicitly constructs compact nested handlebodies
X_(n+1) subset X_n, limit B=intersection_n X_n, and increasing
exteriors Y_n=R3\\X_n. If a **genuine, marked** finite-stage
meridian gamma_w is first certified to avoid ALL of X_n, then:

    gamma_w subset Y_n subset Y_m subset E=R3\\B  for all m>=n.

If the loop trace is compact, X_n is compact and the two are
disjoint, the trace has POSITIVE distance from X_n and therefore
from B. **No separate future-horn clearance check is required.**
But checking avoidance of a nearby *single* tube is insufficient:
other components of X_n could intersect the loop. Exact selected
free-group generator marking and rectifiable length also remain
required independent premises.

Existing PR #1244 constructs R(x,y,z)=(z,x,y) and three satellites
9e_i. R is a rigid Euclidean isometry, R^3=identity. Once ONE
sector-specific loop/marking/length/clearance certificate is proved,
the other two follow by this actual rotation, instead of three
independent Euclidean embeddings. It is still necessary to transport
the marked group map equivariantly, not merely rotate a Cantor address.

New Agda #1249 `DASHI/Unified/HornStageClearanceC3SourceCutExact.agda`
source-writes generic nested-stage -> limiting-ball and all-later
avoidance implications, an exact order-three coordinate carrier and
a deliberately *uninhabited* source-marked-meridian requirement.

New executed AND Git-blob-byte-matched `scripts/check_horn_stage_clearance_c3_reuse.py`
blob SHA `f335654136997c2d985370f724a596b6d30b5cae`:
C3 rotation exactly preserves coordinate norm; 40 hypothetical
round meridians have decreasing 2*pi*r length and positive local
clearance; full-stage crossing-tube and high-winding negative controls
PASS; synthetic finite nested-set avoidance PASS.

This test **does NOT construct Hatcher's source-linked generators**:
the three missing pieces are (1) real stage-wide avoidance,
(2) exact conjugacy/marking in Hatcher's pi1 generator tower,
(3) actual Euclidean arclength for that SAME based meridian.
A round circle around an arbitrarily drawn tube is not source proof.

## Pareto / Ibrahim / snowball dependency ledger

P0 (one source object, highest fan-out):
PR #1244's **actual Hatcher sector** local Z-block -> explicitly
source-marked round/rectifiable meridian with finite-stage
avoidance. The nested-stage and C3-isometry lemmas then discharge
future clearance and other two sectors automatically. Do not
substitute Antoine necklace, clopen endpoint cylinders, Hatcher
word alone or diameter for metric loop length.

P1:
Actual source-based homotopy of parent to transported commutator
inside Y_n/E, Jacobian area and transported curvature integral.
Only real eta enters the strengthened curved arc envelope. Unitary
flat-bundle existence on the open exterior is already a valid positive
control, not a bounded compatible physical gauge-potential receipt.

P2:
Source action, regularity and charged matter, gauge-invariant
multi-scale observable vs ordinary punctured-ring and F2 controls.
Flat SU3 pure-gauge n/r norm negative control in existing #1249
prevents any norm-grow-to-curvature or energy-singularity promotion.

P3:
Native Agda and Lean kernel checks of NEW modules; not run.
All original/derivative publication and PR source identities are
kept separate. Claim existence, original testimony, independent
mathematical derivation, exact script receipt, kernel certification
and physical measurement are distinct evidential types.


## FINAL PARETO IMPROVEMENT: direct commutator and one-stage selected-W curvature cut

**Important correction to interpretation of the n=22/n=398 certificates above:**
those are EXACT **product-only infinite-branch** thresholds if all
sibling gaps are bounded by epsilon and only the multiplicative
step is used. They are NOT the earliest source rejection when the
very first sibling already satisfies that gap: the sharper DIRECT
one-step inequality can reject W immediately. In particular
epsilon=31/60 gives direct c_arc(epsilon)<1, contradicting selected
d(W)>1 already at level one. Never present the n=398 product test as
an optimal finite source depth.

### Direct theorem and sharpness (no chosen-child factor)

For the same lambda=1-delta²/2 and delta<=sqrt(2), conjugation is
an operator-norm isometry. Thus for every unitary A,B,

    d([A,B]) = ||A B A^-1 - B||op
             <= ||A(B-lambda I)A^-1||op + ||B-lambda I||op
             <= 2 delta sqrt(1-delta²/4).

This is sharp **exactly** within SU3 at each fixed delta:
B=diag(e^(i alpha),e^(-i alpha),1), delta=2 sin(alpha/2),
and A the 90-degree exchange of the two eigenvectors with det A=1.
Then [A,B]=B^-2 and d([A,B])=2 sin(alpha) equals this cap.
It applies symmetrically to BOTH original Hatcher children under
the actual flat source commutator equality.

### Exact selected-W first-child floor

The earlier source-independent trace Frobenius certificate for W
was r=854996726408/648677790003, with d(W)^2>=r.
For delta=3/5, the sharp direct squared cap is

    c_arc(3/5)^2 = 819/625
    r - 819/625 = 3105843992543/405423618751875 > 0.

Therefore for the actual selected W= [A,B], **BOTH** child gaps
MUST satisfy d(A)>3/5 and d(B)>3/5. An exact rational
stronger bound from the same certificate is >6019/10000;
the boundary where the lower r meets the direct squared cap is
approximately 0.60194456. This is a necessary numerical property
of any abstract source-marked selected-W representation, NOT
a measured meridian length or new theoretical neutrino observable.

A source-compatible locally bounded connection M and TRUE child
meridian length L_child would obey d(child)<=M L_child.
Consequently any actual source loop with M L_child<=3/5
**rules out selected W immediately** (flat case). Two-sided
first-generation depth is unnecessary for *rejection*, though both
child lower bounds hold for any possible realization.

New Git-blob-byte-executed exact program:
`scripts/check_horn_su3_direct_child_gap_floor.py`
blob `7421fd621cd264ccb984442c8abc3bec74aeae92`, local PASS
exact Q calculations and SU3 spectral-swap matrix family;
the toy metric L=1/4,1/8 test is NOT source geometry.

### ONE-STAGE nonflat Stokes margin: exact rationals, no radicals needed

For a CURVED connection, the actual based root differs from the
commutator of transported child Wilson loops by eta, so

    d(Wroot) <= eta + c_arc(delta_child).

The root and child have strict rational enclosures:

    r > (287/250)^2,
    c_arc(3/5)^2=819/625 < (229/200)^2,
    229/200 + 3/1000 = 287/250.

Hence a genuine source step satisfying BOTH

    d(child)<=3/5   and   eta<=3/1000

contradicts the selected W, with NO recursive length rate,
no 2^n budget, and no all-level source Stokes data. The eta
must come from an actual source-based homotopy and the chosen
connection (possibly a transported curvature-area cap K*Area);
it CANNOT be set by abstract pi1 relations alone. For the
flat case eta=0 automatically.

New byte-executed committed program
`scripts/check_horn_selected_w_one_stage_curved_cut.py`
blob `c42ddbc62cf15e97d3f44542bda2dd0a018c8f02`,
local PASS exact bound, synthetic metric+area budget and larger
eta fail-closed countercontrol. Lean #84
`HornSharpSiblingArcCut.lean` now source-writes conditional exact
selected-W child floor and curved one-step scalar contradiction;
the true SU3 matrix norm, metric meridian, based Stokes and Lean kernel
remain separately unverified.

### Final source-specific blocker under Pareto/Ibrahim

P0: identify **ONE** actual Hatcher first-generation child meridian
with correct generator/conjugacy, whole-stage X_1 avoidance and
physical Euclidean arclength. Using the selected W norm r,
the immediate FLAT acceptance boundary is simply M*L<=3/5.

P1: for the curved consumer, supply the SAME source-based parent to
child-commutator homotopy with eta<=3/1000. The nested X_n clearance
and rigid C3 transport are reusable from the existing Hatcher and
#1244 geometry once ONE source-marked local loop has been constructed.
Do not promote any synthetic curvature K, area, radius, or M to
the source actual gauge configuration.

The previous asymptotic sibling-tail theorem is still a valid more
general result for **arbitrary nontrivial roots** and variable
sibling gaps, but it is no longer the highest-Pareto acceptance
test for this particular selected W.
