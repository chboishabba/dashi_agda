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
