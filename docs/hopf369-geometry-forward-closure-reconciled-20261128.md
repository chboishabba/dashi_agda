# Hopf/369 Einstein–Israel: geometry-first closure roadmap, reconciled 2026-11-28

**Canonical short control document.** Historical/source/attribution ledger:
[`docs/c3-hopfion-abha-prior-art-maxcut-20261125.md`](c3-hopfion-abha-prior-art-maxcut-20261125.md).
Source branch: [PR #1554](https://github.com/chboishabba/dashi_agda/pull/1554),
`research/c3-hopfion-abha-prior-art-20261125`.
Default branch is **master**, not main. All new proof source remains committed in this PR.

## 1. Reconciliation receipt and authority boundary

- At the 28 Nov audit, comparison `master...research/c3-hopfion-abha-prior-art-20261125`
  reported **382 ahead / 40 behind** (the subsequent BR79–82 commits further increase ahead).
  Reverse comparison identified 29 changed master-path entries, predominantly
  YM/Balaban source and YM roadmap files; no original Hopf/Israel paths appeared
  among those entries. Do not claim a clean or complete rebase, or treat this
  spot audit as exhaustive historical proof.
- Existing direct reference/donor PRs inspected: [#1504](https://github.com/chboishabba/dashi_agda/pull/1504)
  (merged; classical AdS5/Israel scalar TT and source distinction),
  [#1508](https://github.com/chboishabba/dashi_agda/pull/1508) (merged moving TT),
  [#1512](https://github.com/chboishabba/dashi_agda/pull/1512) (merged moving Neumann/FV/SBP),
  [#1547](https://github.com/chboishabba/dashi_agda/pull/1547)
  (open F8 material Ward, Gauss–Israel BIDI, signed wall energy and receiver;
  inspected HEAD d368d9728b55),
  [#1527](https://github.com/chboishabba/dashi_agda/pull/1527)
  (open F8 dual-Weyl/normal geometry),
  [#1460](https://github.com/chboishabba/dashi_agda/pull/1460)
  (open Lorentz directional and Hodge donor) and
  [#1291](https://github.com/chboishabba/dashi_agda/pull/1291)
  (open hyperfabric/369 source-indexing).
  Reuse actual source definitions, signed gauges and negative controls; none
  supplies a *source-identical* nonlinear Hopf Einstein–Israel continuum
  well-posedness theorem merely by similarity.
- **Prior scientific attribution:** classical ADM initial constraints,
  Gauss–Codazzi/Israel, contracted Bianchi, warped products, Lax–Milgram,
  sub/supersolution/Harnack/Schauder, York/Hodge, Bel-type energy and
  vector-field multiplier identities are prior mathematics. Credit original
  external physics authors (as in P0AK/F8 source ledgers). DASHI contribution
  is the exact source-indexed parameter choice, geometric/negative-control
  crosswalk, finite certificates and any genuinely new proved weld. Do not
  attribute a physical law or theorem to JMD without source evidence.

## 2. What is ALREADY CONSTRUCTED: do not reopen

| Layer | Existing owners and actual result | Authority/limitations |
|---|---|---|
| Reference AdS5 and tension | `scripts/check_hopf369_p0ak.py`; original b=4/5 cosh(n-log2), L=2 log2, h0=4/5, full Ric(g5)=-4g5, fixed pressure/jump, lapse and reference normal bound | Exact source formulas and historical local tests; not a nonzero Hopf spacetime |
| Nonzero **spatial** constraint | P0 AN/BF/BK/BE/BJ, BL `check_hopf369_p0bl*.py` weak inverse/coercivity, BM `check_hopf369_p0bm*.py` fixed-measure monotonicity, BN `check_hopf369_p0bn*.py` ordered interval barriers and exhaustion/regularity argument | BN11 **conditional analytic existence** of R(h)=-12 nonzero, 4D Riemannian H3×S1 spatial data, cited classical regularity and interval assumptions; not a full spacetime theorem. BL/BM estimates do NOT automatically certify unique membership of BN solution in BM's narrow tube |
| Spatial seam & higher corners | BE + BO/BP/BQ `check_hopf369_p0bo*.py`, `check_hopf369_p0bp_br.py`, `check_hopf369_p0bq_br.py` | Spatial Israel, log-lapse Hermite, normal third/fourth jet repairs and finite shell/wave examples. Full spacetime corner sequence and norm tame control unpaid |
| Real two-chart physical boundary | BR26/32/33, `check_hopf369_br_two_chart_repair.py`, `check_hopf369_br_physical_boundary_repair.py`, BR34 `check_hopf369_br_warped_physical_attachment.py` | Original D/E 30 metric and 10 gauge row maps, mean force, frozen exact inverse; D and E remain distinct |
| Bulk/constraints and source geometry | BR4/14/15/29/31/37 plus `check_hopf369_br_curvature_energy.py`, `check_hopf369_br_holonomy_exterior.py`, `check_hopf369_br_tangential_hierarchy.py` | Original 15 metric, 5 harmonic, 35 Weyl, 9 projected zero modes, normal holonomy and AdS exterior; BR37 damped frozen inverse has Q-dependent losses; BR29 rank-12 **chosen wall-only Gram** obstruction is not a universal no-go |
| Actual nonlinear wall and full row source | BR48–78, especially BR59–64 shape/junction/Codazzi reverse-solve; BR65–67 second-warp/mean Israel source; BR68–72 original combined D/E time jets; BR73–78 normal-frame energy, nonlinear Gauss/Codazzi and vacuum tension Ward | Many constructive scripts and Agda source bodies **COMMITTED_UNRUN / PENDING_KERNEL**. A record containing an uninhabited proof field is not that proof |
| Reused F8 methods | #1547 `check_f8_gauss_israel_energy_weld.py`, `check_f8_material_full_ward.py`, `check_f8_harmonic_material_seam.py`, `check_f8_reciprocal_wall_energy.py`; #1512 moving flux/SBP | Exact F8 energy/constraint BIDI donor; its signed wall Hessian may be indefinite and its finite TT receiver is not the present coupled Einstein IBVP |

**New direct source weld BR79–82 (this roadmap pass):**
- BR79 `scripts/check_hopf369_br79_bn_adm_initial_bridge.py`: BN's
  R(h)=-12 is precisely the **time-symmetric (K_init=0) 5D vacuum
  Hamiltonian**, with all four momentum equations zero. For nonzero K,
  require R+12=|K|²-(tr K)² and momentum; never silently treat BN as
  an arbitrary-K solution. Native owner `OriginalP0BNTimeSymmetricInput`
  has a genuine proof-body forwarding the same original scalar witness.
- BR80 `scripts/check_hopf369_br80_adm_energy_current.py`: first-jet
  independent-nonlinear ADM **normal-frame positive current**. For normal
  spatial metric a², N>0, normal shift v, w=u_t-vu_n and q=u_n:
  ```
  E=(w²/N²+q²/a²)/2, J^t=-aE, J^n=vaE+qw/a
  (sqrt|g| Box u) = -∂t(aw/N)+∂n(avw/N+Nq/a)
  ∂t J^t+∂n J^n
   = (sqrt|g| Box u)w/N+(a_t-v a_n-a v_n)E -N_n wq/(Na).
  ```
  Exact general first-jet algebraic residual is `q*(p_n-q_t)/a` and
  vanishes for a genuine C2 same field. The current is independently
  reconstructed from T^mu_nu X^nu. This provides actual nonfrozen
  source terms for BR44, **not** the 15-component Einstein connection
  energy estimate or boundary coercivity.
- BR81 `scripts/check_hopf369_br81_existing_ak_bn_lapse_bridge.py`:
  existing P0AK reference spatial h=dn²+b² gamma_H3 is Ric_h=-3h,
  scalar -12; the positive N=b/(h0 z) satisfies Hess_h N=Nh and ΔN=4N,
  with time-lapse Israel jump [∂n log N]=j=-6/5 and fixed tension.
  This **static reference lapse** is stronger than the BN scalar
  constraint. Nonzero BN solution should use the **dynamic Cauchy
  evolution route**, unless an independent static lapse Hessian equation
  is actually solved. The existing BE log-lapse corner is not proof
  of a static Einstein spacetime.
- BR82 `scripts/check_hopf369_br82_glancing_loss.py`:
  `s=σ+iω, |ξ|=ω` gives `|ℓ|⁴=σ⁴+4σ²ω²`. Along the ray
  `r=ω/σ>=3`, `r²/5 <= Q_spatial⁴ <= r²/4`. The **particular**
  BR37 M⁴/M² chart factors require at least quadratic/linear
  high-frequency powers on this ray; this is **not** proof that
  an improved adapted symmetrizer cannot be uniform. It is an exact
  geometric regularity budget for the subsequent variable microlocal
  estimate, not an arbitrary four-derivative guess.

## 3. One ORIGINAL theorem target and its eight exact welds

**Goal:** Construct an actual 5D Lorentz Einstein solution on the two
physical material faces, `Ric(g)=-4g`, with a common induced timelike
wall, physically sourced Israel `[K]-h tr[K]+3j h-S=0`, appropriate
harmonic gauge, positive lapse/spatial geometry, spacelike wall normal,
reflecting weighted AdS exterior, and the nonzero Hopf spatial initial
data from BN. Preserve the periodic normal geometry and all scalar,
vector, Weyl and normal-holonomy modes. No claim that this final theorem
is currently proved or accepted.

1. **W0 – initial-data injection, not re-solve (BR79, P0BN/BO/BQ).**
   Provide an actual inhabitant of `OriginalP0BNTimeSymmetricInput`
   with R(h)+12=0, initial K=0 and the genuine *same h* and same
   spatial shell. Attach BE lapse Hermite, BQ fourth normal source,
   initial harmonic constraints and wall timelike-corner regularity.
   Required output: a 5D-compatible initial/boundary corner certificate
   of sufficiently high regularity, NOT a new scalar barrier.
2. **W1 – physical background/normal source identity (BR48–72).**
   Establish that the BR71/72 optical 30+10 D/E rows are the full
   Fréchet derivative of the **actual** nonlinear two-face
   `h,K,C` geometry with BR70 physical tangent/normal frame,
   BR65/66 source warp-acceleration and mean, BR67/69 higher time
   jets, BR74/75 ambient curvature, and original choice of lapse and
   density. Proof must be bidirectional and preserve nonzero
   graph/connection source; equality is not automatic from counts.
3. **W2 – normal-frame multiplier and differentiated energy (BR80).**
   Use the exact physical ADM multiplier current with its deformation
   work, BR43 H¹ two-sided trace premium, BR47 order-eight boundary
   source, BR76/77 moving flux with tilt, and BR41 signed wall work.
   Construct a real positive (not complex bilinear) weighted
   first-order 15+5 symmetrizer and prove its high-order commutator
   estimates on the **same** metric and source. BR73 removes an
   artificial coordinate-shift bound but does not make the boundary
   dissipative.
4. **W3 – actual glancing/Lopatinski closure (BR33/34/37, BR82).**
   Prove the full variable D or E physical boundary map yields a
   uniform or **quantified tame** trace estimate in damped sectors.
   BR37 establishes only a source-specific frozen inverse with
   glancing chart losses. A stronger estimator may be found through
   principal normal characteristic geometry or a symmetrizer
   different from the current Lorentz-boost proof. State actual
   frequency and derivative costs; do not assume `M^4/M²` bounded.
5. **W4 – physical subsidiary propagation, NOT a projected guess.**
   Weld BR55 contracted curved Bianchi source and BR78
   tension/matter Ward to BR74/75 full **curved ambient** Codazzi/Gauss
   and BR29 original 35D/nine-speed boundary carrier. Prove the
   physical source lies in the actual moving projected kernel under
   the real connection, plus uniqueness from zero initial subsidiary.
   Distinguish 5 harmonic channels from 9 Weyl zero modes.
   Preserve BR29 rank12 failure of a selected constant wall-only
   Gram as negative control.
6. **W5 – weighted reconstruction modulo exactly characterized kernel.**
   Reuse BS10–13/BR31/57 *forced normal* curvature-to-shear
   primitive, **including its moment M**, and construct the
   tangential Lorentzian York/Hodge inversion with explicit
   resonant scalar/vector modes rather than dividing through
   `Box-4c` or other resonances. Prove the weighted global
   exterior estimate and handle noncompact AdS radial boundary.
7. **W6 – nonlinear iteration with derivatives and constraints paid.**
   Construct actual linear solution operators and Picard/Nash–Moser
   tame bounds on a single anisotropic weighted space; choose a
   scheme consistent with W3's verified loss. Include two-side
   matter/tension transmission, real initial/corner data and
   BR42 continuation's lapse, wall normal gap, gauge, holonomy
   and exterior controls.
8. **W7 – acceptance and native proofs, no source promotion.**
   Discharge the original Agda certificates with genuine proof
   bodies (no postulates). Execute the local symbolic source
   checks and native kernel in bounded <=90 s stages with
   checkpointing; distinguish historical tested receipts from
   new unrun work. Do not use GitHub CI credits.

## 4. Immediate implementation order (large bites, not increments)

**Slice A – source closure:** W0+W1 together, reusing P0AK/BN/BO/BQ,
BR71/72 and existing F8 Ward/corner donors. Prove the real nonlinear
harmonic/Gauss/Israel wall source change of variables; reject an
unmatched induced metric and varying pure tension without Ward matter.

**Slice B – analytic bulk-boundary closure:** W2+W3+W4 together.
First derive the actual variable-current `T(X,.)`, then source-specific
15+5 connection estimate and original physical D/E boundary
characteristic inequality. Attach the real nonlinear wall-source
factor to the original BR29 projector; test the rank12 obstruction
against candidate positive bulk/wall cross terms.

**Slice C – terminal solution:** W5+W6+W7 together; construct weighted
curvature/gauge quotient and a loss-aware local solver with explicit
regularity margins, boundary/corner and exterior gates; then native
proof and local verification.

### Execution and non-promotion ledger

```bash
# No CI. Separate subprocesses <=90 seconds; creates local JSON receipts.
python scripts/run_hopf369_br39_42_bounded.py --part closure \
  --seconds 90 --output /tmp/hopf369-acceptance
python scripts/run_hopf369_br39_42_bounded.py --part frontier \
  --seconds 90 --output /tmp/hopf369-acceptance
```

The runner's source fingerprint covers both `check_hopf369_p0*.py`
spatial producers and `check_hopf369_br*.py` dynamic consumers,
other Hopf sources, native Hopf Agda owners and pinned local Artifacts.
A cached PASS must be invalidated by changes to the *original* BN
source, not only a new BR checker. Python tests and Agda kernel are
separate. The new BR79–82 files are **COMMITTED_PENDING_LOCAL_RUN**;
the P0AK static calculation and BR80 first-jet reduction had small
independent SymPy spot audits this turn, not an execution receipt for
the exact repository scripts. No full 5D theorem or Agda kernel
acceptance is asserted.


## 5. BR83–84 — full 5D current and original BN/BE timelike-wall corner

This second phase strengthens the **actual operator**, rather than adding generic carrier records.

**BR83 `scripts/check_hopf369_br83_full_5d_energy_current.py`:**
The source-independent classical differential identity behind BR80 is now
transcribed and independently checked on a genuine **five-axis** ADM
Riemannian-spatial block with non-diagonal positive 4×4 spatial H,
four nontrivial ADM shift components, independent first jets in all
five directions of N,H,v, and symmetric scalar Hessians. The full
contravariant stress `T=grad u tensor grad u -g^-1 g^-1(du,du)/2`,
future slice normal `X=(1,-v)/N`, and densitized current
`J=D T^mu{}_nu X^nu` are constructed **from the original ADM
metric**, including its actual derivative jets. The exact identity
being checked is
```
 ∂mu J^mu / D =
      (□_g u) X(u) + (1/2) T^{mu nu}(Lie_X g)_{mu nu}.
```
No scalar frozen coefficient is substituted for the true time,
spatial/normal lapse, shift, H-shear and Christoffel/deformation
terms. The checker has 15+5 independent original field-channel
stress evaluations, true moving material-wall flux and a nonzero
deformation negative control. It provides a genuinely five-dimensional
source **principal** energy geometry, but remains
COMMITTED_PENDING_LOCAL_RUN. It does not assert the full 15-coupled
Einstein connection is symmetric-hyperbolic or that the 30+10 physical
boundary map is dissipative.

**BR84 `scripts/check_hopf369_br84_bn_wall_corner.py`:**
The existing BN/BE/P0AK spatial/wall sources give a **complete
time-symmetric initial wall Israel corner** under the explicitly
prescribed zero-shift/static-material initial gauge, not a generic
positive-time boundary theorem. For the actual four-dimensional
timelike wall induced metric `h4=diag(-N²,H_3)`, positive N and
positive non-diagonal H_3, its physical wall second fundamental form
is
```
 Kwall_tt=-N ∂normal N,
 Kwall_AB=1/2 ∂normal H_AB .
```
Thus all ten original spacetime-wall Israel equations
`[Kwall_ab]=j h4_ab` are **bidirectionally equivalent** to
```
 [Kwall_AB]=j H_AB       (six existing spatial BN/BE components)
 [∂normal log N]=j       (one BE/P0AK lapse-Hermite corner)
 [Kwall_tA]=0            (three time-symmetric mixed corner conditions).
```
The last three are actual zero-shift/time-symmetric material **gauge
conditions**, not consequences of the scalar Hamiltonian. The
full four-dimensional trace reverse is
`[K]-h tr[K]=-3j h`; BR63's full Israel inverse recovers the jump
without a Fourier denominator. The checker retains mismatched-lapse
and mixed-velocity negative controls. For arbitrary initial shift,
wall motion or nonzero Cauchy K, the genuine additional mixed-corner
equations must be paid separately.

**Hard physical promotion boundary:** W0's *reference/time-symmetric
corner* now has a concrete source-equation back-solve from existing
P0 owners, but not yet an inhabitant of the original Agda all-corners
certificate or a high-order corner regularity estimate on the
nonzero BN constructed solution. The time-symmetric input condition
`K_Cauchy=0` cannot be promoted to a static lapse for nonzero Hopf
spatial metric. W1's original full D/E optical physical-wall
Fréchet equality still requires the real moving harmonic connection
and curved Gauss/Codazzi terms. W2/W3 need a positive *15+5*
weighted **full variable source boundary** energy/Kreiss estimate,
not just BR83's physical scalar-principal current.

Updated local acceptance:
```bash
python scripts/run_hopf369_br39_42_bounded.py \
  --part closure --seconds 90 --output /tmp/hopf369-acceptance
```
It now includes independent BR79–84 stages, split all BR83 full
metric/channel/moving/negative cases, and the three BR84 corner/BIDI
negative cases. All original P0/BN producers are in receipt fingerprints.
No new source checkout or Agda kernel test was performed.

## 6. Exact next integrated terminal programme

The project does **not** need another original spatial scalar solver,
time-symmetric ADM Hamiltonian identity, fixed-reference AdS lapse,
standard nonlinear moving hypersurface shape operator, finite Israel
trace inverse or abstract signed hyperfabric. Those owners exist.

- **Real W1+W2 (same solution):** instantiate the BR71/72 D/E full
  metric+gauge rows from the *actual* nonlinear Ric=-4g unknown,
  matching the BR84 corners and BR83 current. In the exact variable
  ADM normal frame, compute all BR14/15 lower-order 15 metric
  Christoffel source matrices and all five BR55 subsidiary sources,
  then prove their real positive symmetrizer/commutator estimate.
  Explicitly include BR59/61 nonzero shape Hessian, BR66 warp-mean,
  BR69 Codazzi/mean, BR70 unit-normal frame, BR78 tension Ward and
  BR77 physical moving tilt.
- **W3+W4 (one boundary-source operator):** reverse-solve the BR37
  frozen D/E map with BR82's actual glancing ray and construct an
  adapted microlocal estimate (or state exact positive loss if truly
  unavoidable). Attach the **same** actual 35D BR29 physical Weyl
  projector source and curved Bianchi to BR74/75 nonlinear
  Gauss/Codazzi, distinguishing nine zero-speed modes from five
  harmonic modes and retaining rank12 wall-only Gram refusal.
  A failed frozen or finite wall-only Gram does not prove the
  full coupled boundary estimate impossible; test bulk/wall
  cross terms and choose D/E source allocation accordingly.
- **W5–W7 (constructive completion):** use existing BS13 forced
  normal shear primitive with its holonomy moment; provide
  tangential York/Hodge resonance-aware gauge reconstruction and
  reflecting AdS exterior. Construct an actual loss-aware
  continuous time solution map from BN/BE/BO/BQ compatible
  initial data and uniform source estimates. Discharge native
  Agda proof certificates and local source checks in bounded
  checkpointed runs, never GitHub CI.

**Status/attribution:** BR79–84 source is committed. The short
independent static-lapse/SymPy and first-jet algebra identities were
checked in this turn. The repository scripts themselves, larger
full-dimensional symbolic suites and native Agda kernel are
NOT yet accepted. The final nonlinear 5D Einstein–Israel
well-posedness theorem remains outstanding, precisely at the
operator/estimate/continuation welds above.


## 6. BR85–88 — connected W1–W4 pass (28 Nov)

New executable owner: scripts/check_hopf369_br85_88_geometric_weld.py.
Status: COMMITTED_PENDING_LOCAL_RUN, except independent local principal
matrix calculations (not an execution receipt for this file). No Agda
kernel acceptance. Retain the classical attribution and all earlier
negative controls.

- **BR85/W1:** explicit non-Gaussian moving graph first variation of the
  induced metric, normalized Hessian/connection Israel K, contracted
  coordinate gauge and physical tangent/normal gauge frame. Both face
  first jets share the induced h. Differentiate BR63 trace-reversal and
  its inverse including the derivative of h^{-1}; use an independent
  exact rank-one metric path oracle. This is a directional source
  certificate; full arbitrary-background BR71/72 row equivalence,
  including mean and allocation-specific conditions, remains open.
- **BR86/W2:** real positive covector fibre metric M=g^{-1}+2XX^T and
  symmetric-tensor induced 15-channel Gram, attached to the 5-channel
  covector Gram. First-order normal/spatial principal symbol is
  symmetrized by diag(1,H^{-1}); the actual Levi-Civita connection
  induces coupled symmetric-tensor connection work
  dG-A^T G-G A. Exact divided time-jet product/commutator through order
  eight. Need integrated mixed-spatial coefficient bounds, physical wall
  energy/trace closure and actual same-solution coefficients.
- **BR87/W3:** directly invert the ORIGINAL BR34 normalized flat
  decaying half-space principal row maps, retaining D/E distinct.
  Set z=((w+w^{-1})/2,(w-w^{-1})/2,0,0), plus derivative=-value,
  minus derivative=+value, j=0 in normalized principal symbol.
  Along s=1+i omega, xi=omega, w=ell, w^2=1+2i omega.
  Both inverse products are checked exactly. Every denominator is
  constant times w^a(w^2+1)^b; |w|>=1 and |w^2+1|>=|w|^2.
  Coefficient l1 gives an explicit row-sum bound. Exact maximum powers
  of |w| are D metric 3, D gauge 2, E metric 1, E gauge 1, with
  nonzero leading inverse coefficient. Thus E has a half-derivative
  normalized principal ray cost, D has 3/2 and 1. This is stronger
  than BR37's chart upper bound on this ray, NOT a global Kreiss
  theorem or finite warped DtN estimate. Do not change physical
  allocation without W0/W1 compatibility. Next: perturb the actual
  BR34 warped finite-interval DtN in the E norm, preserve the row
  scaling, extend to all damped sectors and variable coefficients.
- **BR88/W4:** use the original BR29 rank-nine projector and the actual
  induced bivector frame rotation in the spatial normal/tangent plane.
  Its derivative is the commutator with the compressed 35D geometric
  generator; transport the source as well as projector. Prior to
  subsidiary uniqueness Ric=-4g+D, D=S(C)+Ered; Schouten=-g/2+
  (D-g tr D/8)/3. Mixed Codazzi Weyl source retains the Ricci defect,
  not its prematurely zeroed vacuum value. Need full contracted
  Cotton source and physical wall projected kernel + uniqueness on
  the same solution. A general source fails P0*f=0, explicitly tested.
- Repair existing BR55 vector-versus-square-zero assertions in
  curved and boundary checks; no change of mathematical claim.

**Revised remaining critical cut:** W1 full D/E Jacobian attachment ->
W2 actual high-order wall/bulk estimate -> W3 warped E tame resolvent ->
W4 sourced subsidiary uniqueness. W5/6 remain dependent on this
chain; no new scalar solve, no promotion from pointwise/ray checks.
Local runner closure partition includes BR85–88 in independent bounded
stages. No GitHub Actions run requested.

### BR87 opposite-sector obstruction and exact bounds

Independent local SymPy 1.14 transcription of the BR34 normalized
principal row formulas (not the committed script) returned exact
row-sum coefficient bounds 19, 4, 31/4 and 11/2 for D metric, D gauge,
E metric, E gauge respectively, multiplying |w|^3, |w|^2, |w|, |w|
on the damped glancing ray. The exact inverse also has a contrasting
sector: s=sigma>0 real, |xi| tends to infinity; then
w=(sigma+i|xi|)/sqrt(sigma^2+|xi|^2) -> i and
w^2+1=2w sigma/ell -> 0. At w=i there are **12 metric E and 8 gauge E
nonzero simple pole residues**, but zero in both D matrices. Thus E's
improved glancing loss is NOT a globally superior fixed allocation.
Its opposite-sector normalized inverse cost is at least |xi|/sigma.
Do not frequency-switch physical D/E rows without an equivalence or
well-posed mixed-allocation construction. Compare global tame norms in
both sectors; keep original physical gauge and initial-corner conditions.
The BR87 runner checks these residues and exact constants. The actual
repository checker remains COMMITTED_PENDING_LOCAL_RUN.


## 7. BR89–91 — warped adapted inverse and same-metric defect source

Reuse BR37 (existing exact Lie-algebra and finite-chart intertwiner),
BR34 actual warped DtN, BR35 rest-frame Green contraction, BR63/78
Israel and Ward, BR29 original Weyl carrier. Do not reopen those owners.

**BR89 / W3: positive adapted frozen reference norm.** In the scaled
D row coordinates let T transport all D rows, U transport endpoints,
D(z) U = T D(ell). For E, reorder its replacement row into the
omitted temporal D slot r. Let g0 be the scalar replacement row
at rest, l=g0 D(ell)^-1 and v=T^-1 e_r. Rotational covariance
gives l(v)=a l(e_r), a=s/ell. With f0 the E data with its omitted
D slot set to zero and g the replacement datum, the full inverse
is exactly
  y=T^-1 f0; lambda=(g-l(y))/(a*l(e_r));
  u=U D(ell)^-1 (y+v lambda).
This is the existing BR37 rank-one update performed in the **rest**
data and endpoint norm, not a new physical allocation. In positive
Hermitian endpoint norm ||U^-1 u||, D is bounded by its rest constant;
E satisfies
  ||U^-1 u|| <= ||D(ell)^-1|| [||y||+
     max(1,|xi|/|s|) (|g|+||l|| ||y||)/|l(e_r)|]
using spatial rotation to align xi. This is conditional on the
existing BR35/37 rest inverse and nonzero rest replacement response.
No product of two additional large Lorentz matrix norms is necessary
in this adapted norm. It is frequency dependent; it is NOT a local
physical energy or uniform Sobolev norm. BR87 physical coordinate
powers and the E low-temporal pole remain valid. New checker uses
actual BR34 warped collocation (three frequency sectors, both fields)
and tests full two-sided inverse, not just one forced solution.
Numerical checks pending; require interval or analytic DtN acceptance
for any continuum promotion. Variable localization needs estimates
of U, T, their derivatives and commutators, and the exact physical
boundary source; no claim that this is already paid.

**BR90 / W4: full defect-aware Gauss–Israel jump.** Use fixed signed
j=-6/5, matched h, [K]=jh, mean M, D=Ric+4g. Covariant Codazzi
gives [D_na]=0 for constant tension. Scalar Gauss gives
  [D_nn]=tr_h[D_ab]+6j tr_h M.
Tangential Riemann jump is -j(h wedge M); mixed jump vanishes;
electric jump is [D_ab]+j(2M+h tr M). Subtract g wedge the
actual Schouten defect (D-g tr D/8)/3 to reconstruct all 55 packed
curvature slots. The result is algebraically Weyl and the Ricci
contraction is the original defect. Its tracefree M component is
exactly j times the existing BR29 jump map; the pure trace mean
cancels only after the scalar Gauss relation has been paid.
The defect-to-Weyl map has rank 9; its P0 projection rank 6;
An projection rank 8. P0 kernel on the ten tangent defect channels
is four-dimensional: the three time-space mixed entries and
pure Lorentz trace. Hence even physical matched Israel with
constant tension does not algebraically remove the zero-speed
defect. Do not equate these ranks to evolution-mode counts.

**BR91 / W4: actual differential Cotton source.** At an orthonormal
point retain all 75 covariant first jets of D. Contracted Bianchi
imposes five independent equations, leaving a 70-dimensional jet
space. Differentiate the Schouten defect and use BOTH Weyl divergence
and full differential Bianchi to construct electric and magnetic
forcing in BR29's actual 100-slot embedding. Compress by G^-1 X^T.
The resulting compatible Cotton map has rank 25 and its projection
onto P0 has rank 9. The ranks remain 25/9 on the smaller image of
D=S(C) constructed from actual symmetric Hessians of the five gauge
components with all five homogeneous principal wave constraints.
The exact contraction identity on that Hessian carrier is
  div S(C) - 1/2 d tr S(C) = Box C/2.
Thus no unconditional P0 Cotton cancellation is available even on
wave-compatible gauge jets. The proper proof order is:
  (i) construct the reduced metric using actual W1–W3;
  (ii) prove the homogeneous gauge wave IBVP with zero initial and
       compatible physical boundary data on that same reduced metric;
  (iii) infer D=0 for Ered=0; then the Cotton source and defect jump
        vanish and BR29 vacuum subsidiary identities apply;
  (iv) if evolving independent Weyl variables, separately prove
       their equality to geometric curvature using the coupled
       subsidiary flux/trace estimate. Preserve BR29 rank12
       obstruction to the chosen separated wall-only Gram.
This is not a no-go for the final physical theorem, but a no-go
for using contracted Bianchi alone as a projected-source-zero proof.

Independent local SymPy 1.14 transcription of original BR29 packed
carrier and these source maps returned ranks 9/6/8 and 25/9, including
the gauge-Hessian wave-compatible 25/9 and exact contraction factor.
This was not a byte-identical run of the committed new checker.
BR89 algebra/warped and BR90/91 committed checker stages are pending.
No native kernel or CI run. Runner closure includes BR89–91.


## 8. BR92–95 — same-metric subsidiary, signed D fold and glancing derivatives

BR26/BR5 already prove gauge uniqueness for the old six-value allocation,
but BR32 proves its reduced metric principal problem rank deficient.
BR33 fixes this with physical mean force and different D/E conditions.
Do not import BR26 energy into D or E unchanged. Reuse BR33/68/70/86/89.

**BR92 (W4a):** Ered=Ric+4g-S(C), S=symgrad C. The half trace reverse
TR(Ric+4g) is divergence free in five dimensions. Metric compatibility
and the covector commutator give
  div(S(C)-(1/2)g div C)=(Box C+Ric(C))/2,
  Box C+Ric(C)=-2 div TR(Ered).
Use the actual reduced metric Ricci coefficient, not -4 before C=0.
Correct BR55's misleading full-trace comments (native traceReverse5
already uses half). Exact non-diagonal Lorentz 2-jet oracle computes
Christoffel, its derivatives, Ricci, 125 covariant Hessian entries and
five equations, with both incorrect shortcuts explicitly refused.

**BR93 (W4a):** In a Gaussian collar with common induced h, [K]=jh,
constant j, tr_h M=0, fold periodic n in [0,L] to r in [0,L/2].
Write p=C(r), v=R C(L-r), R=diag(1,1,1,1,-1), A=p-v, B=p+v.
Use actual reflection differential in non-Gaussian charts. Thus
A_a=[C_a], A_n=C_n^++C_n^-, B_a=C_a^++C_a^-, B_n=[C_n].
Radial jets A_r=C'_++R C'_-, B_r=C'_+-R C'_-.
BR33's exact physical derivative rows become
  B_{a,r}+D_a B_n-2 M_a^b A_b-j B_a=0,
  A_{n,r}-D^a A_a-2j A_n=0.
BR68's physical correction from -j/2 is retained. D value conditions
A_a=0, A_n+B_n=0; E instead A_i=0,A_n=B_n=0, no A_0 condition.
At smooth midpoint, A_a=0, A_{n,r}=0, B_n=0, B_{a,r}=0 by parity.
The full signed fold and its inverse are exact, no frequency division.

**BR94 (W2/W4a): conditional analytic uniqueness proof.**
Assume a GIVEN regular reduced solution with reflection-invariant
metric and therefore reflected full covector wave/Ricci operator,
positive lapse/coercive spatial metric, bounded first/lower coefficients,
constant j, D physical BC and zero initial C and time derivative.
Use boundary-adapted slice/time multiplier tangent to wall and midpoint
with normal spatial there, and homogeneous nonincoming exterior flux;
noncompact domain additionally requires justified weighted integration
and trace bounds. Reflection invariance is not asserted for nonzero BN.
Naturality makes A and B independent homogeneous normally hyperbolic
systems. A has four Dirichlet components and A_{n,r}=2j A_n at wall,
plus the above midpoint homogeneous D/N conditions. The BR86 positive
component/fibre energy (normal/tangent block diagonal at wall) plus mass
has Robin outward power -2j weighted A_n partial_t A_n; add the signed
boundary potential j times the weighted A_n squared. Weight derivatives
yield only quadratic trace work. Treat covector connection terms as
bounded lower-order coefficients on this given geometry. Dirichlet
velocities and Neumann derivatives contribute zero flux.
For a>0, epsilon>0,
  |u(0)|² <= epsilon int_0^a |u'|² +
              (1/a+1/epsilon) int_0^a |u|²
by averaging u(0)^2=u(r)^2-2 int_0^r uu' and Young. Use actual
metric/weight comparison constants, choose epsilon small enough to
absorb negative Robin derivative charge, then a sufficiently large
positive bulk mass to dominate its negative value charge. Energy is
equivalent to H1 x L2. All remaining lower-order and boundary weight
work is bounded by that energy, so dE/dt<=K E and zero initial energy
gives A=0 by Gronwall. Now B_n=0 and B_{a,r}=j B_a; repeat the same
mixed D/R argument to get B=0. Reverse fold gives C=0. BR92 with
Ered=0 yields Ric=-4g; BR90/91 defect sources then vanish.
This is conditional uniqueness, not existence or acceptance for
original nonsymmetric BN data, not an independent Weyl proof.

**Exact general-background obstruction:** if reflected operators
Lp,Lm differ, Lbar=(Lp+Lm)/2, Delta=(Lp-Lm)/2, the equations become
  Lbar A+Delta B=0, Lbar B+Delta A=0.
Delta may be SECOND ORDER away from the seam, even though h matches.
A restricted constant face Gram G=[[a,b],[b,c]] in the scalar normal
subblock cancels D's free inward derivative only if b=c (flux has
(b-c)xy+2j c x²). Commutation with unequal diagonal principal speeds
forces b=0, contradicting positive c. This rules out that chosen
constant cross-face energy, NOT general microlocal symmetrizers.
Check actual BN/BQ reflection and gauge before attempting to instantiate
the cascade. Do not assume symmetry or switch to E.

**BR95 (W3):** With sigma=Re s>0, Z=max(|s|,|xi_i|), L=|ell|,
factor ell²=(s+i|xi|)(s-i|xi|) to obtain L²>=sigma Z. Independent
complex perturbations of the four z coordinates with |delta|<=sigma/64
give |delta ell²|<=8Z delta+4delta²<L²/4. Same holomorphic root chart:
|ell'/ell-1|<=1/4, |ell'|>=3L/4, |a'-a|<=|a|/3+1/48.
Since |1+a|>=max(1,|a|) originally, the perturbed Lorentz denominator
stays >=half that bound. |v|²<=1+|a|² at real frequency gives a
conservative 128Q row norm bound for perturbed boost and inverse;
rank-two lifts cost Q². Cauchy bounds fixed-metric frequency derivatives
by alpha! (64/sigma)^|alpha| times corresponding chart power.
This is a damping-scale bound, not conventional symbol order reduction
or control of variable metric derivatives. Indeed vary principal spatial
coefficient c², ell²=s²+c² k²; on s=sigma+i k, c=1,
  partial_c log ell=k²/(sigma²+2i sigma k).
For k>=sigma its squared modulus is between k²/(5sigma²) and
k²/(4sigma²): geometry derivative costs a full frequency power here.
No ordinary zero-order localization estimate follows from BR89.
Need genuine variable glancing patches or coupled defect energy.

**Acceptance:** four independent bounded stages in runner.
Independent local SymPy checks passed BR92 general curvature and
negative controls, BR93 fold and shape, BR94 restricted Gram algebra,
BR95 lower glancing derivative inequality. One structural equality
needed expansion before passing. Exact committed checker and native
kernel unrun. Classical geometry and energy attribution retained.
No CI run requested; commit marked skip ci. Next: inspect actual BN/BQ
reflection data, either instantiate BR94 or close coupled second-order
parity defect; W1 curved D/E Jacobian, W2 actual metric energy, W3
variable localization, W4b independent Weyl, W5/6 exterior/existence
remain open.


## 9. BR96–99 — nonzero source reflection audit and full-continuity allocation F

**BR96 source audit.** Reopened original AN metric, BE seed/coupling,
BN interval/radial/verification, BO third-jet and BQ fourth-jet owners.
AN has a(x) independent of n with g_an/g_nn=a; b(n) is even around
L/2. Its nonzero signed amplitude changes under n->L-n, and the
original AN/BN tests explicitly compare +eps at n with -eps at L-n.
BE's odd second-jet lift f(n) multiplies an odd source correction;
the scalar factor and tangential-only BO/BQ repair preserve the
KK readback. Do not confuse signed covariance with invariance at
one fixed nonzero eps. Exact origin jets of AN rational pullback:
a(0)=(0,0,5 eps), (d a)_12(0)=50 eps=5/4 at eps=1/40.
For base-identity fibre reversal n->L-n+f(x), invariance of the
connection would require df=-2a, impossible where da !=0.
This is not a general all-isometry obstruction, and does not assume
BN existence beyond its conditional source proof. BR94 cannot simply
be instantiated on the actual nonzero fixed-source metric.

**BR97 / W1,W3: third candidate F, not a change to D/E.** Choose
same BR26 two-chart matched metric geometry and same BR33 physical
mean force:
 [h]=0 (10), [beta]=0 (4), [K]=jh (10),
 [C_a]=0 (4), [C_n]=0 (1), tau+ + tau-=0 (1).
Here C_n is physical unit-normal gauge in matching Gaussian trace
frames, not raw coordinate C_y. The full 5-component geometric
gauge continuity replaces D's one-sided normal Dirichlet. Unlike
BR26's rank-deficient six-value allocation, F keeps mean force and
only five gauge conditions. With BR33 common H, d=beta+-beta-,
b=beta++beta-, p=ell+-ell-, a=ell++ell-, finite flat T=ell tanh
and C=ell coth, the five gauge rows are ct=-z p-T b,
nn=T tr H+div d-T a, mean=-div b. Reverse solve for arbitrary
forcing R,g,nn,d0,f:
 H=-(R+z d0^T+d0 z^T)/(2T);
 p=(T f-div g)/q; b=-(g+zp)/T;
 a=tr H+(div d0-nn)/T.
The determinant is signed 2^14 T^14 q, nonzero on the damped
flat domain q=-ell². Gauge F keeps normal and tangent jumps,
then solves their sums by original BR33 Codazzi/Gauss suffix.
No temporal z0 divisor. The full 30 and 10 principal matrices
use actual BR34 rows, only replacing D's one-sided normal with
normal jump. Independent local SymPy 1.13.1 calculation of the
literal full row formula gave both inverse products for the four
rest/ray cases. Exact rest infinity bounds: metric 8, gauge 3/2.
On s=1+i omega, |xi|=omega, w=ell, exact Laurent inverses have
max powers 3 and 1, coefficient bounds 11 and 2 respectively.
No w²+1 denominator: no E opposite-sector temporal pole. This
is a source-compatible *candidate*, not yet a native original
F metric solution; W0 higher compatibility and W1 full moving
nonlinear Jacobian attachment remain. D/E retained unchanged.

**BR98 / W4a: conditional general-background uniqueness for F.**
Assume a given sufficiently regular reduced solution on the
actual two-chart material seam, with F boundary conditions,
constant pure tension, matched induced metric and normals,
compatible wall-tangent time multiplier with normal spatial
there, zero initial gauge and normal time derivative, and
homogeneous nonincoming exterior flux with justified weighted
energy/trace bounds. No normal reflection hypothesis.
BR92 gives homogeneous gauge wave with actual Ricci coefficients.
BR33/68 in common Gaussian trace coordinates gives
 [partial_n C_a] = 2j C_a,
 [partial_n C_n] = 4j C_n
since ALL five values match, tangential derivatives of jumps
vanish, [K]=jh and mean tau=0. In parallel-frame notation the
tangential covariant normal jump is instead j C_a: do not mix
those conventions. Common physical wall trace, time derivative
and positive weight/Gram are available via chart gluing and a
boundary-adapted positive component energy. Pick a smooth real
positive fibre Gram G, same on the two wall traces and block
diagonal in tangent/normal there; extend separately into each
bulk. Work in the Gaussian trace coordinate components, put
connection/curvature coefficients into bounded lower-order work.
The outward sum of both energy fluxes is
 -<partial_t C, G S C> with S=diag(2j,2j,2j,2j,4j),
including the common boundary density/lapse factor in G.
G S symmetric. Add signed wall potential (1/2)<C,G S C>;
its derivative cancels the velocity flux, leaving only
(1/2)<C,partial_t(G S) C>, controlled by H1 trace.
Use BR94 trace interpolation on either/both actual collars to
absorb negative derivative charge and select large bulk mass;
positive modified energy equivalent to H1 x L2 then obeys
dE/dt<=K E. Zero initial energy yields C=0 by Gronwall.
This conditional argument allows unequal reflected principal
operators: the energy is separate bulk energies plus COMMON
wall value potential, not a constant off-diagonal face Gram.
It requires the actual nonlinear geometric F boundary conditions,
regularity and weighted exterior hypotheses, not merely row count
or principal inverse. Once C=0, Ric=-4g and BR90/91 sources
vanish. Independent Weyl preservation remains distinct.
This is an analytic proof written in roadmap, not Agda acceptance.

**BR99 / W3: full frozen warped F route.** Use BR34 actual finite
warped optical DtN, BR35 Green bounds and BR37 Lorentz covariance.
At rest normalize derivative rows by |ell|=L and compare to
flat decaying principal matrix. Let delta bound the relative
endpoint derivative error including finite interval tails and
optical-to-parallel conversion. Exact F row norms give derivative
coefficients <=5 metric, <=2 gauge, and explicit j lower terms
<=3|j|/L and <=4|j|/L. Thus the rest Neumann factors are
 rho_m<=8(5 delta+3|j|/L),
 rho_g<=(3/2)(2 delta+4|j|/L).
If both <1, the rest inverse norms are <=8/(1-rho_m) and
(3/2)/(1-rho_g). BR35/37 existing rest estimates supply a
route to sufficiently large damping, but the exact F relative
error must be traced to its actual operator and accepted.
All F continuity/derivative rows transform as tensors,
covectors or scalars under BR37, including normal gauge jump
and mean. Hence global frozen F transport follows without E
rank-one temporal denominator; physical coordinate chart powers
remain metric Q^4/gauge Q² as safe BR37 upper bounds. BR95
variable localization defect still unpaid for metric evolution.
Do not claim variable-coefficient wellposedness from this route.

Acceptance: independent local full principal F matrices gave
rest 8 and 3/2, ray powers 3/1 and constants 11/2 (meaning
metric 11, gauge 2 separately), no w²+1 pole. This was a
transcription, not execution of committed checker. BR96 origin
calculation and BR98–99 source bodies, finite interval checker,
native F row/count bodies all pending exact replay and kernel.
No CI; commit marked skip ci. Keep manuscript provenance and
all D/E negative controls. Next max-cut: full F curved
Fréchet boundary/corner attachment; source-specific rest warped
DtN bound and actual variable reduced metric estimate; instantiate
BR98 on that same solution, then W4b–W6. Do not spend more
work trying to force original BN into a reflection-symmetric subclass.


## 10. BR100–103 — nonlinear F normal inverse, corner ownership, scalar wall wave and explicit warped bound

Reconciled BR26 material chart, BR70 physical frame, BR71/72 source
corrections, BR85 graph variation, BR96–99 F, BR4/20/24/25 and
BR79/84 initial data, BR35/37 warped Green/covariance donor.
Classical ADM/Christoffel, trace and wave transmission prior math;
DASHI-specific attachment to original signed allocation.

**BR100 (W1):** For g=h_ab(dx^a+beta^a dy)(dx^b+beta^b dy)+lambda²dy²,
lambda>0, common h,beta, independent lambda±, D_y=partial_y-beta.d,
the exact BR26 readback with source H is
 K=(h_y-L_beta h)/(2lambda),
 C_a=Gamma_a(h)-d_a log lambda+lambda^-2 h_ab D_y beta^b-H_a,
 C_perp=-tr_h K+lambda^-2 D_y lambda-H_perp.
Invert:
 h_y=2lambda K+L_beta h,
 beta_y=beta.d beta+lambda² h^-1(C_tan+H_tan-Gamma(h)+d log lambda),
 lambda_y=beta.d lambda+lambda²(C_perp+H_perp+tr_h K).
For arbitrary F residual R=[K]-jh, f=tau+ + tau-, c=[C_tan],
n=[C_perp], choose h-tracefree M0 and common gauge mean C0:
 M=M0+(f/8)h; K±=M±(jh+R)/2; C±=C0±(c,n)/2.
These give exactly the prescribed residuals and reconstruct all
30 normal derivatives; inverse takes mean TF shape and mean gauge.
Thus derivative map rank16 and kernel14=9+5 for all admissible
fixed matched h,beta,lambda and prescribed point-source; add 14
value rows. Local exact rational test with non-diagonal Lorentz
h, nonzero shift, lambda 2/3 and 5/4, independent tangent/source
jets checks full 5x5 Christoffel and K on both faces and ranks.
No claim that arbitrary off-matching value extension, moving chart
regularity, or full boundary symbol is already solved. BR70/85
supply frame and directional graph variation; actual material
straightening must transport source by inhomogeneous Christoffel law,
not assume solution-dependent gauge source remains algebraic.

**BR101 (W0):** BR84 full spacetime Israel follows from existing
time-symmetric spatial jump and log-lapse derivative jump.
BR4's mean d_n log N=-tr spatial mean enforces tr_h M=0;
initial vacuum constraints and prescribed gauge source give C=C_t=0.
These imply F order-zero corner under same-chart hypotheses.
Higher-order F difference vanishes whenever BOTH one-sided gauge
jets have been proved zero; cannot infer this just from D/E.
Reopen BR20/24/25 finite source and mean-acceleration repairs in
same chart at selected Sobolev order. BR100 highest normal-jet
decoder supplies algebraic lift, not time-evolution compatibility
or high-order bounds. No universal corner closure claimed.

**BR102 (W2/W3):** Homogeneous normalized flat principal F gives
 [H]=[b]=0, [H_n]=0, [b_n]=d_wall p, [l_n]=0, p=[l], l=p_nn/2,
 tr(H_n^++H_n^-)/2=div_wall(b^++b^-).
Set U=div_wall b-tr(H_n)/2 on each face. Then [U]=0 and sum U=0,
so U± vanish separately at wall. In common constant-coefficient
flat bulk U solves homogeneous wave by commutation. With zero
initial derivative data and compatible exterior Dirichlet-wave
energy gives U=0. Differentiate and use [H_nn]=-Box_wall[H]=0:
 [U_n]=Box_wall p.
For [b_n]=d_wall p+R and wave(H)=F_H with [H]=0,
 Box_wall p=[U_n]-div_wall R+tr[F_H]/2.
Thus flat homogeneous zero-data wall wave gives p=0; all 15
metric values and principal derivative jumps now match and bulk
energy gives uniqueness. This is conditional flat-model proof,
not variable existence; forced trace and commutator estimates
are separate. In particular U includes a normal derivative.

Exact restricted flux obstruction: with plus p_nn time velocity
only, compensate [b_n] by its gauge row and vary common p_nn
normal derivative d, independently of wall values. The power
coefficient of d is +/-G_nn,nn for any positive plus-face Gram.
No value-only wall potential cancels this. F gauge BR98 energy
cannot be repurposed directly as metric energy. The scalar
wall-wave factor is the genuine q denominator, not a fictitious
zero-speed residual. Construct curved U/wall source and augmented
energy/regularity, preserve variable principal commutators.

**BR103 (W3):** Reuse BR35 Green bound e=18a/(1-6a),
a=2c1/gamma+c0/gamma², metric (1536,30832/25), gauge
(8,1239/100). Reference optical interval length
2 atan(3/4)/(4/5)>1 by atan x>=x/(1+x²).
For Re ell>=gamma, finite flat DtN deviation relative to decaying
diagonal <=coth(alpha length)-1+csch(alpha length)
=2/(exp(alpha length)-1)<=2/gamma.
BR34 optical conversion costs <=13|j|/(4gamma) metric (R norm13),
3|j|/(4gamma) gauge. Thus delta_m=e_m+2/gamma+13|j|/(4gamma),
delta_g=e_g+2/gamma+3|j|/(4gamma). Use BR97/99 constants:
 rho_m=8(5 delta_m+3|j|/gamma),
 rho_g=(3/2)(2 delta_g+4|j|/gamma).
At gamma=10^7 both <1/4; rest inverse bounds <11 and <2.
Conditional on BR35 reference Green and BR97/99 constants,
BR37 Lorentz covariance transports all F rows, yielding frozen
Q^4/Q² physical inverse bounds with no E temporal pole.
BR95 variable geometry obstruction remains.

**Acceptance:** local SymPy 1.14.0 four bounded stages exit 0,
byte-identical Git blob 515f5ef6e11204956e821e00040c02c758c0463c.
Receipt committed. Native constructor source-written, kernel
unrun; no CI requested. Next P0 curved scalar wall-wave source,
coupled mixed-order estimate, moving chart Fréchet and same-data
selected-order corner, actual F reduced development then BR98,
W4b–W6. No W1–W3 full closure claimed.


## 11. BR104–107 — curved F wall-wave, foliation subsidiary and hidden trace

Reconciled actual BR26/100 material inverse, BR74/75/78 physical
Gauss–Codazzi and tension, BR92 same-metric Bianchi, BR98 F
continuous gauge, BR102 flat scalar wall factor, BR80/83 stress
current, BR43/44/56 trace/energy. No new scalar spatial solve.
Classical Raychaudhuri, Bochner, Hodge commutator, stress multiplier,
Lie derivative are prior mathematics; DASHI-specific attachment
to original F and signed nonzero Hopf carrier.

### BR104: exact curved normal curvature and scale wave

On each material collar let psi=log lambda, n=e^-psi(∂y-beta.d),
K=1/2 Lie_n h, tau=tr_h K, Q=C_perp+H_perp=n psi-tau.
D is the intrinsic Lorentzian leaf connection, a=∇_n n=-D psi
(spacelike normal sign); K² below is signed tr(h^-1 K)^2, not
an assumed positive Lorentz norm. The exact identities are
 Ric_nn=-n tau-tr(K²)-Box_h psi-<D psi,D psi>_h,
 Box_g y=-e^-psi Q,
 Box_g psi=(n psi)^2-tr(K²)+n Q-Q n psi-Ric_nn.
The last follows from scalar Bochner on y: Hess y has ttangent
block e^-psi K, mixed -e^-psi D psi, nn=-e^-psi n psi.
With Ered=Ric+4g-S(C), Ric_nn=n C_perp+
<D psi,C_tan>+Ered_nn-4, hence
 Box_g psi=tau n psi-tr(K²)+n H_perp
            -<D psi,C_tan>+4-Ered_nn.
The actual material acceleration term is indispensable: n of the
normal component is NOT the Gaussian extension derivative of that
component unless normal acceleration vanishes. Direct independent
full 5x5 Christoffel, Ricci, scalar Hessian calculation at a
non-diagonal Lorentz point with variable shift, scale and rational
2-jets passes all three curvature/acceleration/Bochner identities.
No use of Ric=-4g before C=0.

### BR105: nonlinear wall-scale jump equation

On F wall, same h and geometric C, [K]=jh, tau+ + tau-=0,
tau±=±2j. Thus [tr(K²)]=2j tr M=0. The physical Gauss identity
[G_nn]=0 implies [Ric_nn]=tr_h[Ric_ab]. Since tangential
S(C)_ab=D_(a C_b)+K_ab C_perp, this equals
4j C_perp + tr_h[Ered_ab].
Taking the jump of BR104 gives the exact curved wall wave
 Box_h p + <D(psi+ + psi-),D p>_h
   = -[n tau]-4j C_perp-tr_h[Ered_ab], p=[psi].
This is valid for distinct reflected metrics and normal scale,
with a common wall h and fixed material foliation. The drift
is a genuine tangential first-order term; it does not vanish
by Israel. If reduced equations hold Ered=0; retain C until
BR98 has been proved on the same development. At normalized
flat principal linearization tau=-U, recovering BR102 including
the correct sign. A different normal-coordinate foliation gives
a different psi: this is a coordinate scale channel, not a new
physical radion or a gauge-invariant curvature degree.

### BR106: bulk mean-curvature subsidiary, no third metric jet on shell

For n^flat=e^psi dy, div n=tau, let B=Box_g psi-|dpsi|_g²
(signed contraction), V=∇_(grad psi) n. The product rule and
covector commutator give
 Box_g n^flat-Ric(n)^flat
   = B n^flat+2 V^flat-dQ+Q dpsi.
The divergence of Box_g n^flat-Ric(n)^flat equals Box_g tau
by the Hodge Laplacian/divergence commutation. Therefore
 Box_g tau=div_g(B n+2V-Q_gradient+Q grad psi),
 V=K^sharp(D psi)-n(psi) D psi (view tangent vector in g).
Expanded:
 Box_g tau=n B+tau B+2 div_g V-Box_g Q+
             <dQ,dpsi>+Q Box_g psi.
Independent exact differential check with curved Lorentz
h=e^(2f) eta4, lambda=e^psi, nonconstant f,psi in t,x,y and
two spectators passes. This test is not the general proof;
the general proof is the tensor product and Hodge identity above.

For a GIVEN regular reduced solution Ered=0, substitute BR104
into B. It becomes a first-jet expression if H(x,g) algebraic
and the material defining function fixed. Then n B and div V
use at most second metric jets. Reduce the apparent third jets
in Box Q by writing Q=C(n)+H_perp:
 Box Q=(Box C)(n)+2 contraction(∇C,∇n)+C(Box n)+Box H_perp.
BR92 gives Box C=-Ric(C) on the same reduced metric; Box n
uses the preceding product formula and at most second jets;
Box H_perp uses at most second metric jets for algebraic H.
Thus on shell the tau source can be expressed with at most
SECOND metric jets, not third; with nonzero residual retain
div TREred and n Ered_nn. For solution-dependent chart changes
or derivative-dependent H this order statement requires new
proof. This is a nonlinear identity for an actual regular
reduced solution, not an independent existence theorem for tau.
For homogeneous F tau±=±2j Dirichlet on the original wall.
Use a smooth prescribed collar lift of these two constants;
w=tau-lift has zero wall trace, source includes Box(lift).

### BR107: hidden normal trace and explicit reconstruction debt

For a GIVEN regular curved scalar Dirichlet wave Box w=F,
with spacelike slices and timelike boundary, choose a smooth
bounded multiplier X equal to outward unit normal at wall,
with controlled deformation and exterior flux. Stress tensor
T=dw⊗dw-g|dw|²/2 (mass can be added). Dirichlet trace gives
all tangential derivatives zero, dw=(n_out w)n_out^flat,
T(n_out,X)=|n_out w|²/2. Divergence
 div(T(.,X))=F X(w)+T:Lie_X g/2
and spacetime integration imply
 ||n_out w||²_L2(wall slab)
 <= C(E_w(t)+E_w(0)+ integral(E_w+||F||²)).
The constant depends on actual multiplier and positive slice
energy comparisons, coefficients and exterior control; weighted
noncompact application requires integration and cutoff payment.
Combined with ordinary Dirichlet energy, this provides a
conditional L2 normal-trace estimate without an additional
normal differentiation of w. On F wall use both sides; [n tau]
then sources BR105 wall wave. The wall wave with drift has
ordinary intrinsic positive energy on regular wall foliation;
source L2 bound controls p in H1 x L2. Tangential commuted
versions require actual coefficient commutators, boundary
compatibility, and normal recovery. No uniform high-order
tame estimate claimed from this low-order multiplier.

Reconstruction obstruction: at flat principal level a normal
coordinate generator V_n=chi(y)p with chi(0)=0, chi'(0)=1 on
one face creates exactly the scale jump p and tangential shift
normal jump d_wall p via Lie_V g. It preserves common H,b
values. Since Box commutes with flat derivative,
 Box(Lie_V g)=2 symgrad(Box V), Box V_n=chi Box_h p+chi'' p.
Direct lift therefore differentiates the wall-wave forcing
[n tau] once; merely inserting BR107 L2 trace into this lift
does not pay the differentiated bulk source. Need a wave-adapted
lift/good unknown or an actual augmented mixed-order energy
with compatible regularity; cannot claim full metric evolution
from a scalar wall energy. At curved level retain Lie and
source transport, metric/normal commutators and the true
induced geometry. The fixed-source H restriction is essential.

Acceptance: byte-identical local SymPy 1.14.0 four separate
90-second-bounded stages all exit zero. One initial wall
assertion needed expansion rather than structural equality.
Source SHA and stdout in Artifacts/hopf369/br104_107_local_sympy_receipt_20261128.txt.
Native algebraic source constructors written, Agda kernel unrun;
no CI requested. BR105 and BR106 are analytic identities, BR107
conditional low-order energy. Next P0: wave-adapted normal
coordinate lift/augmented energy that avoids the derivative of
wall forcing, with actual variable coefficients and same-chart
corners. Full W2/3/6 remain open; BR98 follows only on actual F
reduced development. No physical Weyl or weighted exterior
acceptance inferred.


## 12. BR108–111 — wave-adapted F lift, joint glancing bound and moving-chart weld

Reconciled BR4 fixed-material conformal source and BR6/19 free graph
normal force, BQ conformal gauge/source-jump and derivative-source
resonance negative control, BR102 and BR104–107 curved scale and
Dirichlet trace, BR35/37 finite warped Green and Lorentz machinery.
Do not replace the source with a derivative-dependent harmonic gauge:
BQ already has a resonant loss control. No second spatial constraint
solve. Classical Green kernels, wave energy and diffeomorphism
naturality are prior mathematics; DASHI-specific result is the
joint original F normal-scale/Dirichlet-trace/metric-lift composition.

### BR108 — homogeneous wave lift, rather than prescribed collar profile

For the normalized flat principal half-line pair use y>0 and y<0,
same oriented derivative ∂y and z=(s,i xi), s=gamma+i omega,
gamma>0, ell²=s²+|xi|², Re ell=a>0. Prescribe scale jump p=[l]
(l=p_nn/2). Choose scalar generator V=v ∂y with
 v+=A exp(-ell y), v-=A exp(ell y), A=-p/(2ell).
Then [v]=0, [∂y v]=p, [∂y² v]=0, and Box v=0 on each side.
For L=Lie_V eta, H_L=0, b_L=z v, l_L=∂y v.
Thus [H_L]=[b_L]=0, [∂y H_L]=0, [∂y b_L]=z p,
[l_L]=p, [∂y l_L]=0. Each L channel solves the homogeneous
bulk wave. Subtract L from a flat principal F metric solution:
the residual has full value and normal derivative transmission
and unchanged bulk forcing. The mean-force row does NOT vanish
on L separately, since tau_L=-Box_wall v; it was used upstream
in the U/scale equation. Reconstruction is a source decomposition,
not a replacement F solution. For arbitrary forcing with nonzero
additional original row jumps those must still be lifted separately.
In physical variables this generator has nonzero common wall value;
it is NOT a diffeomorphism fixing the material wall pointwise.
For homogeneous decaying half-line generators imposing v+=v-=0
at wall forces A=0 on both sides and cannot produce p!=0.
Do not hide this obstruction behind BR107 collar extension.

### BR109 — estimate the three operators jointly

Given zero initial/lifted data in the Laplace transformed flat
half-line scalar Dirichlet problem (∂r²-ell²)w=F on r>=0,
the normal derivative at zero is -integral exp(-ell r)F dr,
up to the chosen orientation. Its norm is exactly
(2a)^(-1/2). For the jump on both faces, in the direct-sum
L² norm, the functional norm is a^(-1/2). In the homogeneous
principal BR105 wall equation p has magnitude |jump n w|/L²,
L=|ell|. Additional gauge/inhomogeneous wall terms are not
included in this particular bulk-to-bulk estimate.
The wave lift v has two-face L² norm |p|/(2L sqrt(a)).
Consequently for m=max(|s|,|xi|), D=max(m,L),
the product mapping F to any second derivative of v
(one derivative of metric L, apart from fixed tensor/norm constants)
is bounded by D²/(2 L³ a).

Exact root bounds: write ell=a+i b.
 (a²-gamma²)(a²+omega²)=a² |xi|², so a>=gamma.
 a² L²-gamma² |s|²=a⁴-gamma⁴ >=0.
 a² L²-gamma² |xi|²=a²(a²-gamma²)+gamma²(b²+gamma²)>=0.
Hence a L>=gamma m, L²>=gamma m, L²<=2m².
It follows that D²/(2 L³ a)<=gamma^-2.
This is uniform in tangential frequency on the entire damped
half-line flat domain, including glancing, not just a ray.
By Plancherel this gives a weighted L² spacetime bound for
one metric derivative of the homogeneous lift from a bulk
Dirichlet-wave L² source. For an H^k tangential weight the same
multiplier bound holds if the input has the same weight.
It does not control one EXTRA metric derivative from that same
source; nor replace the variable curved BR106 source by a free
given L² source. The latter has second metric derivatives.

### BR110 — sharp loss of separated estimates

On s=gamma+i r, |xi|=r, L²=sqrt(gamma^4+4 gamma² r²),
a²=(L²+gamma²)/2. The squared operator norm from
|s|p to ∂t²v is |s|²/(4L² a), asymptotic to
sqrt(r)/(8 gamma^(3/2)). The isolated wall H¹-to-metric
H¹ lift thus loses a quarter tangential derivative in norm.
The exact squared joint norm for ∂t²v from the two-face
Dirichlet source is |s|^4/(4L^6 a²), asymptotic to
1/(32 gamma^4). This is bounded as r grows: the correlation
of the Green trace with the wall inverse and lift is essential.
An extra tangential derivative multiplies the latter norm
by |s| and diverges. Therefore the BR106 second metric jet
source cannot be fed into an H¹ estimate as though it were
controlled by H¹ energy alone. Need a curved commutator
factorization, higher-order coupled estimate or alternative
formulation; do not claim derivative-loss-free nonlinear closure.

### BR111 — exact curved Lie-source intertwining and chart boundary

Use actual reduced equation Ered(g)=Ric(g)+4g-S_g(C(g)),
where C is the covector gauge relative to a fixed reference
connection and algebraic prescribed H (possibly dependent on x,g).
Let k=Lie_V g and define P_g V=D C_g[k]-Lie_V C(g).
Naturality of Ric, g and symgrad when both metric AND covector
are varied gives exactly
 D Ered_g[Lie_V g]=Lie_V Ered(g)-S_g(P_g V).
This is on the actual reduced metric, even if C!=0. The
linearized contracted connection applied to Lie_V g has
principal Box_g V; all reference-connection, prescribed
algebraic source and Lie_C corrections are at most first
order in V for given smooth g. Thus P_g is normally
hyperbolic on generators (with actual lower coefficients).
If P_g V=0 and Ered=0, the Lie metric lift solves the
homogeneous linearized reduced equation, with no derivative
of the wall forcing in its bulk equation. The exact identity
is analytic by naturality, not a general curved symbolic
certificate: local oracle independently constructs metric
first jets from nonorthogonal constant Lorentz g and
arbitrary second jets of V, obtains dGamma and nonzero
reference/source lower terms, and verifies the principal
BoxV splitting. It does not assert a solution of P_g V=0.

Moving boundary: with common trace V (physical frames),
its normal component v moves the wall. Tangential Lie metric
jump includes 2[K]v=2jh v. The graph displacement -v
cancels it in the material induced-metric variation, as in
BR6/19. It cannot be ignored if using the fixed material F
system. To consume the curved lift, derive the remaining
mixed/normal value and Israel/gauge derivative rows of the
combined (Lie_V g, graph=-v) lift in the actual two-chart
frames, and reverse-solve compatible vector transmission data.
A fixed material coordinate change vanishing on the wall
does not have the BR108 homogeneous lift degrees of freedom.
Retain harmonic-source transport (do not transform a fixed
H as a tensor under arbitrary diffeomorphism). No assumption
that actual BN nonzero data become reflection invariant.
Check full graph source, corners and invertible chart map.

**Acceptance:** local SymPy 1.14.0 four bounded stages all exit 0,
byte-identical Git blob 77518b343a2bc23332a16087968aa0a84212d19e;
receipt committed. Native algebraic source constructors added,
kernel unrun; no CI requested. Next P0: actual variable
P_g vector transmission and material graph row lift, Green
composition for finite warped collar then variable geometry
(not separate trace/lift estimates), BR106 top-order factor
or coupled energy with adequate derivative regularity,
W0 same-chart high corners, W6 actual reduced existence.
W4a remains conditional BR98; W4b/W5 separate. Do not promote
a flat half-line estimate into an actual nonzero curved IBVP.


## 13. BR112–115 — physical generator transmission, finite AK joint bound, first-jet scale route

Reopened BR26, BR32, BR4/6/19, BQ conformal and derivative-source
controls, BR14/34/35/37, BR104–111. Distinguish the subsidiary
gauge wave (covector) from the gauge-preserving generator P_g
(vector). Classical diffeomorphism, scalar wave, Green spectral
bounds and stress energy prior mathematics; DASHI-specific
attachment to the original signed F source. No replacement of
the nonzero Hopf data by the symmetric AK reference.

### BR112 — generator equation and moving material graph

For C_mu=g_mu,nu g^ab(Gamma^nu_ab-hatGamma^nu_ab)-H_mu,
with fixed reference connection and prescribed H(x,g), covariance
when the background structures are also transported gives
 P_g V=DC_g[Lie_V g]-Lie_V C
      =g_mu,nu g^ab (Lie_V hatGamma)^nu_ab
       +Lie_V H_mu-D_g H_mu[Lie_V g].
Here Lie_V of a connection is the connection Lie derivative
(including ∂ab V^nu); in the BR14 coordinate contracted source
hatGamma=0 in the chosen chart and H fixed in the metric,
 P_g V=g_mu,nu g^ab ∂ab V^nu+Lie_V H_mu.
For a GIVEN smooth g and algebraic H, lower terms are first order;
do not assume hatGamma is a tensor or transport H without the
inhomogeneous source rule. This identity follows from covariance
of the connection difference with both backgrounds varied.

Use matched Gaussian trace collars for the geometric boundary
calculation only, g=dn²+h(n,x), K±=1/2 h_n±, with common h,
[K]=jh and mean trace zero. Write V=w+v n, common value at seam,
[w_n]=0, [v_n]=p. Lie metric perturbations at fixed graph are
 k_ab=Lie_w h+2v K_ab, k_an=h_ab w_n^b+d_a v,
 k_nn=2v_n.
Material graph displacement f=-v removes normal evaluation
from k_ab, so common induced metric variation is Lie_w h,
mixed jump zero, material normal scale jump p. Exact transported
embedding is the inverse diffeomorphism on the original wall:
pullback metric plus pullback embedding yields natural pullback
of its first and second fundamental forms and normal gauge
projection. With tangential wall parameter w, δh=Lie_w h,
δK±=Lie_w K±; thus δ([K]-jh)=0 and δmean tau=0 on the actual
physical shell, constant j. For P_g V=0, δC=Lie_V C, so
the combined graph/metric variation also preserves all geometric
gauge value jumps. If P differs across the wall, its projected
jump is an explicit gauge defect. The coordinate normal derivative
jump [w_n]=0 is NOT [∇_n w]=0: the latter equals j w on this
collar. Covariant conormal transport must include that term.
These are exact geometric first variations; the combined graph
lift is not a fixed-wall diffeomorphism, nor a finite-amplitude
piecewise chart existence theorem.

For prescribed p on a given continuous metric in a matched
material chart, solve P_g V=0 with common V and prescribed
coordinate conormal jump p n (with appropriate density).
With uniform slice energy, common positive component wall Gram,
bounded piecewise coefficients and homogeneous exterior flux,
the signed generator flux is -<V_t,W p>, W includes density,
normal direction and Gram. Add <V,W p> to energy, leaving
<V,∂t(W p)>. Normal H1 trace interpolation and Young control
the cross term by small bulk energy plus C||p||²_wall, and
the remaining power by E_V+C(||p||²+||p_t||²)_wall (bounded
W,W_t). Hence a conditional low-order generator energy
estimate for p∈H1_t L²_wall and compatible initial data.
For existence still construct the weak/strong solution in the
actual chart and pay exterior and boundary coefficient regularity.
This gives V H1, NOT V H2 required for metric H1.

### BR113 — actual harmonic-Y scalar reference generator

On BR14 AK reference g=b² h_base+b^8 dY², H_Y=0, H_a equals
base contracted lower Christoffel independent of Y. A pure
normal coordinate generator V=v ∂Y has Lie_V H=0 (H has no
Y component or dependence). At the frozen base RNC point
P_g^Y V=0 reduces exactly to the scalar normal ODE
 b^-6 ∂YY v-ell² v=0 after multiplying by b².
With dx/dY=b³, k=b_x/b, this is
 v_xx+3k v_x-ell² v=0.
The same scalar ODE governs the mean-curvature Dirichlet
wave at the frozen base RNC point (forcing b²F_tau).
This is NOT the BR34 covector gauge operator.
Conjugate v=b^-3/2 u:
 u_xx-(ell²+U)u=0, U=(3/2)k_x+(9/4)k².
Actual optical b=(4/5) sec((4/5)x), k=(4/5)tan((4/5)x),
k_x=b², 4/5<=b<=1, |k|<=3/5. Thus 0<U<=231/100<3.
Same conjugation of scalar forced equation gives source
b^(7/2) F_tau with L² norm <=||F_tau||. At endpoints b=1,
[v_x]=[u_x]-(3/2)j A for common value A, j=-6/5.
H_perp and mean scalar are evaluated on the reference, not
promoted to the nonzero BN collar.

### BR114 — finite scalar AK joint Green estimate

Let d=2 atan(3/4)/(4/5)>1, a=Re ell>=gamma, L=|ell|.
For gamma>=16, e^-ad<=1/7 since ad>=2 and e²>7.
Dirichlet homogeneous kernels
 K0=sinh(ell(d-x))/sinh(ell d), Kd=sinh(ell x)/sinh(ell d).
Both endpoint values A use extension A(K0+Kd).
Flat trace jump for Dirichlet source f is
 -integral(K0+Kd) f, bilinear (not Hermitian), whose functional
norm equals ||K0+Kd||. Bounds |K0|<=(7/6)e^-ax and
|Kd|<=(7/6)e^-a(d-x), so norm<=2/sqrt(a).
The flat endpoint derivative jump for common A is
 D0 A=-2ell tanh(ell d/2) A, with
 (3/2)L<=|D0|<=(8/3)L.

Dirichlet inverse norm <=1/(aL) in L² by sine spectral basis:
 |ell²+kappa²|²=(a²-b_im²+kappa²)²+4a² b_im².
If b_im²<=a² minimum on kappa²>=0 at 0, L^4>=a²L²;
otherwise minimum >=4a²b_im²>=a²L².
For U with c=3 bound, delta=c/(aL)<=3/gamma²<1/64.
Neumann series gives scalar Dirichlet trace bound
 <=2/(sqrt(a)(1-delta))||f||<=3||f||/sqrt(a)
and equal-endpoint homogeneous u norm <=3|A|/sqrt(a).
Derivative jump correction <=6c|A|/a by flat Green trace;
include optical conjugation shift (3/2)j A. At gamma>=16
 6c/a+(3/2)|j|<L/2, so physical derivative jump scalar
D has |D|>=L and A=p/D uniquely. For integration by parts
|D_u|<=3L; ||u'||² <=(L²+c)||u||²+3L|A|²
<=16 L²|A|²/a, and ||u''||<=4 L²|A|/sqrt(a).
b^-3/2 and its first two derivatives bounded by 2,2,5;
hence v norm<=6|A|/sqrt(a), v'<=9L|A|/sqrt(a),
v''<=10L²|A|/sqrt(a).

For the principal scalar wall inverse p=(signed n tau jump)/ell²,
use BR105 linearized drift-free reference. Other terms (including
gauge, background variation of n tau, residuals and material
graph transport) are separate sources, not included in this
particular operator. With Dfreq=max(L,|s|,|xi|), BR109 root
inequalities yield
 ||any optical/tangent second derivative of v||_L²
 <=30 Dfreq²/(L³ a) ||F_tau|| <=60/gamma² ||F_tau||.
All constants conservative and rational except exact optical
coordinate bounds; no numerical frequency sampling assumption.
Metric Lie reconstruction incurs fixed smooth background
coefficients, and its boundary/material graph attachment must
consume the full BR112 geometry. This is the actual AK frozen
scalar-generator collar estimate, not a variable curved
matrix Green theorem or full warped F boundary inverse.
The full generator on actual nonzero g requires variable
coefficient P_g, graph chart transport and source estimates.

### BR115 — alternative first-jet scale equation and sharp refusal

BR100+104 give a direct alternative to BR106:
 Box_g psi=tau n psi-tr(K²)+nH_perp-<Dpsi,C_tan>+4-Ered_nn,
 n psi±=±2j+C_perp+H_perp± on F.
This is a bulk wave with Neumann data and first metric jets
if H algebraic, fixed chart, actual reduced solution. The
normal derivative jump is 4j+[H_perp], independent of common C.
Do not assert C vanishes before BR98. On reference RNC
H_perp=0, C=0; linearize n psi±=±2j: since npsi0=4k
and Dpsi0=0, linearized Robin is n(δpsi)-4k δpsi=0,
not raw homogeneous coordinate Neumann.

The scale-Neumann route removes the explicit second-jet
tau source but is not automatically a better metric estimate.
Flat principal arbitrary bulk scale source F_l on two half-lines,
homogeneous Neumann, trace difference norm exactly
1/(L sqrt(a)) by Green functional exp(-ell r)/ell.
BR108 lift then gives ∂t²v operator norm
 |s|²/(2L² a).
On glancing s=gamma+i r, |xi|=r, its square /r tends to
1/(16 gamma³). Thus it loses half a tangential derivative
in norm for arbitrary bulk forcing. BR114 tau route has
uniform joint bound but second-jet source. Neither arbitrary
source route closes the nonlinear feedback at the same
metric energy order. Need structured source factorization
or an augmented energy / moving-wall formulation with
derivative-compatible trace, not just add a large damping
constant. This refusal is about these exact model operators,
not an impossibility theorem for Einstein–Israel development.

Acceptance: actual local SymPy 1.14.0 four bounded checks,
all exit 0. Git blob matches executed source after correcting
one blank-line difference and rerunning. Receipt records hashes.
Native algebraic additions, kernel unrun; no CI requested.
Next max-cut: compute actual structured BR104/106 first/second
jet source symbol on the nonzero geometry, including generator
transport of the foliation and gauge-source terms, seek a
cancellation or uniform mixed-order energy without derivative
loss; actual moving chart and W0 higher corners remain.
W4a conditional BR98, W4b Weyl, W5 exterior/Hodge, W6 physical
development and W7 acceptance remain separate.


## 14. BR116–119 — structured scale factorization, actual shear and transported foliation

Reopened BR14/34/35 AK harmonic-Y reference, BR100/104/105 material
foliation, BR112–115 generator/Green and Neumann routes, actual AN
metric and BE/BO/BQ source-preserving correction. No new spatial
solve. Classical curvature variation, Robin spectral form and
diffeomorphism naturality retain prior attribution. DASHI-specific
contribution is the exact signed source factorization and obstruction.

### BR116 — scalar decoupling at the original AK reference

Use the original BR14 fixed lower harmonic source H, tangential base
RNC at the point, H_Y=0 and H_a independent of Y. Proper normal
k=b_n/b, k_n+k²=1, K=k h, tau=n psi=4k. Metric variation m is
normalized as in BR14; l=delta psi=m_YY/(2b^8), c=delta C_perp,
e=delta Ered_nn. Keep all fifteen metric components, nonzero c,e.
The algebraic variation is
 delta tr(K²)=2k delta tau,
 delta(n psi)=n l-4k l,
 delta tau=n l-4k l-c
at the base RNC point. Variation of H_perp and its normal derivative
vanish there (H_a=0 along the normal line). The direct scalar
wave variation includes the inverse normal metric and contracted
connection:
 delta(Box_g psi)=Box_g l-8(k_n+4k²)l-4k c.
Variation of the BR104 right side is
 6k n l-24k² l-2k c-e.
Consequently the exact original frozen reference scalar equation is
 (Box_g-6k n-8)l=2k c-e.
This is not just a principal symbol: all reference normal drift
and zeroth terms are included. Independent full 5D Christoffel,
inverse metric derivative, linearized Ric_YY, and contracted
gauge calculation using independent 15-component metric jets
checks the equation at (b,k)=(1,-3/5),(4/5,0),(5/6,7/25),
(1,3/5), with nonzero c and e. General identity derived above;
finite rational points are oracle checks, not exhaustive proof.
The F mean and jump of K imply delta tau±=0 on the reference,
so n l-4k l=c on both sides. Do not set c=0 as an existence
hypothesis for arbitrary reduced forcing. Conditional BR98
uniqueness on a given smooth homogeneous reduced linearized
solution with zero initial gauge does allow c=0 for that solution.

In optical x, let k_o=b_x/b=b k. Then l=b^(3/2) u gives
 u_xx-(ell²+U_s)u=b^(1/2)(2k c-e),
 U_s=8 b²-(3/2)k_o,x+(9/4)k_o²
    =(13/2)b²+(9/4)k_o².
At b=1 endpoints, outward Robin derivative minus (3/2)u
equals the signed c trace, since k_o=±3/5.
No use of variable tangential chart covariance or nonzero
Hopf equality in this frozen BR14 scalar reduction.

### BR117 — exact shear term and actual nonzero AN obstruction

For A=h^-1 K and S=A-(tau/4)I, set Q=n psi-tau. The exact
first variation of the shape-dependent source is
 delta(tau n psi-tr A²)
 = (n psi+tau/2) delta(n psi)
   -(n psi-tau/2) delta Q-2 tr(S delta A).
This identifies the precise additional shape derivative on
non-umbilic data; other BR104 gauge, source and operator variations
must also be retained. AK S=0 is the special decoupling case.

Use actual AN seed at x=(1/5,0,0), eps=1/40, at paired seam
b=1. Its spatial induced metric H=gamma+a a^T, shift beta=H^-1 a,
lambda²=1-a^T H^-1 a. Opposite b_y terms cancel in the mean
spatial K, so -2lambda M_sp=Lie_beta H. Direct exact rational
differentiation of the original AN rational pullback gives
 (Lie_beta H)_01 H_00-(Lie_beta H)_00 H_01
 = -5721931274414062500/2095616609275832161 != 0.
Here H_01=0, and (Lie_beta H)_01!=0. Thus the spatial mean
shape has a genuine nonzero trace-free part. Under conformal
u²g, M_sp^TF -> u M_sp^TF (normal derivative of u only adds
pure trace); BE/BO/BQ tangent-block lifts vanish to first order
at the seam. Therefore the same obstruction survives in the
conditional nonzero spatial source, independent of the unknown
positive scalar representative. At the time-symmetric corner
choose spatial v±=e0±e1 and equal time components making them
null in the induced Lorentz metric. Their squared spatial lengths
coincide and their shear contractions differ by 4 M_sp,01.
With zero mixed time-space mean shape at the time-symmetric
zero-shift corner, at least one contraction on the null cone is
nonzero. This is a specific actual source witness, not a
general no-go for coordinate choices or Einstein evolution.

For a pure normal Lie metric variation on a fixed Gaussian
foliation, the leading tangential second-generator term in
delta A is -h^-1 D²v (other terms lower), so the shape coupling
contains 2 S^{ab} D_aD_b v. It cannot in general be replaced by
a multiple of Box_h v: null-cone shear survives. The arbitrary
source glancing bound from BR115 cannot be made harmless merely
by the AK cancellation or a small fixed nonzero amplitude.
No assertion that the entire coupled source has no other
possible compensating terms: that is the remaining proof cut.

### BR118 — distinguish moving graph from transported foliation

For independent metric variation m and defining-function
variation sigma=delta phi, lambda=(g^-1(dphi,dphi))^-1/2,
n=lambda grad phi, psi=log lambda, exact first variations are
 delta psi=(1/2)m_nn-lambda n(sigma),
 delta n=-(1/2)m_nn n-(m^sharp n)_tan+lambda D sigma.
With g fixed, the foliation contribution to delta tau is
 lambda (Box_h sigma+2<D psi,D sigma>).
Using normalized Hess phi and moving tangent frame, the fixed
metric foliation contribution to delta K is
 lambda(D_aD_b sigma+D_a psi D_b sigma+D_b psi D_a sigma)
in the tangential frame identified by normal projection.
The normal-Hess and normalization terms cancel; this also
checks the trace identity. The independent local test includes
a sheared Lorentz metric, arbitrary defining-function and metric
jets, moving frame Hessian calculation and curved divergence.

Full Lie transport of BOTH g and phi gives delta psi=V(psi)
and delta tau=V(tau), and the tensor shape transport is natural.
The top-order shear term of the fixed-foliation Lie lift is
canceled by the transported defining function. But at Gaussian
reference phi=y, m=Lie_V g, delta phi=V(phi)=v gives
delta psi=v_n-v_n=0. It therefore also removes the very
scale jump p the graph-only lift was constructed to carry.
Graph-only extension sigma with common wall value v and zero
normal derivative instead preserves [v_n]=p. Do not conflate
these two transformations. BR111/112 moving wall geometry
controls the embedding, not automatically all normal derivatives
of its foliation extension. A transported-foliation formulation
must supply an independent scalar chart equation and transmission,
recover the fixed-material variables with source transport,
and prove invertibility/regularity. This is a precise remaining
coordinate choice, not a free cancellation in the current F IBVP.

### BR119 — explicit finite AK scalar Robin inverse and joint bound

U_s lies in [104/25,731/100], optical length d>1. For the
self-adjoint scalar operator A_s=-d²/dx²+U_s with outward
Robin derivative (3/2)u at both ends, form
 ||u'||²+int U_s |u|²-(3/2)(|u(0)|²+|u(d)|²).
Use endpoint trace <=(2/d)||u||²+4||u||||u'|| and Young
4c ab <= b²/2+8c² a², c=3/2. This gives
 form >= ||u'||²/2-17||u||².
For real tangential spatial frequency, gamma>=16, spectral
parameter s=gamma+i omega, the distance estimate
 |s²+|xi|²+lambda_s|>=gamma²-17 for lambda_s>=-17
follows by separating omega²<=gamma²-17 from the complementary
case. Thus scalar L² inverse <=1/(gamma²-17)<=1/239.
This suffices for homogeneous frozen scale uniqueness when
c=e=0, with homogeneous Robin rows and zero initial data.

For arbitrary bulk f=b^(1/2)(2k c-e) and separate Robin forcing
g_R (two endpoint values), retain BR114 a=Re ell, L=|ell|,
Dfreq=max(L,|s|,|xi|), m=max(|s|,|xi|).
U_s bounded by 8, Dirichlet inverse <=1/(aL), perturbation
<=8/gamma²<=1/32, endpoint extension and forced normal trace
norms <=3/sqrt(a). Since exp(-ad)<1/100, flat outward DtN
differs from ell I in operator norm by <=2L/99. Perturbation
cost <=6*8/a, subtract Robin (3/2)I; total relative difference
<1/2 at gamma>=16. Inverse endpoint map <=2/L. Therefore
 |p| <=3||g_R||/L+9||f||/(L sqrt(a)).
Compose BR114 scalar generator, retaining graph and smooth
reference Lie metric factors separately:
 ||D²v|| <=30 Dfreq²/(L² sqrt(a))||g_R||
            +90 Dfreq²/(L² a)||f||.
Since aL²>=gamma² m and Dfreq²<=2m², the bulk term is
<=180 m||f||/gamma². This controls a bulk H1 tangential
source (in particular independent gauge of that regularity),
NOT arbitrary Robin forcing at the same order, nor arbitrary
first-jet shear forcing from the metric. For c=e=0 and homogeneous
data the reference scalar sector is homogeneous and l=0 by
the scalar inverse; then p=0 and the generator correction
is absent. This is a frozen reference scalar result, not
full metric/glancing/variable reduced existence.

Acceptance: actual local SymPy 1.14.0, four bounded stages
all exit zero; exact executed blob 84f9a7afa580a04956e91745641d458fd95539e0.
Native source expressions and manuscript qualification updated;
kernel and integrated PDE acceptance unrun, no CI. Next
max-cut: exploit Codazzi/Israel constraints on the genuine
shear derivative or build an independent transported defining
function with correct gauge-source/embedding and normal-jet
transmission. Keep BR4 cusp formulation as an alternative
(not same allocation) and pay mean force explicitly. W0
same-chart high corners, W2/3 nonzero variable estimate,
W4a BR98 conditional, W4b/W5/W6/W7 remain as before.


## 15. BR120–123 — arbitrary source jump, moving-chart BIDI, commutator and constrained shear

Reconciled already-committed BR116–119 (HEAD 8b1f8f8c27446bd9a7b0fc4a5c742599afe22e86), BR18/19 moving-chart jet, BR22 separated-energy obstruction, BR100 F normal inverse, BR112/118 moving vs transported foliation, BR117 actual AN shear. At inspection master comparison 408 ahead / 42 behind. Targeted master search and PR discovery reopened #1504/#1508/#1512/#1520/#1527 as relevant F8 moving-boundary/energy donors; their existence is not same-source attachment or a full audit of the 42 master commits. No merge/rebase or master edits. Classical Christoffel, Gauss–Codazzi, Lie and scalar commutator identities are prior mathematics; DASHI-specific work is source-preserving F/moving chart and signed AN application.

### BR120 — full nonlinear 15-row derivative jump inverse (continuous metric chart)

At a matched full metric g, timelike graph with defining covector F (F_y=1), lambda=(g^-1(F,F))^-1/2, n_flat=lambda F, E the four tangent columns, h=E^T g E. Differentiated continuity gives [∂_mu g]=F_mu J, J=[∂_y g]. The direct maps are
 B=[K]=E^T J E/(2lambda),
 a=[Gamma_lower]=J g^-1 F - F tr_g J/2.
Let T be the ambient tangential extension of B (T=g E h^-1 B h^-1 E^T g). Then for arbitrary symmetric B and covector a the exact unique inverse is
 J=lambda(2T+2 tr_h(B) n_flat⊗n_flat+n_flat⊗a+a⊗n_flat).
Proof by tangent-normal decomposition: tangent block 2B, mixed block a_tan, normal block 2 tr_h B+2a_n in proper-normal derivatives. Direct readback pays all 10 Israel and 5 contracted rows. Rank 15 at any admissible continuous chart, no tangential characteristic inverse. Independent 15x15 exact Jacobian at nonorthogonal Lorentz point with shift, tilted graph, lambda=5/4 passes.

For pure tension B=j h and geometric gauge continuity, a=[H_cov] in the common chart:
 J=lambda(2j g+6j n_flat⊗n_flat+n_flat⊗a+a⊗n_flat).
It contains BR1 continuous source (a=0, normal coefficient 8j), BR4 conformal cusp (a=-3j n_flat, normal coefficient 2j), Gaussian trace (a=-4j n_flat, normal coefficient zero) as actual distinct source choices. Do not identify them or assume a=0 after a chart change.
Variation for independent material metric m, graph covector delta F, source delta a and delta j:
 delta lambda=-lambda³(2 delta F^T g^-1 F-F^T g^-1 m g^-1 F)/2,
 delta n_flat=delta lambda F+lambda delta F,
 delta J=delta lambda (J/lambda)+lambda[2 delta j g+2j m+6 delta j nn
             +6j sym2(delta n,n)+sym2(delta n,a)+sym2(n,delta a)].
Here sym2(u,v)=u⊗v+v⊗u. For graph motion delta F_a=-d_a f; material derivative jump is [delta g_y]+f[g_yy]. For fixed constant tension delta j=0; arbitrary j variation only tests source map, not vacuum pure-tension admissibility. delta a is actual material source variation (including evaluation/metric/source transport); it is not silently zero. Independent Sherman–Morrison rank-one metric path and nonzero tilt/source variations check exact derivative. The inverse concerns a common full g, not arbitrary unequal-lambda F background.

### BR121 — conditional linearized F to moving-continuous chart BIDI

At continuous reference g in straight material coordinates F=dy (arbitrary shift, positive lambda), homogeneous F value rows imply [m]=2p nn with p=[delta log lambda]. Choose a generator V with common trace, tangential derivative jumps zero, and [∂_y V]=lambda p n^sharp. Let f=V^y at wall. The exact metric Lie value jump is
 [Lie_V g]=f J+2p nn.
Then q=m-Lie_V g with graph displacement f gives
 [q]+f J=0;
 inverse m=q+Lie_V g gives F value jump 2p nn. The graph value f and normal scale derivative p are independent jet data (rank 2). The coordinate normal component f=V^y is not proper normal speed when lambda!=1. Its geometric normal component is lambda f. Tangential differentiation of moving continuity gives [q_a]+f_a J+f J_a=0. BR112 naturality transports actual induced metric, Israel and mean force (including evaluation shift and wall tangential reparametrization); geometric gauge jump transports with explicit minus [P_g V], projected on the common physical frame. If P_g V=0, the reduced operator intertwines by BR111. BR120 supplies all 15 derivative jump rows for that moving continuous-metric chart with its actual source jump and graph variation. No claim of off-shell equality of different prescribed gauges; if P_g V≠0 it remains a source. This is a BIDI on jets given V, not a constructed vector transmission inverse on general variable g, not nonlinear chart existence, not equivalence of arbitrary unequal-scale background metrics.

### BR122 — actual geometric factorization of the coordinate shear

For any smooth vector X and scalar v on a Lorentz metric,
 [Box_g,X]v=2(∇^mu X^nu) Hess_g(v)_mu,nu
             +(Box_g X+Ric^sharp(X))·dv.
Derivation is the product rule plus the scalar covector Ricci commutator. Direct coordinate coefficients of second scalar jets are
 2g^ab ∂_a X^c - X^d∂_d g^bc (contract with symmetric Hessian);
 first scalar coefficients are g^ab ∂ab X^c-G^a∂a X^c+X^a∂a G^c,
 G^c=g^ab Gamma^c_ab. Independent full 5D rational metric two-jet oracle computes all connections, Ricci and covariant Hessian and verifies equality against these coordinate coefficients with non-diagonal g, arbitrary X two-jet and scalar independent jets.
For X=n, ∇n decomposes into K and normal acceleration. The tangential Hessian contribution is 2 K^ab Hess_g(v)_ab. Its trace-free part is exactly the second-generator shear factor in BR117 for a pure normal Lie perturbation. For X=lambda n, retain the extra derivative of lambda and the acceleration terms. In Gaussian anisotropic warp h_ii=eta_ii exp(2f_i(y)), exact [Box,∂y] is 2 sum_i k_i h^ii ∂ii - tau_y ∂y, verified for two independent tangent derivatives and four independent warp functions. Thus the pure coordinate shear is part of an exact commutator, not an arbitrary forcing. In a fully transported foliation the BR118 good unknown subtracts the corresponding scale derivative; in a graph-only extension it does not. This identifies the correct cancellation on a pure Lie channel, but does not cancel shear from an arbitrary physical perturbation or prove a tame estimate for the commutator. In particular using X=v-independent and the wave equation for v does not mean [Box,X]v=0.

### BR123 — principal gauge and Codazzi alone do not eliminate shear

At an orthonormal wall point h=diag(-1,1,1,1), take null covector z=(1,1,0,0), no normal frequency, mixed metric polarization b=(0,0,1,0), H=l=0. Then full 5D principal harmonic gauge z·m- z tr(m)/2=0, delta tau=0, principal Codazzi z^sharp·delta K-d delta tau=0 with delta K=-(z⊗b+b⊗z)/2. For trace-free spatial mean M with M_12=M_21=1,
 -2 tr(h^-1 M h^-1 delta K)=2.
The mixed polarization is not of the pure normal gauge form b proportional to z. Its shear source is not asserted gauge invariant under changes of foliation. Intrinsic scalar curvature principal symbol of this H=0 vanishes, but the full curved linearized Gauss identity has lower-order mean-shape/source terms; those were NOT imposed by this example. This is not a counterexample to full constrained curved evolution.
BR117 actual AN witness has spatial H_01=0, M_sp,01!=0 at the time-symmetric zero-shift corner; choose equal time component making e0 spatial direction null and transverse e1. The same null/transverse pairing detects that nonzero shape contraction. Thus one cannot erase the BR117 shear term by just the principal Codazzi/trace/gauge identities; full Gauss/curvature or coupled estimates remain necessary. Small amplitude or damping alone is not a proof.

### Exact next weld and acceptance

Carry BR120/121 into the original moving BR18/16 with the actual material source. BR22's unrestricted separated positive energy obstruction remains; do not relabel the chart as a coercivity proof. Derive full curved linearized Gauss/Weyl source factor on the constrained physical quotient, including the lower-order terms BR123 omits. In parallel solve P_g vector transmission with the BR121 normal jump and continuous trace, paying variable graph and source regularity at H² generator order; prove invertible chart map and selected higher corners on original BN/BQ. Use the commutator for pure gauge, not for unconstrained physical perturbations. W2/3 nonzero variable coupled estimate, W4b Weyl preservation, W5 weighted exterior, W6 reduced existence, W7 native/physical acceptance remain open. W4a conditional BR98 remains unchanged.

Local SymPy 1.14.0 four stages exit zero (90s per case, no CI); exact executed Git blob bb58249213fb46e9b5d7e31ac9b6aebac413ef20. Receipt in Artifacts/hopf369/br120_123_local_sympy_receipt_20261128.txt. Native expressions written, kernel unrun. No nonlinear PDE promotion.


## 16. BR124–127 — full Gauss shear source, Weyl inverse and normal transport

Reopened actual BR90 Ricci-defect jump, BR27/29 positive 35D
Weyl carrier, BR53 zero-speed factorization, BR57 normal
electric primitive/holonomy, BR117 actual nonzero shear and
BR123 principal-only negative control. Classical Gauss,
Schouten/Weyl, characteristic linear algebra and Riccati
transport are prior mathematics; DASHI-specific attachment
is the original F signed-source inverse and use of the
actual BR29 carrier. No duplicate spatial constraint solve.

### BR124 — full curved scalar Gauss supplies the wall contraction

Write D=Ric+4g (actual Ricci defect), M=mean K, A_M=h^-1 M,
tr_h M=0 and [K]=jh. On each leaf the scalar Gauss equation
is R_h=-12+tr_h D_tan-D_nn+tau²-tr(A²), A=h^-1 K.
Taking the wall average, tau±=±2j, gives exactly
 R_h=-12+3j²-tr(A_M²)+d_G,
 d_G=mean(tr_h D_tan-D_nn).
The signed trace-reversed normal constraint, not just a
principal Codazzi symbol, is required. Its jump also gives
[D_nn]=tr_h[D_tan] since tr_h M=0.
For an arbitrary material metric variation H and mean shape
variation N, delta A_M=h^-1(N-H A_M), including the inverse
metric variation. Hence
 -2 tr(A_M delta A_M)=delta R_h-6j delta j-delta d_G.
For fixed tension delta j=0. This is the precise contraction
that BR123 omitted, not a general vanishing of shear.
The intrinsic scalar variation is
 delta R_h=-<Ric_h,H>+D^a D^b H_ab-Box_h tr_h H.
Thus trading the mean shape contraction for Gauss alone
exchanges it for two tangent metric derivatives. No gain in
regularity is inferred unless an actual curvature variable
pays that term. The identity is at the wall, not a bulk
extension of the mean condition to every leaf. BR124 checks
the exact signed shape algebra and inverse-metric variation;
it does not independently compute the intrinsic curvature
of a nonzero evolved metric.

### BR125 — full BR90 Weyl jump factors through a single effective shape

At a matched wall with constant j, full Gauss and Codazzi
give [D_na]=0 and [D_nn]=tr_h[D_tan]+6j tr_h M.
Set B=[D_tan], tf_h X=X-h tr_h X/4. The exact jump carrier
from BR90 is
 M_eff=tf_h M+tf_h B/(3j),  j!=0,
 [W_abcd]=-j (h wedge M_eff)_abcd,
 [W_nabc]=0,
 [W_nanb]=2j (M_eff)_ab.
Derivation: subtract the full 5D Schouten jump
([D]-g tr_g[D]/8)/3 from the Riemann jump given by Gauss and
Ricci contraction. The pure trace of M cancels; the B trace
also cancels. All 55 packed symmetric bivector coordinates,
including algebraic Bianchi and tracefree constraints in
the BR29 carrier, are retained. Direct local algebra checks
every tangential component and all 16 electric components;
the original jump carrier factors through the SAME nine
shape coordinates. Rank of mean map 9; combined mean and
Ricci jump map still rank 9. In particular the former
BR90 rank-nine Ricci contribution does not open an
independent second nine-dimensional Weyl channel.

For F (tr_h M=0), exact inverse with the defect retained:
 M=[W_nanb]/(2j)-tf_h B/(3j).
No tangential frequency division. On an actual vacuum
development B=0; then M is determined by the electric
Weyl jump. In a reduced development do NOT set B=0 unless
BR98 is established on that same solution. The local
masking control M=diag(0,1,-1,0), B=-3j M gives identically
zero entire Weyl jump despite nonzero mean shape. It is an
algebraic Ricci-defect witness, not a constructed metric
solution. Thus an independent projected Weyl carrier cannot
certify the gauge subsidiary or the actual geometric shape.

For material variations use the same transported orthonormal
frame on both sides; include the frame variation in delta
electric and delta B. In a fixed such frame at fixed j,
 delta M_eff=delta[W_nanb]/(2j).
The reconstructed delta M requires subtracting the
variation of tf_h B/(3j) (including h variation if using
coordinate components); the mixed shape uses delta h too.
Consequently a curvature trace estimate in positive component
norm controls the wall shear contraction without explicitly
taking two extra tangent metric derivatives. This is an
algebraic readout, not a proof of that trace estimate.

### BR126 — recover all nine shapes from active AND zero-speed Weyl traces

Independently reconstruct the exact BR27/29 packed carrier:
55 symmetric bivector coordinates, algebraic Bianchi and
Ricci trace constraints, 35D nullspace basis, positive Gram
G=X^T X and projected normal Maxwell matrix A_n.
Use the physical scaled jump J=j J_BR29 restricted to the
same tracefree wall basis (all nine independent coordinates).
P0=I-A_n(5 A_n-4 A_n³), rank 9, P0 A_n=0.
Exact ranks:
 rank J=9,
 rank A_n J=8,
 rank P0 J=6,
 rank stacked(A_n J,P0 J)=9.
The active normal map misses exactly the tracefree isotropic
direction diag(3,1,1,1); the zero-speed projection detects
it. With L=5 A_n-4 A_n³ and B_J=(J^T G J)^-1 J^T G,
 J=L A_n J+P0 J,
 m_eff=B_J(L a+z), a=A_n[W], z=P0[W].
Both directions verified as exact matrices in original
basis. At j=-6/5, maximum absolute row sums of B_J L and
B_J are 5/3 and 5/12 respectively. Thus in the specific
packed coordinate infinity norms,
 ||m_eff||_inf <= (5/3)||a||_inf+(5/12)||z||_inf.
These are coefficient norms, not a boundary trace/coercive
energy constant. Transporting the physical frame changes
coordinate norms and introduces BR40/53 connection
commutators. P0 jump trace must be obtained from actual
constraint-compatible evolution and compatible initial
data; it is not a free input to be deleted because it has
zero normal speed. BR53's source factor and BR91's nonzero
projected Cotton obstruction still apply.

### BR127 — normal extension beyond BR57's scalar warp

In a regular Gaussian normal collar with proper normal r
and h(r), K=h_r/2, A=h^-1 K, R_e=h^-1 R_{n a n b},
the full normal Riccati identity is
 A_r+A²=-R_e.
At fixed Gaussian coordinate its linearization is
 B_r+A B+B A=-E, B=delta A, E=delta R_e
(including inverse-metric variation in E). No assumption
of commuting shape and derivative. Let U_r=U A and
V_r=A V, U(0)=V(0)=I. Exact inverse
 B(r)=U(r)^-1 (B(0)-integral_0^r U E V) V(r)^-1.
For any submultiplicative norm and bounded A along a finite
normal segment, elementary linear ODE theory gives
 ||B(r)|| <= exp(2 integral_0^r ||A||)
       (||B(0)||+integral_0^r ||E||).
This follows directly by Gronwall on the B equation; use
positive component norms not signed Lorentz contractions.
Boundary B(0) may be supplied by BR125's electric jump plus
the actual defect and h variation: K±=M±j h/2 implies
A±=A_M±j I/2, so delta A±=delta A_M for fixed j.
Alternatively retain an initial/holonomy moment and invert
with its actual transport kernel; zero electric source
alone leaves a homogeneous shape solution, as in BR57.
Local tests check diagonal anisotropic Gaussian Riemann
formula, exact noncommuting variation/integrating factor,
and nonzero homogeneous scalar-kernel solution. They do
not construct normal collars or solve the actual nonzero
metric. The Gaussian transport identity does not directly
apply to the fixed harmonic material foliation: the normal
acceleration terms and coordinate/source transport from
BR104/118 must be retained and paid. Nor does a local
Gaussian collar guarantee complete normal coverage,
uniform AdS exterior estimates or absence of focal points.

### Max-cut consequences and execution

The full curved wall Gauss contraction and Weyl jump
inverse now have concrete producers; do not repeat a
principal shear cancellation search. For the remaining
nonzero curved metric W2/W3 estimate:
1. Control the actual constrained BR29 curvature trace,
   including P0 zero-speed part, using BR53 factorization
   plus actual geometric Bianchi propagation (W4b).
   Control Ricci defect using same-solution BR98 (W4a);
   off-shell source estimates retain the masking term.
2. Transport the resulting wall shape into the collar via
   BR127/57 and the actual material acceleration terms;
   retain chart and normal holonomy, with W5 exterior
   and weighted Hodge quotient still to pay.
3. Derive coupled curvature-to-metric energy with actual
   BR120/121 material BIDI and generator P_g, pay H²
   generator transmission and higher-order corners.
   The full BR106 second-jet feedback is NOT closed by
   a wall shape readout. No claim of an independent
   curvature solution equaling geometric Weyl until W4b.
4. Actual nonlinear reduced construction W6 and native/
   physical acceptance W7 remain open. Do not infer
   physical evolution from local algebra.

Local SymPy 1.14.0 four bounded stages exit zero, exact Git
blob 0eaff8e1df44fa73b828503d0cbba328ec9598b0.
Native source expressions and manuscript qualification
updated. Kernel unrun, no CI. No new master/other PR
full reconciliation in this tranche; the earlier 42
behind comparison remains the last audited base count.


## 17. BR128–131 — consume existing curvature owners; variable material energy and development

Reopened repository owners, not a new generic Weyl/Gauss/Ricci
construction. On master: DASHI/Physics/GR/RiemannTensor.agda
explicitly stages a canonical zero-table model, not a nonflat
five-dimensional theorem; DASHI/Geometry/LeviCivitaBridge.agda
contains the postulated DCHoTT emergence socket, not general
nonflat uniqueness; DASHI/Physics/Closure/ContinuumCurvatureSourceSpinTwo.agda
has the continuum authority and Bianchi receipt interfaces.
Docs/physics/KSW668F8GeometryWeylRoadmapMaxCut20261117.md
documents the same distinction. The actual F8 characteristic
donor scripts/ksw668_f8_characteristic_constraint_maxcut.py
preserves interior constraints for mode3 but leaves weak SAT
endpoints open and has a different weighted-mode commutator.
Do not import that finite TT acceptance as full Hopf curvature.

Actual original-source owners: BR27/29
scripts/check_hopf369_br_curvature_energy.py (35D Weyl, 9D
wall, positive Gram, signed flux), BR30 frozen projected
generation, BR53 zero-speed/connection factor, BR90/91 actual
Ricci-defect/Cotton source, BR31/BS11/13 exterior and holonomy,
BR57 normal primitive, BR124–127 curved Gauss and electric
readout, BR104/118 material normal and defining function.
Classical Bianchi, Cartan, Riccati, symmetric-hyperbolic energy
and matrix ODE arguments retain prior attribution. DASHI work
is the source-specific weld to these actual carriers.

### BR128 — variable material projected energy, no normal derivative in tangential commutators

Given a piecewise sufficiently regular material metric, choose
one-sided orthonormal frames with e0 future timelike and
e0,e1,e2,e3 tangent to the y-leaves, e4=n; choose the same
intrinsic frame on the two wall faces via common h. Not assuming
e0 is a common ambient geodesic, nor that dt(n)=0. This is a
local chart/frame construction with timelike time covector dt.
In these frames the actual BR29 projected Maxwell equations
have constant component matrices A_i, positive Gram G, connection
lower term L_g, and Cotton source F_g from BR91:
 e0 w = sum_{i=1..3} A_i e_i w + A_n n w + L_g w + F_g.
The connection here is the actual metric frame connection on
both bivector pairs, not the toy conjugation of BR40e. For the
geometric Weyl field the equation is obtained by selecting the
divergence and time-containing Bianchi rows and projecting into
the 35D algebraic Weyl carrier. Projection does not imply the
other unprojected Bianchi equations for an independent field.

Write n=lambda^-1(partial_y-beta^a partial_a), a=0..3. Multiply
by lambda to obtain
 C^a partial_a w - A_n partial_y w = lambda L_g w + lambda F_g,
 C^a=lambda(e0^a I-sum_i e_i^a A_i)+beta^a A_n.
Each G C^a is symmetric. The normal matrix G A_n is CONSTANT
in these coordinates, even for unequal lambda and arbitrary
one-sided beta. The raw Maxwell matrix for spatial vector v
acts between electric and magnetic slots by wedge v and its
Euclidean adjoint; norm <=|v|. Compression into the Weyl
subspace in the positive component Gram cannot enlarge that
bound. The analogous raw wall matrix acts on the time column
and spatial columns by v and its adjoint, norm <=|v|. Thus
timelike dt with positive e0(t) gives strictly positive G C^t
and H D^t on the wall, with quantitative margins
 lambda(e0(t)-sqrt(sum_{i=1..4} e_i(t)^2)) G,
 (e0(t)-sqrt(sum_{i=1..3} e_i(t)^2)) H respectively.
Need uniform lower and upper comparability on the chart.

For the wall write D^a=e0^a I-sum_i e_i^a B_i (B_i BR29),
 D^a partial_a m = L_h m-R mean(w)+f_wall.
Use common coordinate tangential measure dx^1dx^2dx^3 (or
a common smooth positive weight in both energies; include its
derivatives in lower terms). Define energy on a compact slab
 E=1/2 int_bulk w^T G C^t w + (-3j)/2 int_wall m^T H D^t m.
Here j=-6/5, -3j=18/5>0. For the active jump
 A_n([w]-j J m)=0, the signed bulk normal work is
 -mean(w)^T G A_n [w]=-3j mean(w)^T R^T H m;
 the wall exchange contributes +3j m^T H R mean(w).
Exact cancellation by BR27/29, also if only active jump is
imposed, because G A_n P0=0 and R P0=0.
No assumption of equal normal lapse or reflection symmetry.
Energy derivative consists of bounded coefficient-divergence,
connection work, bulk and wall source pairings and exterior
flux. On compact charts with uniform time coercivity and
bounded coefficients/first derivatives, homogeneous nonincoming
outer flux (or separately controlled forcing), Cauchy/Young and
Gronwall give
 E(t)<=exp(Kt)(E(0)+K int_0^t (||F_g||²+||f_wall||²)ds)
with K depending on actual chart bounds, not frequency.
This is an a priori estimate for sufficiently regular solutions
on a GIVEN metric. It does not establish their existence.
The wall shape L² is paid directly by this energy, without
first proving a separate trace estimate on each Weyl face.
Individual active or zero-speed Weyl traces are NOT bounded by
this L² energy alone.

For tangential spacetime multiindex alpha, differentiating the
scaled material equation gives no normal-principal commutator:
 [partial^alpha,P] w =
 sum_{0<nu<=alpha} binom(alpha,nu)
 (partial^nu C^a) partial_a partial^(alpha-nu)w
 minus the lower-coefficient commutators if included in P.
The analogous wall coefficient derivatives are tangential;
R,J,A_n and G,H constant in the common adapted frame. Thus
the differentiated active jump and exchange still cancel.
For integer s>=0, uniform bounded coefficient derivatives
through s+1 (or later proved tame product bounds), compatible
initial spacetime tangent jets through s, and differentiated
outer work hypotheses, summing all |alpha|<=s gives E_s'
<=K_s E_s+K_s source_s². There is no normal derivative
of the zero-speed sector in this commutator, nor derivative
loss relative to tangential curvature order on a fixed
background with those coefficient bounds. This is NOT a tame
quasilinear estimate in unknown metric regularity, a full H^s
normal estimate, nor a free exterior estimate. Partition of
unity on common tangential charts requires matched wall weights
and connection-compatible frames. Do not assume a global
orthonormal frame or global uniform time margin.

### BR129 — absorb actual Ricci defect into wall energy; conditional W4b uniqueness

In a matched F metric, D=Ric+4g, tr_h M=0, [K]=jh.
BR125 gives [w]=j J m_eff, with m_eff=m+delta, where delta
is the 9-coordinate encoding of tf_h[D_tan]/(3j).
This is an exact source shift, not an assumption of vacuum.
Mean Codazzi in our convention is
 D^a M_ab=mean D_nb,
 D_0 M_ia = D_i M_0a - mean Riem_{n a 0 i}.
With frame derivatives and the intrinsic connection separated,
the raw wall source from Ricci defect in column i=0 is
 -mean D_na; in i=1..3 it is
 -(mean D_n0 h_ai - mean D_ni h_a0)/3
since (g wedge Sch)_{n a 0 i}=Sch_n0 h_ai-Sch_ni h_a0,
Sch_na=D_na/3. Project with H^-1 Y^T into the actual
9-coordinate wall carrier. This source is not generically zero.
Thus for m_eff the wall equation has the SAME principal/exchange
matrices, with forcing
 f_eff=f_Codazzi+e0 delta-sum_i B_i e_i delta-L_h delta.
Frame dependence of the tracefree operation is included by
using the same wall orthonormal frame; its derivatives are
part of these actual tangential derivatives. No arbitrary
boundary flux pairing with an uncontrolled mean w trace
remains from the algebraic Ricci jump; it is paid in wall
forcing. Bulk forcing remains the actual Cotton source F_g.
Regularity requirement: tangential derivatives of f_eff through
order s involve order s+1 of the wall Ricci-defect trace; bulk
F_g has one derivative of D. Not a free metric energy estimate.

Conditional W4b theorem: on the SAME given sufficiently regular
matched F metric, with D from that metric, same material frame,
connection, actual Cotton/Codazzi/Schouten sources, same
geometric initial (w,m_eff), and same exterior conditions,
any sufficiently regular projected solution with active jump
A_n([w]-j J m_eff)=0 equals the actual geometric Weyl and
effective mean shape. Proof: the geometric pair satisfies the
projected bulk equations by differential Bianchi and projected
wall equations by Gauss/Codazzi, and the full jump by BR125.
Subtract, apply BR128 homogeneous energy with zero initial
data and zero/nonincoming exterior difference work, conclude
w_diff=m_eff_diff=0. Then the full zero-speed jump and all
geometric Bianchi constraints follow for this pair by equality,
rather than independently assuming an arbitrary projected
source lies in the P0 kernel. The vacuum case D=0 follows
only on a same-solution BR98 vacuum development. This pays the
conditional same-metric preservation implication on a regular
compact chart. Global weighted uniqueness needs the exterior
and localization hypotheses. It does NOT construct a metric,
an independent projected solution, or solve the Cartan
constraint propagation when the metric itself is unknown.
BR53/91 remain relevant to construction, not overwritten.

Given g, a possible projected weak generation route on a
compact tangential torus: use the BR30 dense fixed active-jump
domain and positive time mass above, Galerkin test functions
satisfying the same jump, integrate the normal skew exchange
exactly and use time-dependent positive finite mass ODEs.
A priori L² energy and weak compactness would yield a weak
formulation with the domain pairing; strong traces,
spacetime-jet compatibility and higher regularity still
need a proof. This route is not executed or claimed complete.

### BR130 — actual lapse acceleration in normal curvature transport, weighted inverse

BR127 Gaussian inverse is not directly the material identity.
On arbitrary regular timelike leaves write A=h^-1 K,
a=nabla_n n=-D psi, psi=log lambda, and use the projected
normal derivative D_n on mixed tangential tensors:
 R_e=(R_{n a n b})^sharp
   =-D_n A-A²+(D a)^sharp-a^sharp tensor a_flat
   =-D_n A-A²-lambda^-1(Hess_h lambda)^sharp.
The second identity uses a=-D log lambda and the Hessian
chain rule. Trace gives exactly BR104 Ric_nn.
Independent rational 5D nonumbilic variable lapse/metric
two-jet oracle with non-diagonal h, zero shift, checks all
16 mixed normal curvature components. In general nonzero
shift use projected connection derivative, not raw partial_y.
The curvature sign and acceleration term also follow from
the Ricci identity on n, decomposing nabla_n n and nabla_X n.
Linearizing in a fixed normal-parallel comparison frame yields
 D_n B+A B+B A=-E_eff, B=delta A,
 E_eff=delta R_e+delta(lambda^-1 Hess_h lambda)^sharp
       +(delta D_n)A.
All frame, metric and normal variations in the last terms
are retained; this is not closure of the lapse-Hessian debt.

Let r be proper normal along a regular segment, U'=U A,
V'=A V, U(0)=V(0)=I, Z=U B V. Then Z'=-F,
F=U E_eff V. For any positive integrable weight omega,
let Qomega=int omega, and momega=Qomega^-1 int omega Z
(the TRANSPORTED moment). Exact weighted primitive inverse:
 Z(r)=momega+Qomega^-1 int_0^d omega(x) int_0^x F
                        -int_0^r F,
 B=U^-1 Z V^-1.
For |A|<=a0 on length d and weight 0<omega_min<=omega<=omega_max,
using ||Z||<=|momega|+2 int |F| gives for positive
submultiplicative component norms
 ||B||_{L2(omega)} <= exp(2a0 d) sqrt(Qomega)|momega|
      +2 exp(4a0 d) sqrt(Qomega int omega^-1)
                           ||E_eff||_{L2(omega)}.
Cauchy-Schwarz supplies the last factor. For scalar A=k I,
b(0)=1, U=V=b I and omega=1, this recovers BR57's
b² shear moment. General transported moment must be attached
to original BR31/BS11 graph/holonomy, not freely set to zero.
Alternatively BR125 supplies B(0) if actual metric/wall
regularity and Ricci trace are paid. Uniform normal segment
length, coefficient and weight distortion across the actual
Hopf foliation, global coordinate coverage and focal/holonomy
compatibility remain W5.

Exterior: reopen BR31/BS12 actual static reference weights
N³ dvol ~ R^4 dR, outer curvature work ~ R^6 W_even W_odd.
For even W=O(R^-p) and odd W=O(R^-(p+1)), p>=3,
energy tail integrable and flux tends zero (p=3 gives
R^-2 energy and R^-1 work). Without parity p=3 gives
O(1) flux, not vanishing. These are explicit sufficient
asymptotic hypotheses inherited from BR31, not established
for evolved nonzero geometry or independent projected W.
The static Bel/Killing current and material projected energy
must be matched before using this bound as a global estimate:
BR128's coordinate coefficient work may grow at AdS infinity,
and projected fields are not automatically divergence-free
Bel tensors. No global weighted exterior coercivity claim.

### BR131 — Cartan development route for W6, exact defects and wall obstruction

Reuse the existing general Levi-Civita/Bianchi interfaces
and BR120/121 material chart. For metric-compatible Lorentz
connection Omega and coframe theta, define curvature
F_Omega=dOmega+Omega wedge Omega and torsion
T=dtheta+Omega wedge theta. Work in temporal frame gauge
Omega_t=0 along a given timelike coordinate flow, with theta_t
not necessarily constant (wall flow need not be geodesic).
For prescribed algebraic Riemann carrier R=W+g wedge Schouten,
the time equations
 partial_t Omega_i=R_{ti},
 partial_t theta_i=partial_i theta_t+Omega_i theta_t
impose E_ti=0 and T_ti=0 for E=F_Omega-R.
Exact Cartan differential identities:
 D_Omega E=-D_Omega R,
 D_Omega T=F_Omega wedge theta.
If the FULL unprojected Bianchi D_Omega R=0 and algebraic
R wedge theta=0 hold, the remaining spatial defects satisfy
 partial_t E_ij=0,
 partial_t T_ij=E_ij theta_t.
More generally partial_t E_ij=-(D_Omega R)_{tij}.
Zero initial defects then imply actual torsion-free
metric-compatible curvature, hence same-source Levi-Civita
and actual Riemann. In vacuum select Sch=-g/2; if reduced
retain actual Sch with D as in BR90. These are conditional
Cartan defect equations, not proof that the projected
35D evolution implies the unprojected equations on the
unknown coframe/connection. Need the combined constraint
propagation and wall matching theorem before construction
can invoke this route. Local oracle computes noncommuting
polynomial connection and coframe on 1+2 coordinates,
checks Cartan identities directly; the general exterior
calculus derivation is dimension-independent, not a full
5D nonlinear solution test.

Do NOT fix theta_t to a common unit ambient geodesic
tangent to the wall on both faces. For a unit wall timelike
T, [K(T,T)]=-j !=0. Both ambient accelerations cannot vanish;
a frame parallel along coordinate time need not be the
wall-adapted orthonormal frame. Must transport the actual
BR29 frame through the temporal gauge and pay the wall
embedding/gauge/lapse choices (BR120/121). This is the
exact new construction cut, not an arbitrary source change.

### Updated max-cut and acceptance

W4b: conditional same-g regular projected uniqueness paid
analytically (BR128/129). Unconditional same-object existence
and full Cartan constraint evolution on unknown g remain.
W2/3: regular given-metric compact tangential E_s hierarchy
and Ricci-defect forcing attachment paid at a priori level.
Actual nonlinear tame coefficient control, normal derivatives,
higher corners and weighted exterior remain.
W5: nonumbilic material acceleration and weighted transported
moment inverse constructed; actual lapse-Hessian control,
uniform coverage, original holonomy and exterior closure open.
W6: temporal Cartan equations with explicit torsion/curvature
defect conditions written; no nonlinear fixed point or complete
initial-boundary construction claimed. Need actual compatible
BN/BQ corners, full unprojected Bianchi/Cartan subsidiary,
wall gauge/embedding, coupled normal/exterior estimates.
Keep W4a conditional BR98 and W7 native/physical acceptance.

Local SymPy 1.14.0 four stages exit zero, bounded 90s each;
checker Git blob 9dec80672c8b59c75afa8c877d8d54f6d8d86644.
BR128/129 import the existing BR29 carrier; local execution
used the extracted carrier/read definitions from the fetched
donor (not a full repository checkout/replay). BR130/131
independent symbolic tests. Native kernel and integrated
PDE unrun; no CI. Targeted owner audit, not exhaustive master
reconciliation. No new detached deliverables.
