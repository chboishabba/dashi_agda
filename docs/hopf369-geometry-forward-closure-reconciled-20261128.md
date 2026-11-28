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
