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
