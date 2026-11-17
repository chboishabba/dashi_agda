# Smith/Filsinger F10-STOKES — four-direction rational space-time work and selected original boundary
**17 November 2026 · PR #1524 · Agda source candidate, NOT kernel receipt**

## Max-cut result: reuse source rather than duplicate a Maxwell theorem

Existing canonical owners:
- `DASHI/Physics/Plasma/KSW668FullVectorMaxwellJetExact.agda`: actual three-component pointwise Maxwell curl and Poynting identity in the C3 real-field carrier. A differential jet alone is not a global field with a surface/time integral.
- `DASHI/Physics/YangMills/YangMillsLatticeStressWardSliceConservationExact.agda`: `differencePartialTelescopes`, a general exact finite rational forward-difference sum theorem, valid beyond the Yang–Mills application.
- `DASHI/Physics/Motors/SmithFilsingerOpenBoundaryPoyntingGaussExact.agda`: **open**, not periodic, three-axis outward Poynting finite-face flux telescope, plus conditional `OriginalMaxwellOpenFaceTrace` linking real Maxwell field integration to a physical original source boundary.
- `SmithFilsingerIndexedFaceIncidenceExact.agda`, `SmithFilsingerIndexedSignedCellStokesExact.agda`: per-face endpoint uniqueness and signed internal-face cancellation.
- `SmithFilsingerSourceMaxwellBoundaryWeldExact.agda`: historical original source/port selection; Smith suitcase, original Earth reel and portable Filsinger proposal are not identified by name alone.
- `SmithFilsingerMaxwellMaterialEnergyCutExact.agda`: prevents material/controller ledger double counting.

## New exact four-direction mathematical construction

New `DASHI/Physics/Motors/SmithFilsingerSpaceTimePoyntingTelescopeExact.agda` adds one **time-direction** finite telescope to the existing three spatial open-boundary telescopes. It uses rational signed work, not arbitrary nonnegative Nat work, and keeps the exterior source flux, radiation and energy depletion visible.

`FiniteSpaceTimeWindow` carries rational stored-energy samples `U(n)`, three oriented spatial face sequences `S_x,S_y,S_z`, signed natural/controller **volume** driving, material+ion loss, useful receiver work and a separately supplied *finite-difference local work law*. The mathematical theorem `spaceTimeExteriorEnergyBalance` derives

[
 (U(T)-U(0)) + \Phi_{\mathrm{exterior,outward}}
       + Q_{\mathrm{material,ion}} + W_{\mathrm{receiver}}
   = W_{\mathrm{natural,volume}} + W_{\mathrm{controller,volume}}.
]

Here `Phi_exterior,outward` is **signed net outward Poynting work**, not a presumed nonnegative radiant loss. Its three-axis expression retains BOTH low/high exterior faces, e.g. `S_x(xmax)-S_x(xmin)`. Any natural energy **entering across the boundary** must be represented with negative outward sign, NOT added again as `W_natural,volume`.

The proof uses `Ward.differencePartialTelescopes` for the stored energy in time and `Open.finiteOpenBoundaryPoyntingGauss` for space. The discrete local work law is a real independent assumption: this **does not yet integrate Maxwell's PDE** or prove a calibrated Yee scheme. Different time/face quadratures must be physically matched.

`DisjointExteriorPowerPartition` requires the signed exterior flux to be decomposed explicitly into natural incoming/outgoing, controller incoming/outgoing and other outgoing radiation; `partitionedSpaceTimeExteriorBudget` transports the exact same energy law with those ports named, preventing source double counting by bookkeeping.

`DecomposedSpaceTimeWork` disaggregates Ohmic heat, ADE relaxation, ion/chemical heat, electric driver, parametric material pump, ion creation pump and neutral-wind mechanical power. `decomposedSpaceTimeExteriorBudget` is derived by substitution, not a new physical energy-conservation law. Positivity of heat and the actual full plasma thermochemical model remain **separate physical admissions**; the rational algebra itself permits either sign.

## Real Maxwell and same historical source

`SameOriginalSpaceTimeMaxwellAdmission jet` requires the existing `Open.OriginalMaxwellOpenFaceTrace jet`, exact spatial-face identity, and explicit identification of real integrated natural, controller, material and load work at the same time window. `sameOriginalSpatialExteriorFlux` consumes the original KSW668 Poynting jet via `Open.originalFullVectorJetOpenBoundaryFlux`; `sameOriginalTimeIntegratedPowerBalance` then transports the rational four-direction budget. This is **conditional on physical field integration**, not an original-electrode field solution.

New `SmithFilsingerSelectedSpaceTimePortWeldExact.agda` strengthens this to `SelectedBoundary b` and `FormalFieldToPort b` of the **same historical original**. It adds an additive rational work calibration from Nat energy quanta and exact equalities identifying original natural incident-minus-outgoing, controller incident-minus-outgoing, load, initial stored and final stored work. The source, receiver and return-path measurement/geometry needed to inhabit these fields remains **OPEN**. The mathematical conservation theorem is consumed, never independently assumed again.

No arbitrary phase readout or calculated fair-weather shunt is promoted to independent solar work, and a source-controlled plasma bridge may carry much more power than a passive linear conductor only where actual independent source access is demonstrated.

## Independent exact arithmetic controls

New `scripts/test_smith_filsinger_space_time_poynting_telescope_exact.py` tests:
- **800/800** independent exact Fraction four-direction windows (8 seeds × 100), with varying temporal counts, each spatial axis and signed source/controller terms.
- Source-off **storage discharge** can pay a load for a transient but does not imply replenishment.
- Negative signed natural source work is admissible.
- Removing one unit of controller/ionization cost breaks the exact budget.
- Reversing one exterior-face orientation breaks the source match.
- Open boundary flux does NOT vanish as it would for a wrongly assumed periodic box.
- A finite sampled equation cannot assign original measured natural source current.

The 800 windows plus selected adversarial cases were run locally as an **independent equivalent Fraction checker**, and passed. The committed exact-head pytest suite was **not** run; the pinned Agda 2.9 executable/Nix unavailable in this runtime, so the new source is a proof **candidate**, not a kernel typechecked theorem. Both new Agda targets are in the existing `scripts/check_smith_filsinger_formal_weld_agda29.sh`, and the test is in the existing `scripts/check_smith_filsinger_dynamic_replenishment.sh`.

## Open highest-alpha gates

1. **D1:** pinned Agda kernel verification of *current exact PR head*; source syntax/zero postulates alone is insufficient.
2. **F10-STOKES-physical:** construct a genuine global regular or weak Maxwell field with exact/controlled signed spacetime Poynting quadrature; local field+ADE/Hall/neutral/ion work law must be proved **from field equations**, not simply specified in the record.
3. **F10-INTEGRATION:** weld signed rational time/face values and the previously authored `IndexedSignedCellStokes` unique 3D face-ID structure, including genuine space/time geometry, unit dimensions and face normals; current rectangular and general mesh carriers are complementary but not automatically identical.
4. **F02-CONE:** separately prove true retarded propagator support for specified material assumptions; Yee CFL is only a numerical stability constraint.
5. **F13-GREEN/PORT:** actual source/return terminals, conduction + displacement current, contour-dependent voltage, nonlinear plasma and real soil–air–ionosphere Green kernel; measured source backaction/replenishment.
6. **F15/R3:** original, independently replenished signed natural work over a restored source+receiver+material cycle, full controller/plasma/ion cost and repeatability; 100× physical gain is OPEN.
7. **F14/F16:** original actual phase/electrical/acoustic and rainfall/cold-pool chain remain separate, OPEN.

**Attribution:** classical Maxwell/Poynting/Gauss/Yee are external; Yang–Mills finite algebra and KSW668 original physical jet are reused DASHI theorem owners. The Sun–Earth Smith/Filsinger solar-source harvesting steelman is user-origin and not attributed to these external authors. ESD surfaces untouched, no premature TOE import graph promotion.


## Exact Maxwell field witness, not merely a chosen energy ledger

New `SmithFilsingerPlaneWaveSpaceTimeWitnessExact.agda` uses the existing `Rational.rationalRealField` and the actual KSW668 three-component curl jet. It constructs the smooth affine travelling vacuum solution (in normalized units)

[
 E=(0,A,0),\quad B=(0,0,A),\quad
 A=a+b(x-t),\quad J=0 .
]

The authored `planeAmpere` and `planeFaraday` rational polynomial proofs establish its Maxwell differential jet conditions; `planeJetSatisfiesOriginalMaxwell` consumes the canonical full-vector Poynting theorem. `planePoyntingXFromFullVector` equates the real three-vector cross-product face flux with `A²`, where the electric+magnetic energy density is also `A²`.

For a **selected discrete, matched-width** time/space control, `planeWaveExactSpaceTimeCell` proves

[
U(x,t+h)-U(x,t) + S_x(x,t)-S_x(x-h,t)=0 .
]

The result is a nontrivial finite sample/flux control with changing storage and opposite signed flux. `planeWaveFiniteSpaceTimeWindow` constructs the canonical four-direction record, `planeWaveSamplesMeetFourDirectionOwner` **actually applies** `SpaceTime.spaceTimeExteriorEnergyBalance`, and the right/left field-face readbacks use `Sample.poyntingFaceSample`. Unlike a proof `P=P` by `refl`, this is a concrete constructed local work identity fed into the prior Stokes owner.

**Scope:** an affine travelling plane wave has unbounded energy when extended to all space; it is a smooth control on a bounded observation domain, not a finite-energy environmental generator or original device. The discrete time/face sample law is not the general physically integrated Yee/Poynting theorem; nonlinear plasma, Hall/Pedersen, Maxwell retarded waveguide, atmospheric Green kernel and real source data remain independent. CFL stability does not alone imply physical support.

New independent exact rational regression `scripts/test_smith_filsinger_plane_wave_spacetime_exact.py`: **1,200/1,200** rational characteristic and changing-energy cell identities PASS, with a mismatched time/space stride negative control. Source-authored theorem has **no pinned Agda kernel receipt**. Both new formal and Python owners are part of the existing check scripts.

Additional source-paid negative controls added to the 4-axis test: four units of natural work entering through an outward-negative face cannot also be counted as four units of natural volume injection; omitting separately counted ionization work breaks the same-window equality. They are pure arithmetic tests and not observations.
