# Gate 3 Adelic Sobolev PAWOTG Roadmap

Date: `2026-06-01`
Status: `roadmap/theorem surface; non-promoting; Gate 3/Gate 4 bridge target`

This note corrects the Gate 3/Gate 4 roadmap framing for the adelic Sobolev
route.  The earlier "external collaboration target" language was wrong for the
core tower: the relevant PAWOTG structure already exists locally as
`ParametricAlgebraicWaveObservableTransportGeometry`.  The remaining work is
not to ask an external collaborator to invent the tower, but to bind the
existing tower to the adelic Sobolev comparison obligation without promoting
Gate 5, Clay, or terminal physics closure.

The local tower already has the regime layers needed for the comparison:
Harmony, Continuity, Reproducibility, Coherence, Normalization, Transport,
Observable, and Geometry.  It also has known-limits consumers and hooks through
the recovered WOTG side, including `KnownLimitsQFTBridgeTheorem` and the GR/QFT
known-limits boundary.  Those hooks are bridge surfaces only.  They do not
claim a full recovery of QFT, GR, Standard Model dynamics, or a continuum Clay
theorem.

## 2026-06-02 Digit-Expansion Partial Result

The current strongest positive PAWOTG calculation is now recorded in:

```text
DASHI/Physics/Closure/Gate3DigitExpansionPAWOTGPartialResultReceipt.agda
```

For the digit-expansion embedding

```text
phi_digit(sum a_k p^k) = sum a_k p^(-k-1),
```

uniform digits give

```text
Var(phi_digit) = 1/12
sigma = 1/sqrt(12) ~= 0.2887
```

independently of `p`.  Since the binding Gate 3 threshold is
`sigma_crit(p=3) = 0.5052`, this embedding satisfies the PAWOTG spread bound
for every prime and every BT level; refinement improves the spread by the
factor `p^{-j}`.

This is a genuine partial result: PAWOTG is not vacuous, and a natural
adelic-to-Archimedean map passes the threshold.  The remaining theorem is
specificity: prove that the SSP/CM/Hecke atom embedding is `phi_digit` or has
the same uniform spread.  Until that is shown, `inf_N A_N > 0`, Mosco recovery,
no spectral pollution, Gate 3 closure, and Clay promotion remain open.

## Corrected Target

The new theorem target is:

`AdelicSobolevWaveObservableTransportGeometryTheorem`

Its intended position in the closure lattice is above the existing
`KnownLimitsQFTBridgeTheorem` consumer surface and below the product formula
constraint layer represented by `ProductFormulaConstraint`.  In other words,
the theorem should consume local WOTG/PAWOTG structure and known-limits bridge
language, then supply a disciplined adelic Sobolev comparison target before
any product-formula-level closure claim is allowed.

This target is now represented by the Agda theorem surface
`DASHI.Physics.Closure.AdelicSobolevWaveObservableTransportGeometryTheorem`.
That module records the PAWOTG/QFT/product-formula routing, saturated `Sig15`
admissibility, and the candidate adelic Plancherel inequality statement.  It
does not promote the analytic norm-comparison proof, Clay NS, Clay YM, QFT
recovery, or terminal physics closure.

## Norm Map

The bridge should be stated as a norm-compatibility problem, not as a generic
request for external formalism.

| Source norm | Local target | Required binding |
| --- | --- | --- |
| Archimedean Sobolev norm | Observable norm | Map the analytic arch norm into the Observable layer as the real-valued readout that the carrier comparison must dominate. |
| p-carrier norm at each SSP prime | TransportGeometry norm | For each SSP prime, interpret the p-carrier norm as a TransportGeometry norm with explicit prime-indexed transport data. |
| Adelic bridge inequality | WOTG coherence | Express the bridge inequality as a WOTG coherence condition rather than an informal analytic analogy. |
| Hecke scan saturation | `Hecke.Scan` / `Sig15` saturation | Require the coherence witness to survive the finite `Sig15` scan/saturation boundary; saturated signatures are diagnostics, not closure by themselves. |

The central obligation is therefore:

`arch-observable-norm <= adelic-comparison(p-carrier TransportGeometry norms)`

with the comparison routed through WOTG coherence and checked against the
Hecke `Sig15` saturation surface.  The inequality must be a bridge lemma with
named hypotheses, not a prose statement that local p-adic data automatically
controls the Archimedean Sobolev norm.

## Revised Gate Estimates

These are planning estimates for the current proof surface, not theorem
completion percentages.  They record relative difficulty and dependency order
for the Gate 1, Gate 6, Gate 2, Gate 3, Gate 4, Gate 5 sequence.

| Gate | Task | Revised estimate | Current reading |
| --- | --- | --- | --- |
| Gate 1 | `Y_d` texture numerical fit | 1-2 sessions | Unchanged. |
| Gate 6 | `p=7` independence graph | 2-4 sessions | Unchanged. |
| Gate 2 | NS conditional tail dominance | 3-6 sessions | Unchanged. |
| Gate 3 | Adelic Sobolev bridge | 5-10 sessions | The old external-collaboration framing is retired.  The local PAWOTG/WOTG tower supplies the theorem grammar; the hard part is the actual adelic Sobolev inequality and `Sig15`-stable coherence. |
| Gate 4 | Hecke envelope preservation | 3-5 sessions | `Hecke.Scan` plus a finite `K*(nu)` envelope give the local framework; the preservation theorem is still open. |
| Gate 5 | YM Clay continuum | years | Constructive QFT, OS axioms, reflection positivity, and infinite-volume limit remain external to the current formalism. |

The revised order is intentionally `1, 6, 2, 3, 4, 5`: first ensure carrier and
DHR/QFT readout sockets are honest, then use finite energy/spectral surfaces
only as inputs, then build the Gate 3 adelic Sobolev/WOTG bridge, then pass
only bounded geometry data toward Gate 4, while keeping Gate 5 outside the
claim.

## Eigenspace Correction

The current eigenspace bookkeeping must use the corrected intrinsic/extension
split:

| Class | Primes | Reading |
| --- | --- | --- |
| Intrinsic `Z/3` | `p=7,13,19,31` | These primes carry the intrinsic threefold eigenspace structure. |
| Extension-needed | `p=2,5,11,17,23,29,41,47,59,71` | These primes require an extension before the corresponding threefold eigenspace can be stated. |
| Ramified | `p=3` | The ramified prime is separated from the intrinsic and extension-needed lists. |

Within the intrinsic class, `p=7` remains the unique lowest intrinsic case and
the CM-compatible case for `Q(sqrt(-7))`.  This is the correct place to cite
the `p=7` CKM/CM convergence story: it supports a local arithmetic selection
surface, not a physical CKM matrix, not a full Standard Model derivation, and
not a Clay theorem.

## Governance Boundary

This roadmap records a revised theorem surface and dependency map.  The
corresponding Agda module is wired as a non-promoting theorem surface; the
proof obligation remains the analytic adelic Sobolev comparison.

The PAWOTG tower being local changes the work plan, not the promotion status.
The bridge still requires a real proof of the adelic Sobolev inequality, an
explicit mapping from arch norm to Observable norm, explicit SSP-prime
p-carrier to TransportGeometry norm bindings, and a WOTG coherence witness
stable under `Hecke.Scan` `Sig15` saturation.

No Gate 5 closure, Clay Navier-Stokes closure, Clay Yang-Mills closure, GR/QFT
terminal closure, Standard Model reconstruction, or product-formula closure
follows from this document.

## 2026-06-02 Analytic Evidence Bundle

The current PAWOTG/Gate 3 diagnostic artifacts are staged under:

```text
Docs/Images/clay-analytic-sprint/
```

Relevant files:

- `gate3_frame_extended.csv`
- `gate3_sampler_quality.csv`
- `pawotg_sigma_crit.png`
- `pawotg_sigma_crit_1.png`
- `pawotg_sigma_crit_2.png`

Checked receipt links:

- `DASHI/Physics/Closure/Gate3PAWOTGConcreteConditionReceipt.agda`
- `DASHI/Physics/Closure/Gate3GershgorinFiniteFrameBoundReceipt.agda`
- `DASHI/Physics/Closure/Gate3ScaleGraphBarrierInstantiationReceipt.agda`

The concrete PAWOTG target remains the BT-overlap condition

```text
S_p(sigma) = sum_{d>=1} p^d exp(-((log p)^2 d^2)/(4 sigma^2)) < 1
```

with binding critical spread `sigma_crit(p=3) = 0.5052`.  The computed
inert-prime threshold table now recorded in
`Gate3PAWOTGConcreteConditionReceipt.agda` is:

| Prime/block | Computed `sigma_crit` reading |
| --- | --- |
| `p=3` | `0.5052` binding row |
| `p=5` | `0.6225` |
| `p=13` | `0.7891` |
| `p=17` | `0.8334` |
| `p=19-59` | `0.86-1.05` range |

The supplied finite-frame CSV is a diagnostic obstruction, not a proof: the
sampled dictionaries fail the Gershgorin condition in every row, and `A_N`
collapses to numerical zero at larger `N`, including the phase-complete toy
rows.  The correct theorem surface therefore remains conditional:

```text
finite separation -> finite A_N > 0
PAWOTGUniformSeparation -> uniform lower control -> Mosco/no-pollution route
```

The refined sampler-quality file `gate3_sampler_quality.csv` makes the
engineering failure explicit: the current sampler has `mu_N` near `1`, while
the strict Gershgorin target is `mu_N < 1/(N-1)`.  The next sampler target is:

```text
AtomSamplerPAWOTGQuality : mu_N <= C / N
```

or at least enough quasi-uniform phase/twist placement to keep
`(N-1)mu_N < 1`.

No Gate 3 closure, Mosco recovery proof, no-spectral-pollution theorem,
mass-shell transfer, or Clay promotion follows from the artifacts.

The blocker classification is checked at:

```text
DASHI/Physics/Closure/ClayBlockerAsymmetryReceipt.agda
```

For Gate 3, this records `PAWOTGUniformSeparation` as new
adelic-localization mathematics, not a routine final lemma and not a theorem
already supplied by finite Kozyrev orthogonality.

`MonsterMoonshineSSPQuotientControl` now sits above the Gate 3/YM interface as
a separate quotient/compression blocker.  The 15SSP/moonshine carrier may
compress the effective contour family, but it is not an entropy multiplier and
does not turn the raw `c2/c1 ~= 109` ratio into the physical polymer entropy
constant `C0`.  Gate 3 may cite this only as a target for proving quotient
control of the SSP carrier.  Until that theorem exists, use the fail-closed
branches: `C0_eff ~= 1` gives the YM `beta_abs ~= 12.97` target if quotient
control holds; square-root/raw leakage would raise the threshold to about
`22.66`/`32.35`.  No PAWOTG theorem, quotient theorem, YM mass gap, or Clay
promotion follows from this bookkeeping.

## Why This Is Still Open

`PAWOTGUniformSeparation` is not a bookkeeping lemma.  To inhabit it, the
programme needs:

1. an explicit adelic-to-Archimedean atom map from the `p`-adic/SSP carrier
   into the continuum target;
2. a proof that the Archimedean images of the carrier atoms have Gaussian
   envelope localization;
3. a proof that the spread stays uniformly below the binding threshold
   `sigma_crit(p=3) = 0.5052` as the cutoff/refinement level tends to infinity.

Kozyrev wavelets provide orthogonality on the `p`-adic side.  They do not by
themselves supply uniform Archimedean localization after transfer.  This is why
the current PAWOTG condition is a precise open theorem rather than a solved
Gate 3 bridge.

## Adelic Localization Reduction

The next checked receipt is
`DASHI/Physics/Closure/Gate3AdelicLocalizationReductionReceipt.agda`.
It records the strongest honest theorem surface currently available:

```text
ExplicitAdelicEmbedding phi
  + GaussianSpreadBelow sigma_crit phi
  + sigma_crit < 0.5052
  -> inf_N A_N > 0
```

This is a reduction, not an inhabitant.  It binds the uniform frame lower-bound
problem to a concrete localization estimate for the Archimedean images of SSP
carrier atoms.

The literature side is recorded fail-closed:

- the `p=2` Kozyrev/Haar map is the only model case treated as already
  theorem-backed in this lane, with `sigma=0`; this is related evidence only
  and is not a proof of SSP `p>=3` localization;
- the SSP primes `p>=3`, especially the corrected inert block, still need an
  explicit adelic embedding and uniform localization control;
- the Weil-representation/theta-correspondence route is the proposed attack
  route because it can expose the Archimedean spread of the transferred
  p-adic wavelet through computable symbols.

Until that localization estimate is proved, Mosco recovery,
no-spectral-pollution, mass-shell transfer, Gate 3 closure, and Clay promotion
remain false.

## Uniform Separation Target Receipt

The exact next theorem target is now pinned by
`DASHI/Physics/Closure/Gate3PAWOTGUniformSeparationTargetReceipt.agda`.
It consumes the existing localization, concrete PAWOTG, adelic Sobolev norm,
Mosco, no-spectral-pollution, and scale-graph barrier receipts and records:

```text
ExplicitAdelicEmbedding phi
  + GaussianSpreadBelow sigmaCrit phi
  + sigmaCrit < 0.5052 at p=3
  -> inf_N A_N > 0
  -> Mosco/no-pollution/mass-shell route becomes available
```

The receipt keeps the remaining obligations explicit: construct `phi`, prove
`p>=3` Archimedean localization, prove uniform-in-depth spread, transfer the
separation result to Mosco recovery, and then transfer Mosco to no spectral
pollution.  It is non-promoting: Gate 3 closure and Clay promotion remain
false.
