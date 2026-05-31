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
