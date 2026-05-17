# Compressed GR/QFT Import Roadmap

## Status

The current GR/QFT roadmap has a new import-compression lane.  The lane records
three external formal candidates as leverage points, but it does not promote
any local DASHI physics receipt from citation alone:

- `DCHoTT-Agda` / Wellen-Cherubini differential cohesion in Agda: candidate
  infrastructure for manifolds, formal disks, frame bundles, Cartan geometry,
  and torsion-free G-structure style metric-adapter work.
- Haag-Kastler stacks / locally covariant AQFT: candidate infrastructure for a
  local-algebra net receipt that avoids choosing one global Fock
  representation as the primitive QFT carrier.
- Schreiber's modal/cohesive HoTT physics programme: candidate ambient grammar
  for comparing carrier transport, metric adapters, gauge fields, and AQFT
  locality in one cohesive vocabulary.

The corresponding Agda surface is
`DASHI.Physics.Closure.ExternalFormalImportRoadmapReceipt`.  Its canonical
receipt records the timeline compression as real, but keeps
`theoremImportedIntoDASHI` false.  The DCHoTT dependency is now cloned locally
and the flat import shim typechecks.  The next bridge surface,
`DASHI.Geometry.LeviCivitaBridge`, also typechecks against the actual exported
`G-structures` socket.  This is a bridge socket, not theorem promotion: B0
geometric emergence, torsion-free specialisation, and Levi-Civita uniqueness
remain open.  `DASHI.Geometry.DCHoTTBridgeObligationIndex` now decomposes B0
into four open audit targets: carrier-to-formal-D-space, wave-coherence to
flat formal disk, refinement stability to G-structure, and G-structure to
Levi-Civita specialisation.  It additionally names the concrete B0.1 compatible
family/formal-disk scaffold, the B0.2 flat-formal-disk target, and the B0.3
refinement-stable frame/metric/pro-frame target without constructing a DCHoTT
manifold, G-structure, torsion-free specialization, or Levi-Civita adapter.
The Haag-Kastler stack surface is also now recorded as a
self-contained DASHI receipt at `DASHI.Physics.Closure.AQFTNetReceipt`; this
is a governance/intake surface, not a concrete QFT carrier.  The first
free-field witness and boundary surfaces are also now explicit:
`DASHI.Physics.Closure.KleinGordonAQFTReceipt` records the cited
Klein-Gordon stack witness, while
`DASHI.Physics.Closure.InteractingQFTBoundaryReceipt` records constructive
interacting nets as the first open QFT obligation.  `DASHI.Physics.QFT.AQFTTypedNetSurface`
adds the typed local-algebra interface that those receipts should refine
toward; it is still abstract and does not construct a C*-algebra, GNS state,
Born-rule adapter, or interacting theory.

## DCHoTT Intake State

The local clone is:

- path: `DCHoTT-Agda`
- remote: `https://github.com/felixwellen/DCHoTT-Agda.git`
- commit: `ca8c755af0b26f8f50c5a60d3b7f9384a26f5d0e`
- local Agda: `2.6.4.3`
- stdlib lib file: `/usr/share/agda/lib/standard-library.agda-lib`
  (`standard-library-2.0`)
- license file: not present in the cloned repository root; license remains an
  intake item before vendoring or redistribution claims

The clone uses a flat module layout.  Imports are therefore:

```agda
open import Manifolds
open import FormalDiskBundle
open import G-structure
```

not `DCHoTT.Manifolds` or other namespaced forms.  The project library file
adds `DCHoTT-Agda` to `include:` so `DASHI.Geometry.DCHoTTImportShim`
can typecheck these imports.

The immediate exported bridge sockets are now identified:

| DCHoTT module | Exported socket | DASHI use |
| --- | --- | --- |
| `HomogeneousType` | `homogeneous-structure-on_` | model homogeneous carrier for manifold targets |
| `Manifolds` | `_-manifold`, `homogeneous-space-as-manifold` | manifold socket and homogeneous example |
| `FormalDiskBundle` | `formal-disk-bundle`, `T∞`, `T∞-as-dependent-type` | infinitesimal/formal-disk carrier bridge |
| `G-structure` | `groups-over-automorphismgroup-of_`, `G-structures`, `G-str→` | G-structure lift/pullback surface |

`G-structure.agda` contains a comment saying the code will work toward
torsion-free G-structures, but this clone does not expose a
`TorsionFreeGStructure` identifier.  The Phase 2 bridge must therefore target
the currently exported `G-structures` surface first, then add or import the
torsion-free/Levi-Civita specialization separately.

`DASHI.Geometry.LeviCivitaBridge` is now that first surface.  It imports the
real DCHoTT `G-structures` socket, links the existing DASHI flat
`GRConcreteLeviCivita` prerequisite and downstream
`DiscreteEinsteinTensorCandidate` diagnostic, and records B0 as the first open
obligation.  It intentionally does not construct an Einstein tensor, GR
promotion, G6/W7 promotion, or a GRQFT closure receipt.

## Local Overlap Audit

The repo is not empty on these themes.  The audit distinguishes local overlap
from imported external formal infrastructure:

| Surface | In repo? | Current reading |
| --- | --- | --- |
| Flat Levi-Civita prerequisite | yes | `GRConcreteLeviCivita.agda` closes only the selected flat Minkowski finite-r prerequisite. |
| Non-flat Levi-Civita / metric adapter | no | The non-flat route is still blocked on scalar algebra, Christoffel-from-metric, Ricci, and Einstein-tensor laws. |
| GR/QFT consumer obligation | yes | `GRQFTConsumerNextObligation.agda` names downstream fields and keeps the promotion token constructorless. |
| AQFT net receipt | yes | `AQFTNetReceipt.agda` records the point/descent/isotony/causality/time-slice contract from arXiv:2404.14510v2, while keeping GNS/vacuum, Born rule, representation choice, and interacting QFT open. |
| Klein-Gordon free-field witness | yes | `KleinGordonAQFTReceipt.agda` records Theorem 4.41 as a cited witness surface, while keeping the concrete algebra-net reconstruction, vacuum selection, and Born rule open. |
| Interacting-QFT boundary | yes | `InteractingQFTBoundaryReceipt.agda` names constructive interacting local algebra nets, renormalisation, and coupling calibration as open obligations. |
| Adapter-boundary matrix | yes | `Docs/PhysicsLaneMaturityMatrix.md` already records metric, representation, GNS/vacuum, Born-rule, and calibration boundaries. |
| DCHoTT dependency / import shim | yes | `DCHoTT-Agda` is cloned locally and `DASHI.Geometry.DCHoTTImportShim` typechecks against its flat modules. |
| DCHoTT Levi-Civita bridge socket | yes | `DASHI.Geometry.LeviCivitaBridge` typechecks against `G-structures` and records B0 as first open obligation. |
| DCHoTT B0 obligation index | yes | `DASHI.Geometry.DCHoTTBridgeObligationIndex` splits B0 into four open sub-obligations, records B0.1/B0.2/B0.3 target surfaces, and constructs no B0 promotion receipt. |
| AQFT typed net surface | yes | `DASHI.Physics.QFT.AQFTTypedNetSurface` introduces typed region/local-algebra sockets for isotony, causality, time-slice, and descent while keeping concrete C*-algebras, GNS, Born, vacuum, and interacting QFT open. |
| DCHoTT imported theorem | no | The shim sees manifold/formal-disk/G-structure surfaces but imports no torsion-free Levi-Civita or B0 theorem. |

So the corrected state is: DASHI already has substantial native bridge targets
for the import work, DCHoTT flat import resolution and the first
`G-structures` bridge socket are now live, B0 has a four-part obligation index,
and the AQFT stack contract, typed local-algebra surface, Klein-Gordon
free-field witness, and interacting-QFT boundary are locally receipted.  No
DCHoTT theorem, concrete AQFT algebra net, interacting QFT
construction, or cohesive theorem has been consumed yet.  The next action is
replacing the B0 postulate and refining the AQFT receipts into typed carriers,
not a from-scratch conceptual design pass.

## Roadmap Compression

| Stage | Previous stance | Compressed stance | Promotion boundary |
| --- | --- | --- | --- |
| Stage 2 metric adapter | build Levi-Civita/metric-adapter machinery locally | import or bridge to DCHoTT torsion-free G-structure and frame-bundle infrastructure | only after exact dependency intake and Agda bridge typecheck |
| Stage 3 QFT carrier | start from Fock/CCR/CAR carrier and hit representation issues early | refine the AQFT net/descent receipt into typed local-algebra carriers; defer GNS/vacuum/Born choices to adapters | AQFT net does not solve interacting QFT or Born/vacuum selection |
| Stages 4-6 GRQFT | compose from locally built geometry/QFT pieces | use cohesive/modal HoTT as the comparison language for geometry, gauge, and locality | no mass-gap, cosmological-constant, coupling, Born-rule, or TOE promotion follows |

## Execution Plan

1. Complete dependency intake for `DCHoTT-Agda`.
   The clone and flat import shim are present.  Remaining intake is license
   clarification and compatibility notes beyond the minimal shim.

2. Replace the B0 bridge postulate with a proof or imported theorem.
   `DASHI.Geometry.DCHoTTImportShim` proves the flat imports resolve, and
   `DASHI.Geometry.LeviCivitaBridge` proves the actual `G-structures` socket
   can be targeted.  `DASHI.Geometry.DCHoTTBridgeObligationIndex` fixes the
   proof checklist so this does not remain one opaque postulate and now records
   the B0.1 compatible family, B0.2 flat-disk, and B0.3 frame/metric/G-structure
   target surfaces. The next deliverable is a proof-grade bridge from DASHI
   wave-coherent/refinement-stable transport into the DCHoTT socket, followed
   by the torsion-free/Levi-Civita specialisation.

3. Write the DASHI-to-DCHoTT translation layer.
   Map DASHI carrier, transport receipt, curvature receipt, admissibility, and
   promotion gates into the DCHoTT/cohesive vocabulary.  Only after this bridge
   typechecks can `LeviCivitaAdapterReceipt` cite an imported theorem.

4. Refine the `AQFTNetReceipt` surface.
   The current receipt names point/descent, isotony, causality, time-slice, and
   Klein-Gordon witness surfaces.  `KleinGordonAQFTReceipt` and
   `InteractingQFTBoundaryReceipt` now separate the free-field witness from the
   interacting-field boundary.  `DASHI.Physics.QFT.AQFTTypedNetSurface` now
   supplies the typed open-region/local-algebra/morphism/descent interface; the
   next deliverable is wiring the governance receipts to this surface while
   keeping GNS state, vacuum selection, Born rule, renormalisation, and
   empirical representation choices as explicit adapters.

5. Connect both bridges to existing GR/QFT consumer obligations.
   The target is better staging for `GRQFTConsumerNextObligation`, not a
   constructed `GRQFTClosurePromotionReceipt`.

## Stop Rule

Do not replace an open obligation with a citation.  Imported formal work can
compress a lane only when the dependency is present, the bridge typechecks, and
the local receipt records the imported theorem boundary.  Until then, the
compressed roadmap is a high-leverage work plan, not a physics closure result.
