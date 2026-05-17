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
and the flat import shim typechecks; this is dependency intake, not theorem
promotion.

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

## Local Overlap Audit

The repo is not empty on these themes.  The audit distinguishes local overlap
from imported external formal infrastructure:

| Surface | In repo? | Current reading |
| --- | --- | --- |
| Flat Levi-Civita prerequisite | yes | `GRConcreteLeviCivita.agda` closes only the selected flat Minkowski finite-r prerequisite. |
| Non-flat Levi-Civita / metric adapter | no | The non-flat route is still blocked on scalar algebra, Christoffel-from-metric, Ricci, and Einstein-tensor laws. |
| GR/QFT consumer obligation | yes | `GRQFTConsumerNextObligation.agda` names downstream fields and keeps the promotion token constructorless. |
| AQFT net receipt | no | The local-algebra/isotony/causality/time-slice net receipt is still a planned surface. |
| Adapter-boundary matrix | yes | `Docs/PhysicsLaneMaturityMatrix.md` already records metric, representation, GNS/vacuum, Born-rule, and calibration boundaries. |
| DCHoTT dependency / import shim | yes | `DCHoTT-Agda` is cloned locally and `DASHI.Geometry.DCHoTTImportShim` typechecks against its flat modules. |
| DCHoTT imported theorem | no | The shim sees manifold/formal-disk/G-structure surfaces but imports no torsion-free Levi-Civita or B0 theorem. |

So the corrected state is: DASHI already has substantial native bridge targets
for the import work, and DCHoTT flat import resolution is now live.  No
DCHoTT/AQFT/cohesive theorem has been consumed yet.  The next action is a
translation layer, not a from-scratch conceptual design pass.

## Roadmap Compression

| Stage | Previous stance | Compressed stance | Promotion boundary |
| --- | --- | --- | --- |
| Stage 2 metric adapter | build Levi-Civita/metric-adapter machinery locally | import or bridge to DCHoTT torsion-free G-structure and frame-bundle infrastructure | only after exact dependency intake and Agda bridge typecheck |
| Stage 3 QFT carrier | start from Fock/CCR/CAR carrier and hit representation issues early | define an AQFT net/descent receipt first; defer GNS/vacuum/Born choices to adapters | AQFT net does not solve interacting QFT or Born/vacuum selection |
| Stages 4-6 GRQFT | compose from locally built geometry/QFT pieces | use cohesive/modal HoTT as the comparison language for geometry, gauge, and locality | no mass-gap, cosmological-constant, coupling, Born-rule, or TOE promotion follows |

## Execution Plan

1. Complete dependency intake for `DCHoTT-Agda`.
   The clone and flat import shim are present.  Remaining intake is license
   clarification and compatibility notes beyond the minimal shim.

2. Extend the minimal import shim before writing adapter logic.
   `DASHI.Geometry.DCHoTTImportShim` proves the flat imports resolve.  The next
   deliverable is a typed bridge that maps DASHI carrier/transport terms into
   the DCHoTT surfaces without relying on postulated sockets.

3. Write the DASHI-to-DCHoTT translation layer.
   Map DASHI carrier, transport receipt, curvature receipt, admissibility, and
   promotion gates into the DCHoTT/cohesive vocabulary.  Only after this bridge
   typechecks can `LeviCivitaAdapterReceipt` cite an imported theorem.

4. Add an `AQFTNetReceipt` surface.
   The receipt should name local algebra assignment, isotony, causality,
   time-slice, and descent fields.  It should keep GNS state, vacuum selection,
   Born rule, and empirical representation choices as explicit adapters.

5. Connect both bridges to existing GR/QFT consumer obligations.
   The target is better staging for `GRQFTConsumerNextObligation`, not a
   constructed `GRQFTClosurePromotionReceipt`.

## Stop Rule

Do not replace an open obligation with a citation.  Imported formal work can
compress a lane only when the dependency is present, the bridge typechecks, and
the local receipt records the imported theorem boundary.  Until then, the
compressed roadmap is a high-leverage work plan, not a physics closure result.
