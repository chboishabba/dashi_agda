# SeaMeInIt ROM kernel formalism

## Intention

This note records the DASHI-side formalism for the SeaMeInIt ROM/kernel/seam
lane found in the sibling repo `../ITIR-suite/SeaMeInIt`.

Agda module:

```text
DASHI.Interop.SeaMeInItROMKernelFormalism
DASHI.Interop.SeaMeInItSeamDerivationFormalism
```

The formalization is deliberately theorem-thin. It is an engineering receipt
model for a production pipeline, not a proof that the external SeaMeInIt
runtime, assets, body fit, solver output, or manufacturing export have been
validated.

## Pipeline Shape

The stable carrier order is:

```text
BodyCarrier
  -> KernelBasis
  -> ROMOperator
  -> ProjectedField
  -> SeamGraph
  -> SeamCutPanelization
  -> ManufacturingReceipt
```

The corresponding operational reading from SeaMeInIt is:

```text
body carrier
  -> basis
  -> ROM projection/operator
  -> projected tension/pressure/shear/support fields
  -> seam graph and seam cuts
  -> panels
  -> manufacturing receipt
```

The matured seam derivation reading expands that operational pipeline to:

```text
input evidence
  -> admissible body/ROM/fabric carrier
  -> projected surface fields
  -> seam-cost graph
  -> seam topology
  -> panel topology
  -> flattening residuals
  -> darts/ease/gussets/splits
  -> manufacturing allowances
  -> finished pattern receipt
```

Darts, ease, gussets, pleats, stretch panels, and panel splits are not
post-hoc tailoring annotations. In this formalism they are discrete
metric-correction operators promoted only when they absorb flattening or
curvature residual enough to pay for their added manufacturing, comfort,
accessibility, and description cost.

This is a DASHI observation-and-transport surface: each stage is a carrier with
a receipt boundary. Downstream artifacts should not be promoted when an
upstream carrier, basis, ROM, solver domain, seam cost, panel unwrap, or
manufacturing receipt remains diagnostic-only.

## Tri-Valued Gates

SeaMeInIt uses a PDA-style tri-valued admissibility discipline:

```text
-1 reject
 0 diagnostic / risky / unknown
+1 admissible
```

The Agda surface names these:

```text
gateReject
gateDiagnostic
gateAdmissible
```

The strict promotion rule is conservative:

```text
promotedArtifact iff every required gate is gateAdmissible
```

Any reject or diagnostic gate keeps the artifact in:

```text
diagnosticOnly
```

This mirrors the sibling repo's receipt-orchestrator discipline: an
unreceipted object may be useful as a diagnostic, but it is not a promoted
artifact.

## Body Carrier

`BodyCarrier` represents the fitted body surface and its atlas-level context:

```text
vertices
faces
atlas
region masks
forbidden zones
body receipt
```

The carrier is intentionally generic. The Agda module does not import SMPL-X,
mesh files, fitted body assets, Blender output, or scan data. It only records
the typed slot where those receipts must land.

## Kernel Basis

`KernelBasis` is the body-attached field basis. The SeaMeInIt documents
describe a fixed basis such as:

```text
B0 in R^(N x K)
```

where `N` is the body-surface vertex count and `K` is the compressed component
count. The Agda surface records the important admissibility checks:

```text
coefficientLengthMatchesComponents
vertexSetMatchesBody
areaWeightedOrthonormalReceipt
basisReceipt
```

The key invariant is not "this basis is physically true"; it is:

```text
the coefficient vector, basis component count, and body vertex set agree
before downstream fields are interpreted.
```

## ROM Operator

`ROMOperator` treats ROM as a compressed operator over admissible pose or task
space, not as a mesh, a renderer label, or a list of poses.

The intended shape is:

```text
Pose -> CoefficientVector
```

with a derivation stream:

```text
tokens in tri-valued admissibility space
stream -> decode -> pose -> project
```

The stricter seam-derivation reading is:

```text
ROM is an admissible movement-derivation language;
pose coordinates are only one projection of that language.
```

A ROM derivation carries history, coupling debt, load/contact context, and
fabric/seam obligations that a final pose coordinate has already forgotten.
Seam derivation therefore consumes task-weighted accepted derivations, not just
static body poses.

The formal surface includes:

```text
tokenGate
streamGate
decode
validPose
projectPose
encodePose
romReceipt
```

This keeps the ROM lane separate from renderer morphology. A rendered body may
look human, ogre-like, or otherwise distorted; that appearance is not a ROM
invariant unless separately receipted as part of the body carrier and transform
chain.

## Coupling Cocycles And Debts

`CouplingCocycle` records demand/response mismatch and its obligation gate:

```text
demand
response
delta demand response -> debt
obligationProjection debt -> gate
blockingDebt
```

In the sibling SeaMeInIt terms, seam/fabric constraints can add coupling
obligations on top of ROM/PDA obligations. A blocking debt prevents promotion
even if other local artifacts are present.

The important DASHI reading is:

```text
coupling residuals are first-class transport debt
```

not comments on the side of an otherwise promoted solve.

## Projected Fields

Projected fields are typed by:

```text
tension
pressure
shear
support
```

The SeaMeInIt runtime may compute these from real ROM samples, finite
differences, task-weighted aggregation, or fallback synthetic/procedural
inputs. The Agda surface only records:

```text
Task
Fabric
Pose
CoefficientVector
reconstruct coefficient vertex -> projected value
field gate
ROM aggregation receipt
```

So a field is admissible only when its basis, ROM projection, task/fabric
context, and aggregation receipt are aligned.

## Seam Graph, Cuts, And Panels

The seam space is modeled as a graph:

```text
G = (V, E)
S subset E
panels = connected components of G \ S
```

The Agda records expose this as:

```text
SeamGraph
SeamCutPanelization
```

with edge endpoints, edge costs, per-edge seam admissibility, cuts, panels,
cut gates, panel gates, and panel unwrap receipt.

This makes the solver output an admissibility-checked graph artifact. It does
not assert that the selected seam cut is globally optimal, manufacturable, or
safe without the relevant receipts.

## Seam Derivation And Metric Corrections

The seam derivation receipt has the shape:

```text
SeamDerivation = (B, R, F, G, S, P, U, D, A, C)
```

where `B` is the body carrier, `R` is the ROM derivation language, `F` is the
fabric/fabrication carrier, `G` is the projected field basis, `S` is seam
topology, `P` is panel topology, `U` is panel flattening, `D` is the shaping
operator set, `A` is the allowance/manufacturing envelope, and `C` is the
receipt.

The Agda seam surface is:

```text
DASHI.Interop.SeaMeInItSeamDerivationFormalism
```

It records ROM derivation-language carriers, PDA admissibility, ROM coupling
debt, derivation ultrametric witnesses, fabric/fabrication carriers, seam
feedback operators, field-driven seam costs, panel metric residuals, shaping
operators, seam allowance fields, and a finished seam receipt. The solver order
is deliberately one-way: derive a field-driven seam-cost graph, extract panel
topology, flatten panels, then promote shaping operators against remaining
metric residual.

A dart, gusset, ease region, pleat, stretch panel, or split is admissible only
when its residual reduction beats its MDL/manufacturing/accessibility cost and
does not introduce a higher-severity blocker. Seam and shaping operators feed
back into ROM/design admissibility; a layout that blocks an accepted movement
derivation remains diagnostic or rejected.

The atlas bridge is:

```text
DASHI.Interop.SeaMeInItROMSeamAtlas
```

It records the higher-level compiler reading:

```text
body + ROM derivation language + fabric carrier
  -> adaptive seam/panel atlas
  -> pattern serialization
```

The atlas bridge ties the existing ROM kernel surface to an unwrap competitor
run and optional garment pattern receipt. It explicitly records that the unwrap
run does not claim global optimality, true inverse correspondence, or
manufacturing authority. A promoted atlas still depends on the underlying ROM
promotion certificate and all atlas gates clearing.

The executable diagnostic companion is:

```text
scripts/seam_derivation_diagnostic.py
```

It uses a synthetic ellipsoid patch, synthetic reach/twist fields, a toy seam
cost graph, toy panel extraction, toy XY flattening residuals, diagnostic
metric-correction operators, and seam allowances. It proves the JSON receipt
pipeline shape exists, but it does not validate a fitted body, real ROM,
physical fabric mechanics, manufacturing safety, or production pattern export.

## Unwrap Competitor Layer

Unwrap and panel-flattening methods are compared through:

```text
DASHI.Interop.SeaMeInItUnwrapCompetitors
```

The competitor layer is a benchmark/governance surface, not another solver. A
method is not represented merely as a named algorithm. It is represented as:

```text
source carrier
target carrier
map contract
metric witness
UFTC severity report
method family
claim boundary
```

The split Agda surface is:

```text
DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Core
DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Methods
DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Benchmark
DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Obligations
DASHI.Interop.SeaMeInIt.Unwrap.Competitor.GarmentGate
DASHI.Interop.SeaMeInIt.Unwrap.Competitor.ClaimBoundaries
DASHI.Interop.SeaMeInIt.Unwrap.Competitor.ExternalConformance
DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Everything
```

A map contract may expose both a forward chart and an optional pullback, but
the pullback is correspondence-only unless the receipt carries an explicit
roundtrip witness and error bound. Method families constrain what a candidate
may claim: spherical export, scientific grid, spectral basis, mesh
parameterizer, seam/cut optimizer, black-box artist tool, body correspondence
atlas, learned proposal, and DASHI-native atlas methods do not share the same
authority.

The first registered spherical candidates are equirectangular, cylindrical
equal-area, cubed sphere, octahedral mapping, HEALPix, geodesic/icosahedral,
spherical harmonics, HEALPix plus spherical harmonics, and BT369 sphere unwrap.
The first garment and mesh-UV candidates are LSCM, ABF, ARAP, SLIM, BFF,
xatlas, OptCuts, AutoCuts, Ambrosio-Tortorelli, Blender unwrap,
DensePose/SMPL UV, and learned semantic UV proposal methods.

Safe benchmark claim:

```text
best promoted candidate in the declared benchmark slice
```

Unsafe claims:

```text
globally optimal sphere or mesh flattening
sphere-plane isometry
true inverse correspondence
external solver authority without measured receipts
manufacturing safety
SeaMeInIt production promotion
```

Missing optional solvers are represented as unavailable diagnostic competitors,
not as suite failures. External implementations remain measured/conformance
surfaces: tool version, settings hash, input/output hashes, metric receipts,
and claim boundaries are required before they participate in a benchmark slice.
Their absence does not fail the suite, and their presence does not create
internal proof authority.

Executable sphere benchmark:

```text
scripts/sphere_unwrap_benchmark.py
```

The runner emits deterministic JSON receipts across adversarial spherical
fields: constant, linear xyz, low-frequency harmonic, high-frequency harmonic,
polar cap, longitude seam stripe, checkerboard/geodesic patch, localized
Gaussian bump, binary hemisphere, and band-limited mix. It measures
BT369/adaptive, cylindrical equal-area, equirectangular, cubed-sphere, and
octahedral candidates, measures HEALPix only when `healpy` is importable, and
emits unavailable diagnostic receipts for optional external solvers such as
xatlas, SLIM, BFF, OptCuts, and Blender.

The local sandbox smoke run at `12x6` currently reports:

```text
bt369      9 field wins
equal_area 1 field win, on binary_hemisphere
```

HEALPix and xatlas are unavailable diagnostics in this sandbox because their
Python packages are not importable here. The benchmark result is declared
slice evidence only and does not strengthen the Agda claim boundary.

## Compression: Hypervoxels And Hypersheets

The sibling formalism uses compression over pose/task space:

```text
hypervoxel = pose-space region with the same admissibility stack
hypersheet = continuous family of hypervoxels with the same constraint transitions
```

The Agda surface records these as `CompressionCell` values:

```text
kind
poseRegion
admissibilityStack
equivalentUnderStack
boundaryResidual
needsFineGraining
compressionReceipt
```

The intended rule is:

```text
coarse grain where admissibility is stable;
fine grain near boundaries and residual jumps.
```

That is compression without truth-collapse: the model compresses equivalent
admissibility classes, not arbitrary averages over incompatible states.

## Strict Promotion Gate

`SeaMeInItROMKernelSurface` gathers the pipeline and exposes:

```text
carrierGate
basisGate
romGate
couplingGate
seamCostGate
topologyGate
panelizationGate
solverDomainGate
manufacturingReceiptGate
```

For an unwrap competitor benchmark, the corresponding gates are map-contract,
metric-availability, coverage/foldover, residual, seam/cut, solver-domain,
UFTC severity, benchmark-slice, certificate, and claim-boundary gates. Severity
is non-masking: a foldover, invalid inverse claim, manufacturing failure, or
claim-boundary violation cannot be offset by lower distortion or better packing
score. Clearing these gates promotes a candidate only inside its declared
benchmark slice.

The strict promotion state is:

```text
promotionFromGates strictPromotionGates
```

Promotion is possible only when all of these are `gateAdmissible`.

Safe claim:

```text
the DASHI-side surface describes the receipt and promotion structure for
SeaMeInIt ROM/kernel/seam artifacts.
```

Unsafe claims:

```text
the external pipeline is validated by this Agda module
the solver output is physically or clinically safe
the rendered morphology is a ROM invariant
the body fit proves true inverse ROM-domain deformation
the manufacturing artifact is safe without independent manufacturing review
```

## Relation To SeaMeInIt Docs

This module summarizes and types the formalism described across these sibling
repo documents:

```text
../ITIR-suite/SeaMeInIt/README.md
../ITIR-suite/SeaMeInIt/CONTEXT.md
../ITIR-suite/SeaMeInIt/docs/rom_definition.md
../ITIR-suite/SeaMeInIt/docs/rom_levels_spec.md
../ITIR-suite/SeaMeInIt/docs/rom_compression_and_coarse_graining.md
../ITIR-suite/SeaMeInIt/docs/solver_kernel_roadmap_note_20260310.md
../ITIR-suite/SeaMeInIt/docs/seaminit_sprint0.md
../ITIR-suite/SeaMeInIt/docs/receipt_orchestrator.md
../ITIR-suite/SeaMeInIt/docs/seam_pipeline_intended_vs_observed.md
../ITIR-suite/SeaMeInIt/schemas/basis_readme.md
```

It intentionally does not copy implementation logic from the Python pipeline
or claim to execute the solver. The Agda layer is the typed DASHI receipt
surface that keeps carrier, quotient, gate, transport, and promotion
boundaries explicit.
