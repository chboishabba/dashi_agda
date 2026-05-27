# SeaMeInIt ROM kernel formalism

## Intention

This note records the DASHI-side formalism for the SeaMeInIt ROM/kernel/seam
lane found in the sibling repo `../ITIR-suite/SeaMeInIt`.

Agda module:

```text
DASHI.Interop.SeaMeInItROMKernelFormalism
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
