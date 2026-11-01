# Penrose Local-Global Hyperfabric Cross-Pollination Design

## Scope

This design adds a thin Interop bridge across already-owned theorem surfaces. It does **not** introduce a new local/global kernel, topology library, Pareto order, graph-colouring ontology, or Penrose theorem implementation.

The bridge must reuse:

- `DASHI.Reasoning.LocalFibreHyperfabricExact` for local stalk/restriction/global-section compatibility;
- `DASHI.Core.NDimParetoHyperfabricExact` for projection asymmetry and omitted-coordinate non-promotion;
- `DASHI.Combinatorics.GraphColouringRecolourPantsSnowballExact` for local recolour -> boundary restriction -> seam compatibility -> recursive gluing -> global colouring;
- the stacked Penrose owners from #908 for local focusing, horismos causal-boundary semantics, compactness payment, global causality authority, and the compact/noncompact same-object reductio.

The implementation branch is intentionally stacked on #908 because these Penrose owners are not yet on `master`.

## Goal

Make one reusable structural observation executable without equating domains:

```text
local witness
  -> boundary / restriction
  -> compatibility
  -> global object
  -> projection
  -> global obstruction or admissibility conclusion
```

The bridge records **proof-architecture correspondence**, not theorem identity.

## Proposed owner

Create:

`DASHI/Interop/PenroseLocalGlobalHyperfabricCrossPollinationExact.agda`

The owner should contain only adapters/receipts over existing owners.

### Structural roles

Define a small role vocabulary sufficient to state the correspondence:

- local witness;
- boundary restriction;
- compatibility/seam condition;
- global compatible object;
- projection/reduction;
- global obstruction;
- reductio conclusion.

The role vocabulary is descriptive. It must not replace domain-specific types.

### Penrose adapter

Map, without identification:

- trapped surface / local null expansion and focusing -> local witness;
- null generator remaining on `E+(T)` -> boundary/compatibility condition;
- `E+(T)` -> global causal object;
- timelike-flow projection to a Cauchy surface -> projection;
- compactness vs noncompactness of the **same** `E+(T)` -> global obstruction;
- discharge of assumed null completeness -> reductio conclusion.

The same-object invariant must be retained explicitly.

### Graph-colouring adapter

Reuse the existing sequence:

- local recolour move;
- boundary restriction;
- pants seam compatibility;
- recursive gluing compatibility;
- global colouring.

The adapter must preserve the existing boundary that local recolouring does not imply global seam/gluing compatibility.

### Local-fibre / hyperfabric adapter

Reuse:

- local stalk / selected local carrier;
- `restrict`;
- `GlobalSection.compatible`;
- global section.

The bridge must not identify a Penrose horismos with a hyperfabric global section. The correspondence is only between dependency roles.

### NDim projection adapter

Reuse the asymmetric rule from `NDimParetoHyperfabricExact`:

```text
full information -> projected information
```

while preserving:

```text
projected result -/-> full result automatically.
```

This is the cross-domain donor for the Penrose Cauchy-projection firewall: a valid projection step does not make the projection a sufficient replacement for the source object.

## Mandatory WrongType firewalls

The bridge must expose exact negative boundaries equivalent to:

1. `localValidityDoesNotImplyGlobalValidity`
2. `projectionValidityDoesNotImplySourceSufficiency`
3. `boundedLocalCarrierDoesNotImplyGlobalCompactnessOrClosure`
4. `sharedProofArchitectureDoesNotIdentifyDomainTheorems`

Additional required distinctions:

- Penrose causal projection is not a Pareto axis projection;
- `E+(T)` is not a hyperfabric `GlobalSection`;
- graph-colouring seam compatibility is not Lorentzian causal compatibility;
- compact/noncompact same-object reductio is an obstruction architecture, not a generic contradiction generated merely by having two domains.

## Constructive vs obstruction duality

The bridge should make explicit one useful duality:

### Constructive gluing

```text
local candidates
  -> restriction
  -> compatibility filter
  -> globally admissible family/object
```

This is exemplified by graph colouring, LocalFibre/GlobalSection, and later RSA/NDim compatible reducer families.

### Obstruction / reductio

```text
local dynamics
  -> global property P of object X

global topology / external constraint
  -> incompatible property not-P of the same object X

therefore discharge the reductio assumption
```

Penrose is the first adapter for this obstruction form.

The owner must not claim these two forms are equivalent; it only records that they are dual local-to-global dependency patterns.

## First implementation tranche

The first tranche is deliberately limited to:

1. one Interop owner;
2. one focused structural checker or regression owner requiring the role adapters and WrongType firewalls;
3. import into an appropriate Interop/reasoning aggregate only if a canonical aggregate already exists;
4. no changes to canonical domain kernels.

Do not cross-pollinate RSA, Fly/MaleCNS, SensibLaw, or Navier-Stokes in this first implementation. Those are downstream consumers after the bridge itself is stable.

## Testing / proof-debt discipline

TDD order:

1. add the focused structural requirement first;
2. verify the new Interop owner is absent / requirement is RED;
3. add the minimal owner;
4. add exact regressions for the four WrongType firewalls and same-object preservation;
5. do not claim Agda kernel success without a fresh receipt.

CI availability is explicitly out of scope for this tranche at the user's request. Missing CI does not authorize a kernel-success claim.

## Non-goals

This design does not:

- prove Penrose's theorem internally;
- prove graph-colouring theorems;
- identify local fibre charts with spacetime geometry;
- scalarize NDim/Pareto structure;
- make a universal category of all local-to-global proofs;
- create a new planner or roadmap ontology;
- promote an analogy into physical, mathematical, legal, or biological identity.

## Promotion boundary

The intended promotion is only:

```text
several existing DASHI domains instantiate a shared dependency shape
```

The prohibited promotion is:

```text
shared dependency shape => same theorem / same semantics / same domain object.
```
