# G3 Poincare-Galilei Carrier Chain

Status: carrier-chain obligation surface; non-promoting.

Agda module:

```text
DASHI/Physics/Closure/G3PoincareGalileiCarrierChain.agda
```

This surface records the smallest reusable G3 carrier chain needed by the
Schrodinger lane:

```text
PoincareSectorCarrier
  -> NonRelativisticLimitCarrier
  -> GalileiSectorCarrier
  -> PoincareToGalileiContractionCarrier
```

The chain is a record over the existing
`G3HamiltonianEvolutionObligations` fields from
`SchrodingerEvolutionScope.agda`. It does not construct a Poincare sector, a
non-relativistic limit, a Galilei sector, or a contraction theorem. It only
records the exact carrier and map types already required by the Schrodinger
obligation surface.

Continuation layer `2026-05-13`: the module now owns an independent
`PoincareSectorCarrier` record shape instead of only pointing at the
Schrodinger obligation field. The record is deliberately structural:

- `PoincareState`;
- `CarrierOperator` and its action on `PoincareState`;
- a CCR-shaped operator surface using `DASHI.Algebra.CCR.Op`;
- a CCR-shaped commutator surface using `DASHI.Algebra.CCR._commutator_`;
- `MetricCarrier` and a metric map on the Poincare state carrier;
- translation and Lorentz generator index carriers;
- maps from generator indices into `CarrierOperator`;
- Set-valued slots for translation/translation, Lorentz/translation, and
  Lorentz/Lorentz Poincare bracket relations.

This is not yet an inhabited Poincare algebra. The new obligation surface names
the missing concrete `CarrierOperator`, commutator-closure proof, metric /
Lorentz-signature witness, and Poincare relation proofs. Those pieces must be
supplied before the layer may promote from a carrier record shape to a real
Poincare-sector witness.

IW / associated-graded continuation `2026-05-13`: inspection did not find a
repo-native filtration, associated graded carrier, inhabited Poincare/Galilei
carrier algebra, filtered-bracket descent law, contraction-parameter law, or
`p2`-indexed Poincare isomorphism. The module therefore adds
`G3IWAssociatedGradedObligationSurface` instead of promoting an IW theorem. Its
canonical inhabitant names the missing filtration, associated graded, carrier
algebra, filtered bracket compatibility, contraction parameter law,
Poincare-at-`p2` carrier/isomorphism, and Galilei associated-graded
identification.

MDL density continuation `2026-05-13`: finite density support is real but
finite only. `G3MDLDensityToL2ObligationSurface` records the inhabited
`shiftPhaseWaveDensityMonotone` and `shiftPointDensityMonotone` laws from the
phase-wave and shift carriers, and also stores
`canonicalP2OfflineL2ObstructionCertificate` as negative offline-L2 evidence.
It does not turn those finite witnesses into an analytic L2 density theorem.
The required positive seam remains the exact
`MDLToL2SeamDerivedType obligationSchrodingerHamiltonianEvolutionFields`
obligation, with missing finite-to-L2 density map, L2 density carrier,
measurability/integrability or scoped substitute, and MDL-density-to-L2 control
law.

The module also stores a `DASHIState`-compatible state marker for Markov/DASHI
consumers. That state names the current node as the contraction-carrier boundary
and marks the residual obligation as the missing Poincare-to-Galilei derived
theorem. It is a state surface only, not a stochastic Markov chain and not a
promotion receipt.

The exact theorem obligation exposed for later `SchrodingerEvolutionScope`
consumption is:

```text
PoincareToGalileiContractionDerivedType obligations
```

For the canonical Schrodinger obligation postulate, this specializes to:

```text
PoincareToGalileiContractionDerivedType
  obligationSchrodingerHamiltonianEvolutionFields
```

No `poincareToGalileiContractionDerived` field is inhabited here.
