# Schrodinger Evolution Scope

Status: typed G3 obligation surface; non-promoting.

Agda module:

```text
DASHI/Physics/Closure/SchrodingerEvolutionScope.agda
```

This scope records what is available for a future
`SchrodingerEvolutionTheorem`, or explicitly scoped substitute, and what is
still missing. It does not claim G3.

## Already Inhabited Inputs

The scope imports the current theorem-thin Schrodinger-facing and wave-state
surfaces:

| Field | Source |
|---|---|
| `phaseWaveSchrodingerGap` | `shiftPhaseWaveSchrodingerGap` |
| `phaseWaveAssumedTheorem` | `shiftPhaseWaveSchrodingerAssumedTheorem` |
| `knownLimitsQFTBridge` | `canonicalKnownLimitsQFTBridgeTheorem` |
| `knownLimitsPhysicalWaveState` | `KnownLimitsQFTBridgeTheorem.physicalWaveState` |

These inputs already provide bounded phase-wave packaging, an assumption-guarded
Schrodinger-form witness consumer, and a known-limits physical wave-state
carrier. They do not provide a self-adjoint Hamiltonian, unitary evolution, norm
preservation, a Hamiltonian exponential construction, a non-relativistic
contraction theorem, or a derived Schrodinger equation.

The scope also records the strongest currently inspected supporting surfaces:

| Surface | Source | Boundary |
|---|---|---|
| finite Hamiltonian proxy | `ShiftDiscreteWaveStep.shiftDiscreteWaveStep` | Euler-style `shiftHamiltonian4`, not a self-adjoint operator |
| finite energy behavior | `ShiftDiscreteWaveEnergy.shiftDiscreteWaveEnergy` | held-state preservation plus explicit non-held growth witnesses |
| finite unitary-like behavior | `ShiftUnitaryLikeConstraint.shiftUnitaryLikeConstraint` | basis-level `mulI` norm preservation only |
| offline-L2 evidence | `canonicalP2OfflineL2ObstructionCertificate` | negative below-delta obstruction, not a positive MDL-to-L2 seam theorem |

## Obligation Fields

The Hamiltonian/evolution surface is grouped under
`G3HamiltonianEvolutionObligations`:

| Obligation field | Purpose |
|---|---|
| `SpineCarrier` | canonical spine carrier used to construct the lane |
| `WaveStateCarrier` | wave-state carrier for the G3 lane |
| `HamiltonianOperatorCarrier` | carrier for a Hamiltonian operator or scoped substitute |
| `TimeCarrier` | time parameter carrier |
| `EvolutionOperatorCarrier` | carrier for Hamiltonian-generated evolution |
| `InnerProductCarrier` | carrier for norm/inner-product preservation |
| `HamiltonianDomainCarrier` | analytic/admissible domain for the Hamiltonian |
| `DomainAdmissibilityCarrier` | evidence carrier for domain admissibility |
| `KatoRellichRouteCarrier` | Kato-Rellich route evidence for self-adjointness |
| `StoneTheoremRouteCarrier` | Stone theorem route evidence for unitary-group generation |
| `ExponentialCarrier` | carrier for the formal `exp(-iHt)` construction |
| `PoincareSectorCarrier` | spine/Poincare sector to be contracted |
| `NonRelativisticLimitCarrier` | target non-relativistic limit carrier |
| `ContractionCarrier` | Inonu-Wigner/contraction evidence carrier |
| `GalileiSectorCarrier` | Galilei-sector target carrier for the Poincare contraction |
| `PoincareToGalileiContractionCarrier` | evidence carrier for the Poincare-to-Galilei contraction |
| `GalileiHamiltonianCompatibilityCarrier` | evidence carrier connecting the Galilei limit to Hamiltonian form |
| `CCRCompatibilityCarrier` | CCR compatibility evidence for the Galilei/Hamiltonian route |
| `EquationCarrier` | carrier for the Schrodinger equation consumer |
| `MDLFiniteCarrier` | finite MDL-side wave-state carrier |
| `L2ContinuumCarrier` | analytic L2/continuum-side wave-state carrier |
| `MDLToL2SeamCarrier` | evidence carrier for finite-MDL to L2 transport |
| `hamiltonianFromSpine` | construct Hamiltonian operator from the spine |
| `poincareSectorFromSpine` | extract the Poincare-sector candidate from the spine |
| `waveStateFromKnownLimits` | adapt the known-limits wave state into G3 |
| `hamiltonianDomain` | assign a candidate domain to the Hamiltonian |
| `domainAdmissibilityLaw` | law making the domain usable for self-adjointness |
| `selfAdjointnessDomainEvidence` | evidence object for the chosen domain |
| `domainIsAdmissible` | proof obligation for domain admissibility |
| `katoRellichRouteForHamiltonian` | Kato-Rellich candidate for the spine-derived Hamiltonian |
| `katoRellichRouteDerived` | proof obligation for the Kato-Rellich route |
| `evolutionFromHamiltonian` | build evolution from Hamiltonian and time |
| `exponentialFromHamiltonian` | build the exponential `exp(-iHt)` carrier |
| `exponentialGeneratesEvolution` | law tying the exponential to the evolution operator |
| `evolutionGeneratedByExponential` | proof obligation for exponential generation |
| `applyEvolution` | apply evolution to wave states |
| `selfAdjointOrScopedSubstitute` | self-adjointness or explicitly bounded substitute |
| `stoneTheoremUnitaryGroupRoute` | Stone theorem candidate from self-adjoint Hamiltonian to unitary group |
| `stoneTheoremRouteDerived` | proof obligation for the Stone theorem route |
| `unitaryEvolutionLaw` | law asserting unitary evolution |
| `normPreservationLaw` | law asserting inner-product/norm preservation |
| `schrodingerEquation` | Schrodinger-equation carrier construction |
| `schrodingerEquationLaw` | law for the equation carrier |
| `nonRelativisticLimit` | map the Poincare sector to the non-relativistic limit |
| `galileiSectorFromNonRelativisticLimit` | extract the Galilei target from the non-relativistic limit |
| `contractionToHamiltonianForm` | contraction candidate producing Hamiltonian form |
| `contractionLaw` | law for the contraction evidence carrier |
| `inonuWignerContractionDerived` | proof obligation for the contraction route |
| `poincareToGalileiContraction` | Poincare-to-Galilei contraction candidate |
| `poincareToGalileiContractionLaw` | law for the Poincare-to-Galilei evidence carrier |
| `poincareToGalileiContractionDerived` | exact missing contraction theorem field |
| `galileiHamiltonianCompatibility` | Galilei/Hamiltonian compatibility candidate |
| `galileiHamiltonianCompatibilityDerived` | exact missing Hamiltonian compatibility theorem field |
| `ccrCompatibilityForGalileiHamiltonian` | CCR compatibility candidate for the Galilei/Hamiltonian route |
| `ccrCompatibilityDerived` | exact missing CCR compatibility theorem field |
| `finiteMDLState` | finite MDL-side extraction from wave states |
| `l2ContinuumState` | L2/continuum-side extraction from wave states |
| `mdlToL2Seam` | finite-MDL to L2 seam candidate |
| `mdlToL2SeamDerived` | exact missing positive seam theorem field |

## Exact Four-Field Typed Obstruction

The scope now also records an inhabited
`G3SchrodingerFourFieldTypedObstruction`. This object does not contain theorem
proofs. It carries the exact upstream theorem types that would inhabit the four
inspected derived fields:

| Missing field | Exact upstream type alias |
|---|---|
| `poincareToGalileiContractionDerived` | `PoincareToGalileiContractionDerivedType obligationSchrodingerHamiltonianEvolutionFields` |
| `galileiHamiltonianCompatibilityDerived` | `GalileiHamiltonianCompatibilityDerivedType obligationSchrodingerHamiltonianEvolutionFields` |
| `ccrCompatibilityDerived` | `CCRCompatibilityDerivedType obligationSchrodingerHamiltonianEvolutionFields` |
| `mdlToL2SeamDerived` | `MDLToL2SeamDerivedType obligationSchrodingerHamiltonianEvolutionFields` |

No inspected local surface inhabits these theorem types. The type aliases are
computed from `G3HamiltonianEvolutionObligations`, so a future implementation
must prove the same dependent targets as the corresponding record fields. The
typed obstruction includes `refl` exactness witnesses tying each stored type to
the corresponding alias; it does not add any new postulate or theorem witness.

The root Poincare-to-Galilei carrier-level gap is also recorded separately as
`G3PoincareToGalileiCarrierLevelObstruction`. Its canonical inhabitant stores
only exact carrier/type equalities for:

- `PoincareSectorCarrier`;
- `NonRelativisticLimitCarrier`;
- `GalileiSectorCarrier`;
- `PoincareToGalileiContractionCarrier`;
- `SpineCarrier -> PoincareSectorCarrier`;
- `PoincareSectorCarrier -> NonRelativisticLimitCarrier`;
- `NonRelativisticLimitCarrier -> GalileiSectorCarrier`;
- `PoincareSectorCarrier -> GalileiSectorCarrier -> PoincareToGalileiContractionCarrier`;
- `PoincareToGalileiContractionDerivedType obligationSchrodingerHamiltonianEvolutionFields`.

This is the exact upstream theorem/type missing before the four-field chain can
advance. It does not construct `poincareToGalileiContractionDerived`.

The intended theorem path is:

```text
spine/Poincare sector
  -> Inonu-Wigner or scoped non-relativistic contraction
  -> Poincare-to-Galilei contraction and Galilei/Hamiltonian compatibility
  -> Hamiltonian form
  -> CCR compatibility for the Galilei/Hamiltonian route
  -> admissible self-adjointness domain
  -> Kato-Rellich self-adjointness route
  -> Stone theorem unitary-group route
  -> exponential evolution exp(-iHt)
  -> unitary evolution
  -> norm preservation
  -> positive finite-MDL to analytic-L2 seam
  -> Schrodinger equation derivation
```

The module records this path as obligations only. It does not assert that the
Poincare sector has been extracted from the spine, that the contraction is
proved, or that the resulting Hamiltonian is self-adjoint.

Spine preservation is separate under
`G3SchrodingerSpinePreservationObligations`:

| Obligation field | Purpose |
|---|---|
| `SpineCarrier` | canonical spine carrier for section comparison |
| `SchrodingerLaneCarrier` | Schrodinger lane carrier |
| `embedSchrodingerInSpine` | Schrodinger lane embedding into the spine |
| `recoverSchrodingerFromSpine` | recovery from spine to Schrodinger lane |
| `schrodingerSpineSection` | section proof needed by the G6 `section-QM` gate |

## Postulate Boundary

The Agda file has two postulates, both explicitly named as obligations:

```text
obligationSchrodingerHamiltonianEvolutionFields
obligationSchrodingerSpinePreservationFields
```

They are not theorem witnesses. They keep the surface typed while making the
missing proof obligations explicit.

## Obstruction Status

The obstruction certificates are dependency certificates, not negation proofs:

```text
firstMissingObligationOnlyNoNegation
```

The named blockers are:

- `missingHamiltonianFromSpine`;
- `missingSelfAdjointnessOrScopedSubstitute`;
- `missingSelfAdjointnessDomain`;
- `missingKatoRellichHamiltonianRoute`;
- `missingStoneTheoremUnitaryGroupRoute`;
- `missingUnitaryEvolution`;
- `missingExponentialEvolutionConstruction`;
- `missingNormPreservation`;
- `missingSchrodingerEquationDerivation`;
- `missingInonuWignerNonRelativisticContraction`;
- `missingPoincareToGalileiContraction`;
- `missingGalileiHamiltonianCompatibility`;
- `missingCCRCompatibilityForGalileiHamiltonian`;
- `missingMDLToL2Seam`;
- `missingMDLToL2PositiveTheorem`;
- `missingSchrodingerSpinePreservationSection`.

A real obstruction would require a concrete failed Schrodinger lane candidate.
This scope only records the first missing typed obligations.

## No-Promotion Boundary

`canonicalSchrodingerEvolutionScope` records:

- no `SchrodingerEvolutionTheorem` is constructed;
- no upgrade beyond `SchrodingerGap` or `SchrodingerAssumedTheorem` supplied
  witness packaging is claimed;
- Hamiltonian-from-spine, self-adjointness/scoped substitute,
  self-adjointness domain, Kato-Rellich route, Stone theorem route, exponential
  evolution, unitary evolution, norm preservation, equation derivation,
  Inonu-Wigner contraction, Poincare-to-Galilei contraction,
  Galilei/Hamiltonian compatibility, CCR compatibility, MDL-to-L2 seam, and
  spine preservation remain obligations;
- G6 `section-QM` remains unsatisfied.

## MDL-to-L2 Theorem Surface

`G3SchrodingerMDLToL2SeamTheoremSurface` names the seam theorem target without
promoting it. The exact missing field on the typed obligation record is
`mdlToL2SeamDerived`. The exact positive theorem still missing is a theorem
transporting finite MDL wave-state control to the analytic L2/continuum carrier.

The only inspected L2 support is
`CanonicalP2OfflineL2ObstructionCertificate`, which is negative evidence for a
below-delta candidate family. It cannot inhabit the positive MDL-to-L2 seam.
