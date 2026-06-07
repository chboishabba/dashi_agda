module DASHI.Physics.Closure.NSSprint109SmoothCompactSupportWitness where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint108RadialBumpFunctionConstruction
  as Sprint108

------------------------------------------------------------------------
-- Sprint 109 smooth compact-support witness decomposition.
--
-- Sprint 108 recorded SmoothCompactSupportWitness as the first open
-- subgate of RadialBumpFunctionConstruction.  Sprint 109 records the five
-- concrete obligations needed for that smooth compact-support witness.
-- The decomposition ledger closes; every analytic subgate, the parent
-- radial bump construction, the dyadic partition chain, and every
-- downstream Navier-Stokes Clay flag remains fail-closed.

smoothCompactSupportWitnessDecompositionLedgerClosed : Bool
smoothCompactSupportWitnessDecompositionLedgerClosed = true

baseExpSmoothFunctionClosed : Bool
baseExpSmoothFunctionClosed = false

boundaryFlatnessAtUnitRadiusClosed : Bool
boundaryFlatnessAtUnitRadiusClosed = false

compactSupportCutoffDefinitionClosed : Bool
compactSupportCutoffDefinitionClosed = false

smoothnessAcrossSupportBoundaryClosed : Bool
smoothnessAcrossSupportBoundaryClosed = false

nonCircularCompactSupportSourceClosed : Bool
nonCircularCompactSupportSourceClosed = false

smoothCompactSupportWitnessClosed : Bool
smoothCompactSupportWitnessClosed = false

radialBumpFunctionConstructionClosed : Bool
radialBumpFunctionConstructionClosed = false

smoothDyadicCutoffPartitionClosed : Bool
smoothDyadicCutoffPartitionClosed = false

littlewoodPaleyShellProjectorClosed : Bool
littlewoodPaleyShellProjectorClosed = false

dyadicShellEnergyDensityClosed : Bool
dyadicShellEnergyDensityClosed = false

highFrequencyConcentrationMeasureClosed : Bool
highFrequencyConcentrationMeasureClosed = false

strainCompressionAtHighFrequencyConcentrationPointsClosed : Bool
strainCompressionAtHighFrequencyConcentrationPointsClosed = false

signedLowModeFluxLowerBoundClosed : Bool
signedLowModeFluxLowerBoundClosed = false

timeIntegratedFluxSurplusClosed : Bool
timeIntegratedFluxSurplusClosed = false

finiteKStarCollapseClosed : Bool
finiteKStarCollapseClosed = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

failClosedSmoothCompactSupportWitnessDecomposition : Bool
failClosedSmoothCompactSupportWitnessDecomposition = true

data BaseExpSmoothFunction : Set where
  BaseExpSmoothFunctionOpen :
    BaseExpSmoothFunction

data BoundaryFlatnessAtUnitRadius : Set where
  BoundaryFlatnessAtUnitRadiusOpen :
    BoundaryFlatnessAtUnitRadius

data CompactSupportCutoffDefinition : Set where
  CompactSupportCutoffDefinitionOpen :
    CompactSupportCutoffDefinition

data SmoothnessAcrossSupportBoundary : Set where
  SmoothnessAcrossSupportBoundaryOpen :
    SmoothnessAcrossSupportBoundary

data NonCircularCompactSupportSource : Set where
  NonCircularCompactSupportSourceOpen :
    NonCircularCompactSupportSource

data SmoothCompactSupportWitnessDecomposition : Set where
  SmoothCompactSupportWitnessSplitsIntoFiveSubgates :
    SmoothCompactSupportWitnessDecomposition

record Sprint108SmoothCompactSupportWitnessAnchor : Set where
  constructor sprint108SmoothCompactSupportWitnessAnchorReceipt
  field
    sprint108Receipt :
      Sprint108.NSSprint108RadialBumpFunctionConstruction
    sprint108ReceiptIsCanonical :
      sprint108Receipt
      ≡ Sprint108.canonicalNSSprint108RadialBumpFunctionConstruction
    sprint108SmoothCompactSupportWitness :
      Sprint108.SmoothCompactSupportWitness
    sprint108SmoothCompactSupportWitnessIsCanonical :
      sprint108SmoothCompactSupportWitness
      ≡ Sprint108.SmoothCompactSupportWitnessOpen
    sprint108DecompositionLedgerClosed :
      Sprint108.radialBumpFunctionConstructionDecompositionLedgerClosed
      ≡ true
    sprint108SmoothCompactSupportWitnessStillFalse :
      Sprint108.smoothCompactSupportWitnessClosed ≡ false
    sprint108RadialBumpFunctionConstructionStillFalse :
      Sprint108.radialBumpFunctionConstructionClosed ≡ false
    sprint108ClayPromotionStillFalse :
      Sprint108.clayNavierStokesPromoted ≡ false

open Sprint108SmoothCompactSupportWitnessAnchor public

canonicalSprint108SmoothCompactSupportWitnessAnchor :
  Sprint108SmoothCompactSupportWitnessAnchor
canonicalSprint108SmoothCompactSupportWitnessAnchor =
  sprint108SmoothCompactSupportWitnessAnchorReceipt
    Sprint108.canonicalNSSprint108RadialBumpFunctionConstruction
    refl
    Sprint108.SmoothCompactSupportWitnessOpen
    refl
    refl
    refl
    refl
    refl

record SmoothCompactSupportWitnessSubgateStatus (Gate : Set) : Set where
  constructor smoothCompactSupportWitnessSubgateStatusReceipt
  field
    gate :
      Gate
    gateClosed :
      Bool
    gateClosedIsFalse :
      gateClosed ≡ false
    note :
      String

open SmoothCompactSupportWitnessSubgateStatus public

canonicalBaseExpSmoothFunctionStatus :
  SmoothCompactSupportWitnessSubgateStatus BaseExpSmoothFunction
canonicalBaseExpSmoothFunctionStatus =
  smoothCompactSupportWitnessSubgateStatusReceipt
    BaseExpSmoothFunctionOpen
    false
    refl
    "Requires an explicit exp-based smooth seed and derivative control before the compact-support witness can close."

canonicalBoundaryFlatnessAtUnitRadiusStatus :
  SmoothCompactSupportWitnessSubgateStatus BoundaryFlatnessAtUnitRadius
canonicalBoundaryFlatnessAtUnitRadiusStatus =
  smoothCompactSupportWitnessSubgateStatusReceipt
    BoundaryFlatnessAtUnitRadiusOpen
    false
    refl
    "Requires proof that all boundary jets vanish at unit radius for the selected seed."

canonicalCompactSupportCutoffDefinitionStatus :
  SmoothCompactSupportWitnessSubgateStatus CompactSupportCutoffDefinition
canonicalCompactSupportCutoffDefinitionStatus =
  smoothCompactSupportWitnessSubgateStatusReceipt
    CompactSupportCutoffDefinitionOpen
    false
    refl
    "Requires a concrete cutoff definition with interior activity and exterior zero support behavior."

canonicalSmoothnessAcrossSupportBoundaryStatus :
  SmoothCompactSupportWitnessSubgateStatus SmoothnessAcrossSupportBoundary
canonicalSmoothnessAcrossSupportBoundaryStatus =
  smoothCompactSupportWitnessSubgateStatusReceipt
    SmoothnessAcrossSupportBoundaryOpen
    false
    refl
    "Requires a proof that the cutoff glues smoothly across the support boundary."

canonicalNonCircularCompactSupportSourceStatus :
  SmoothCompactSupportWitnessSubgateStatus NonCircularCompactSupportSource
canonicalNonCircularCompactSupportSourceStatus =
  smoothCompactSupportWitnessSubgateStatusReceipt
    NonCircularCompactSupportSourceOpen
    false
    refl
    "Requires an explicit non-circular source for compact support so the witness does not import a circular radial assumption."

record SmoothCompactSupportWitnessDecompositionStatus : Set where
  constructor smoothCompactSupportWitnessDecompositionStatusReceipt
  field
    decomposition :
      SmoothCompactSupportWitnessDecomposition
    decompositionClosed :
      Bool
    decompositionClosedIsTrue :
      decompositionClosed ≡ true
    baseExpSmoothFunction :
      BaseExpSmoothFunction
    baseExpSmoothFunctionIsCanonical :
      baseExpSmoothFunction ≡ BaseExpSmoothFunctionOpen
    boundaryFlatnessAtUnitRadius :
      BoundaryFlatnessAtUnitRadius
    boundaryFlatnessAtUnitRadiusIsCanonical :
      boundaryFlatnessAtUnitRadius ≡ BoundaryFlatnessAtUnitRadiusOpen
    compactSupportCutoffDefinition :
      CompactSupportCutoffDefinition
    compactSupportCutoffDefinitionIsCanonical :
      compactSupportCutoffDefinition ≡ CompactSupportCutoffDefinitionOpen
    smoothnessAcrossSupportBoundary :
      SmoothnessAcrossSupportBoundary
    smoothnessAcrossSupportBoundaryIsCanonical :
      smoothnessAcrossSupportBoundary ≡ SmoothnessAcrossSupportBoundaryOpen
    nonCircularCompactSupportSource :
      NonCircularCompactSupportSource
    nonCircularCompactSupportSourceIsCanonical :
      nonCircularCompactSupportSource ≡ NonCircularCompactSupportSourceOpen
    sprint108Gate :
      Sprint108.SmoothCompactSupportWitness
    sprint108GateIsCanonical :
      sprint108Gate ≡ Sprint108.SmoothCompactSupportWitnessOpen
    sprint108GateClosed :
      Bool
    sprint108GateClosedIsFalse :
      sprint108GateClosed ≡ false
    note :
      String

open SmoothCompactSupportWitnessDecompositionStatus public

canonicalSmoothCompactSupportWitnessDecompositionStatus :
  SmoothCompactSupportWitnessDecompositionStatus
canonicalSmoothCompactSupportWitnessDecompositionStatus =
  smoothCompactSupportWitnessDecompositionStatusReceipt
    SmoothCompactSupportWitnessSplitsIntoFiveSubgates
    true
    refl
    BaseExpSmoothFunctionOpen
    refl
    BoundaryFlatnessAtUnitRadiusOpen
    refl
    CompactSupportCutoffDefinitionOpen
    refl
    SmoothnessAcrossSupportBoundaryOpen
    refl
    NonCircularCompactSupportSourceOpen
    refl
    Sprint108.SmoothCompactSupportWitnessOpen
    refl
    false
    refl
    "Sprint 109 decomposes the Sprint 108 smooth compact-support witness gate into five obligations without closing them."

requiredSmoothCompactSupportWitnessSubgates :
  List String
requiredSmoothCompactSupportWitnessSubgates =
  "BaseExpSmoothFunction"
  ∷ "BoundaryFlatnessAtUnitRadius"
  ∷ "CompactSupportCutoffDefinition"
  ∷ "SmoothnessAcrossSupportBoundary"
  ∷ "NonCircularCompactSupportSource"
  ∷ []

record SmoothCompactSupportWitnessFlags : Set where
  constructor smoothCompactSupportWitnessFlagsReceipt
  field
    smoothCompactSupportWitnessDecompositionLedgerClosedFlag :
      smoothCompactSupportWitnessDecompositionLedgerClosed ≡ true
    baseExpSmoothFunctionClosedFlag :
      baseExpSmoothFunctionClosed ≡ false
    boundaryFlatnessAtUnitRadiusClosedFlag :
      boundaryFlatnessAtUnitRadiusClosed ≡ false
    compactSupportCutoffDefinitionClosedFlag :
      compactSupportCutoffDefinitionClosed ≡ false
    smoothnessAcrossSupportBoundaryClosedFlag :
      smoothnessAcrossSupportBoundaryClosed ≡ false
    nonCircularCompactSupportSourceClosedFlag :
      nonCircularCompactSupportSourceClosed ≡ false
    smoothCompactSupportWitnessClosedFlag :
      smoothCompactSupportWitnessClosed ≡ false
    radialBumpFunctionConstructionClosedFlag :
      radialBumpFunctionConstructionClosed ≡ false
    smoothDyadicCutoffPartitionClosedFlag :
      smoothDyadicCutoffPartitionClosed ≡ false
    littlewoodPaleyShellProjectorClosedFlag :
      littlewoodPaleyShellProjectorClosed ≡ false
    dyadicShellEnergyDensityClosedFlag :
      dyadicShellEnergyDensityClosed ≡ false
    highFrequencyConcentrationMeasureClosedFlag :
      highFrequencyConcentrationMeasureClosed ≡ false
    strainCompressionAtHighFrequencyConcentrationPointsClosedFlag :
      strainCompressionAtHighFrequencyConcentrationPointsClosed ≡ false
    signedLowModeFluxLowerBoundClosedFlag :
      signedLowModeFluxLowerBoundClosed ≡ false
    timeIntegratedFluxSurplusClosedFlag :
      timeIntegratedFluxSurplusClosed ≡ false
    finiteKStarCollapseClosedFlag :
      finiteKStarCollapseClosed ≡ false
    clayNavierStokesPromotedFlag :
      clayNavierStokesPromoted ≡ false
    failClosedSmoothCompactSupportWitnessDecompositionFlag :
      failClosedSmoothCompactSupportWitnessDecomposition ≡ true

open SmoothCompactSupportWitnessFlags public

canonicalSmoothCompactSupportWitnessFlags :
  SmoothCompactSupportWitnessFlags
canonicalSmoothCompactSupportWitnessFlags =
  smoothCompactSupportWitnessFlagsReceipt
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

record NSSprint109SmoothCompactSupportWitness : Set where
  constructor nsSprint109SmoothCompactSupportWitnessReceipt
  field
    sprint108Anchor :
      Sprint108SmoothCompactSupportWitnessAnchor
    sprint108AnchorIsCanonical :
      sprint108Anchor ≡ canonicalSprint108SmoothCompactSupportWitnessAnchor
    baseExpSmoothFunctionStatus :
      SmoothCompactSupportWitnessSubgateStatus BaseExpSmoothFunction
    baseExpSmoothFunctionStatusIsCanonical :
      baseExpSmoothFunctionStatus
      ≡ canonicalBaseExpSmoothFunctionStatus
    boundaryFlatnessAtUnitRadiusStatus :
      SmoothCompactSupportWitnessSubgateStatus BoundaryFlatnessAtUnitRadius
    boundaryFlatnessAtUnitRadiusStatusIsCanonical :
      boundaryFlatnessAtUnitRadiusStatus
      ≡ canonicalBoundaryFlatnessAtUnitRadiusStatus
    compactSupportCutoffDefinitionStatus :
      SmoothCompactSupportWitnessSubgateStatus CompactSupportCutoffDefinition
    compactSupportCutoffDefinitionStatusIsCanonical :
      compactSupportCutoffDefinitionStatus
      ≡ canonicalCompactSupportCutoffDefinitionStatus
    smoothnessAcrossSupportBoundaryStatus :
      SmoothCompactSupportWitnessSubgateStatus SmoothnessAcrossSupportBoundary
    smoothnessAcrossSupportBoundaryStatusIsCanonical :
      smoothnessAcrossSupportBoundaryStatus
      ≡ canonicalSmoothnessAcrossSupportBoundaryStatus
    nonCircularCompactSupportSourceStatus :
      SmoothCompactSupportWitnessSubgateStatus NonCircularCompactSupportSource
    nonCircularCompactSupportSourceStatusIsCanonical :
      nonCircularCompactSupportSourceStatus
      ≡ canonicalNonCircularCompactSupportSourceStatus
    decompositionStatus :
      SmoothCompactSupportWitnessDecompositionStatus
    decompositionStatusIsCanonical :
      decompositionStatus
      ≡ canonicalSmoothCompactSupportWitnessDecompositionStatus
    flags :
      SmoothCompactSupportWitnessFlags
    flagsAreCanonical :
      flags ≡ canonicalSmoothCompactSupportWitnessFlags
    requiredSubgates :
      List String
    requiredSubgatesAreCanonical :
      requiredSubgates ≡ requiredSmoothCompactSupportWitnessSubgates
    noClayClaim :
      String

open NSSprint109SmoothCompactSupportWitness public

canonicalNSSprint109SmoothCompactSupportWitness :
  NSSprint109SmoothCompactSupportWitness
canonicalNSSprint109SmoothCompactSupportWitness =
  nsSprint109SmoothCompactSupportWitnessReceipt
    canonicalSprint108SmoothCompactSupportWitnessAnchor
    refl
    canonicalBaseExpSmoothFunctionStatus
    refl
    canonicalBoundaryFlatnessAtUnitRadiusStatus
    refl
    canonicalCompactSupportCutoffDefinitionStatus
    refl
    canonicalSmoothnessAcrossSupportBoundaryStatus
    refl
    canonicalNonCircularCompactSupportSourceStatus
    refl
    canonicalSmoothCompactSupportWitnessDecompositionStatus
    refl
    canonicalSmoothCompactSupportWitnessFlags
    refl
    requiredSmoothCompactSupportWitnessSubgates
    refl
    "Sprint 109 closes only the smooth compact-support witness decomposition ledger; all five analytic witness subgates and downstream Navier-Stokes Clay flags remain false."

canonicalNSSprint109SmoothCompactSupportWitnessReceipt :
  NSSprint109SmoothCompactSupportWitness
canonicalNSSprint109SmoothCompactSupportWitnessReceipt =
  canonicalNSSprint109SmoothCompactSupportWitness

canonicalSprint109SmoothCompactSupportWitnessFlags :
  (smoothCompactSupportWitnessDecompositionLedgerClosed ≡ true)
  × (baseExpSmoothFunctionClosed ≡ false)
  × (boundaryFlatnessAtUnitRadiusClosed ≡ false)
  × (compactSupportCutoffDefinitionClosed ≡ false)
  × (smoothnessAcrossSupportBoundaryClosed ≡ false)
  × (nonCircularCompactSupportSourceClosed ≡ false)
  × (smoothCompactSupportWitnessClosed ≡ false)
  × (radialBumpFunctionConstructionClosed ≡ false)
  × (smoothDyadicCutoffPartitionClosed ≡ false)
  × (littlewoodPaleyShellProjectorClosed ≡ false)
  × (dyadicShellEnergyDensityClosed ≡ false)
  × (highFrequencyConcentrationMeasureClosed ≡ false)
  × (strainCompressionAtHighFrequencyConcentrationPointsClosed ≡ false)
  × (signedLowModeFluxLowerBoundClosed ≡ false)
  × (timeIntegratedFluxSurplusClosed ≡ false)
  × (finiteKStarCollapseClosed ≡ false)
  × (clayNavierStokesPromoted ≡ false)
  × (failClosedSmoothCompactSupportWitnessDecomposition ≡ true)
canonicalSprint109SmoothCompactSupportWitnessFlags =
  refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl
