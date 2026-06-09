module DASHI.Physics.Closure.NSSprint108RadialBumpFunctionConstruction where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint107SmoothDyadicCutoffPartition
  as Sprint107

------------------------------------------------------------------------
-- Sprint 108 radial bump-function construction decomposition.
--
-- Sprint 107 recorded RadialBumpFunctionConstruction as the first open
-- subgate of SmoothDyadicCutoffPartition.  Sprint 108 records the five
-- concrete obligations needed for that radial bump construction.  The
-- decomposition ledger closes; every analytic subgate, the parent cutoff
-- partition, and every downstream Navier-Stokes Clay flag remains
-- fail-closed.

radialBumpFunctionConstructionDecompositionLedgerClosed : Bool
radialBumpFunctionConstructionDecompositionLedgerClosed = true

smoothCompactSupportWitnessClosed : Bool
smoothCompactSupportWitnessClosed = false

radialProfileDefinitionClosed : Bool
radialProfileDefinitionClosed = false

nonnegativeBumpWitnessClosed : Bool
nonnegativeBumpWitnessClosed = false

annularDifferenceBumpClosed : Bool
annularDifferenceBumpClosed = false

nonCircularRadialBumpSourceClosed : Bool
nonCircularRadialBumpSourceClosed = false

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

failClosedRadialBumpFunctionConstructionDecomposition : Bool
failClosedRadialBumpFunctionConstructionDecomposition = true

data SmoothCompactSupportWitness : Set where
  SmoothCompactSupportWitnessOpen :
    SmoothCompactSupportWitness

data RadialProfileDefinition : Set where
  RadialProfileDefinitionOpen :
    RadialProfileDefinition

data NonnegativeBumpWitness : Set where
  NonnegativeBumpWitnessOpen :
    NonnegativeBumpWitness

data AnnularDifferenceBump : Set where
  AnnularDifferenceBumpOpen :
    AnnularDifferenceBump

data NonCircularRadialBumpSource : Set where
  NonCircularRadialBumpSourceOpen :
    NonCircularRadialBumpSource

data RadialBumpFunctionConstructionDecomposition : Set where
  RadialBumpFunctionConstructionSplitsIntoFiveSubgates :
    RadialBumpFunctionConstructionDecomposition

record Sprint107RadialBumpFunctionConstructionAnchor : Set where
  constructor sprint107RadialBumpFunctionConstructionAnchorReceipt
  field
    sprint107Receipt :
      Sprint107.NSSprint107SmoothDyadicCutoffPartition
    sprint107ReceiptIsCanonical :
      sprint107Receipt
      ≡ Sprint107.canonicalNSSprint107SmoothDyadicCutoffPartition
    sprint107RadialBumpFunctionConstruction :
      Sprint107.RadialBumpFunctionConstruction
    sprint107RadialBumpFunctionConstructionIsCanonical :
      sprint107RadialBumpFunctionConstruction
      ≡ Sprint107.RadialBumpFunctionConstructionOpen
    sprint107DecompositionLedgerClosed :
      Sprint107.smoothDyadicCutoffPartitionDecompositionLedgerClosed
      ≡ true
    sprint107RadialBumpFunctionConstructionStillFalse :
      Sprint107.radialBumpFunctionConstructionClosed ≡ false
    sprint107SmoothDyadicCutoffPartitionStillFalse :
      Sprint107.smoothDyadicCutoffPartitionClosed ≡ false
    sprint107ClayPromotionStillFalse :
      Sprint107.clayNavierStokesPromoted ≡ false

open Sprint107RadialBumpFunctionConstructionAnchor public

canonicalSprint107RadialBumpFunctionConstructionAnchor :
  Sprint107RadialBumpFunctionConstructionAnchor
canonicalSprint107RadialBumpFunctionConstructionAnchor =
  sprint107RadialBumpFunctionConstructionAnchorReceipt
    Sprint107.canonicalNSSprint107SmoothDyadicCutoffPartition
    refl
    Sprint107.RadialBumpFunctionConstructionOpen
    refl
    refl
    refl
    refl
    refl

record RadialBumpFunctionConstructionSubgateStatus (Gate : Set) : Set where
  constructor radialBumpFunctionConstructionSubgateStatusReceipt
  field
    gate :
      Gate
    gateClosed :
      Bool
    gateClosedIsFalse :
      gateClosed ≡ false
    note :
      String

open RadialBumpFunctionConstructionSubgateStatus public

canonicalSmoothCompactSupportWitnessStatus :
  RadialBumpFunctionConstructionSubgateStatus SmoothCompactSupportWitness
canonicalSmoothCompactSupportWitnessStatus =
  radialBumpFunctionConstructionSubgateStatusReceipt
    SmoothCompactSupportWitnessOpen
    false
    refl
    "Requires a concrete smooth compact-support witness for the radial seed before any bump construction can close."

canonicalRadialProfileDefinitionStatus :
  RadialBumpFunctionConstructionSubgateStatus RadialProfileDefinition
canonicalRadialProfileDefinitionStatus =
  radialBumpFunctionConstructionSubgateStatusReceipt
    RadialProfileDefinitionOpen
    false
    refl
    "Requires an explicit radial profile with the intended inner plateau, transition region, and exterior zero behavior."

canonicalNonnegativeBumpWitnessStatus :
  RadialBumpFunctionConstructionSubgateStatus NonnegativeBumpWitness
canonicalNonnegativeBumpWitnessStatus =
  radialBumpFunctionConstructionSubgateStatusReceipt
    NonnegativeBumpWitnessOpen
    false
    refl
    "Requires a proof that the constructed bump is pointwise nonnegative on the active frequency domain."

canonicalAnnularDifferenceBumpStatus :
  RadialBumpFunctionConstructionSubgateStatus AnnularDifferenceBump
canonicalAnnularDifferenceBumpStatus =
  radialBumpFunctionConstructionSubgateStatusReceipt
    AnnularDifferenceBumpOpen
    false
    refl
    "Requires an annular difference bump whose support and transition behavior match the later dyadic shell partition."

canonicalNonCircularRadialBumpSourceStatus :
  RadialBumpFunctionConstructionSubgateStatus NonCircularRadialBumpSource
canonicalNonCircularRadialBumpSourceStatus =
  radialBumpFunctionConstructionSubgateStatusReceipt
    NonCircularRadialBumpSourceOpen
    false
    refl
    "Requires an explicit source boundary showing that the radial construction does not smuggle in a circular normalization assumption."

record RadialBumpFunctionConstructionDecompositionStatus : Set where
  constructor radialBumpFunctionConstructionDecompositionStatusReceipt
  field
    decomposition :
      RadialBumpFunctionConstructionDecomposition
    decompositionClosed :
      Bool
    decompositionClosedIsTrue :
      decompositionClosed ≡ true
    smoothCompactSupportWitness :
      SmoothCompactSupportWitness
    smoothCompactSupportWitnessIsCanonical :
      smoothCompactSupportWitness ≡ SmoothCompactSupportWitnessOpen
    radialProfileDefinition :
      RadialProfileDefinition
    radialProfileDefinitionIsCanonical :
      radialProfileDefinition ≡ RadialProfileDefinitionOpen
    nonnegativeBumpWitness :
      NonnegativeBumpWitness
    nonnegativeBumpWitnessIsCanonical :
      nonnegativeBumpWitness ≡ NonnegativeBumpWitnessOpen
    annularDifferenceBump :
      AnnularDifferenceBump
    annularDifferenceBumpIsCanonical :
      annularDifferenceBump ≡ AnnularDifferenceBumpOpen
    nonCircularRadialBumpSource :
      NonCircularRadialBumpSource
    nonCircularRadialBumpSourceIsCanonical :
      nonCircularRadialBumpSource ≡ NonCircularRadialBumpSourceOpen
    sprint107Gate :
      Sprint107.RadialBumpFunctionConstruction
    sprint107GateIsCanonical :
      sprint107Gate ≡ Sprint107.RadialBumpFunctionConstructionOpen
    sprint107GateClosed :
      Bool
    sprint107GateClosedIsFalse :
      sprint107GateClosed ≡ false
    note :
      String

open RadialBumpFunctionConstructionDecompositionStatus public

canonicalRadialBumpFunctionConstructionDecompositionStatus :
  RadialBumpFunctionConstructionDecompositionStatus
canonicalRadialBumpFunctionConstructionDecompositionStatus =
  radialBumpFunctionConstructionDecompositionStatusReceipt
    RadialBumpFunctionConstructionSplitsIntoFiveSubgates
    true
    refl
    SmoothCompactSupportWitnessOpen
    refl
    RadialProfileDefinitionOpen
    refl
    NonnegativeBumpWitnessOpen
    refl
    AnnularDifferenceBumpOpen
    refl
    NonCircularRadialBumpSourceOpen
    refl
    Sprint107.RadialBumpFunctionConstructionOpen
    refl
    false
    refl
    "Sprint 108 decomposes the Sprint 107 radial bump-function construction gate into five obligations without closing them."

requiredRadialBumpFunctionConstructionSubgates :
  List String
requiredRadialBumpFunctionConstructionSubgates =
  "SmoothCompactSupportWitness"
  ∷ "RadialProfileDefinition"
  ∷ "NonnegativeBumpWitness"
  ∷ "AnnularDifferenceBump"
  ∷ "NonCircularRadialBumpSource"
  ∷ []

record RadialBumpFunctionConstructionFlags : Set where
  constructor radialBumpFunctionConstructionFlagsReceipt
  field
    radialBumpFunctionConstructionDecompositionLedgerClosedFlag :
      radialBumpFunctionConstructionDecompositionLedgerClosed ≡ true
    smoothCompactSupportWitnessClosedFlag :
      smoothCompactSupportWitnessClosed ≡ false
    radialProfileDefinitionClosedFlag :
      radialProfileDefinitionClosed ≡ false
    nonnegativeBumpWitnessClosedFlag :
      nonnegativeBumpWitnessClosed ≡ false
    annularDifferenceBumpClosedFlag :
      annularDifferenceBumpClosed ≡ false
    nonCircularRadialBumpSourceClosedFlag :
      nonCircularRadialBumpSourceClosed ≡ false
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
    failClosedRadialBumpFunctionConstructionDecompositionFlag :
      failClosedRadialBumpFunctionConstructionDecomposition ≡ true

open RadialBumpFunctionConstructionFlags public

canonicalRadialBumpFunctionConstructionFlags :
  RadialBumpFunctionConstructionFlags
canonicalRadialBumpFunctionConstructionFlags =
  radialBumpFunctionConstructionFlagsReceipt
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

record NSSprint108RadialBumpFunctionConstruction : Set where
  constructor nsSprint108RadialBumpFunctionConstructionReceipt
  field
    sprint107Anchor :
      Sprint107RadialBumpFunctionConstructionAnchor
    sprint107AnchorIsCanonical :
      sprint107Anchor ≡ canonicalSprint107RadialBumpFunctionConstructionAnchor
    smoothCompactSupportWitnessStatus :
      RadialBumpFunctionConstructionSubgateStatus SmoothCompactSupportWitness
    smoothCompactSupportWitnessStatusIsCanonical :
      smoothCompactSupportWitnessStatus
      ≡ canonicalSmoothCompactSupportWitnessStatus
    radialProfileDefinitionStatus :
      RadialBumpFunctionConstructionSubgateStatus RadialProfileDefinition
    radialProfileDefinitionStatusIsCanonical :
      radialProfileDefinitionStatus
      ≡ canonicalRadialProfileDefinitionStatus
    nonnegativeBumpWitnessStatus :
      RadialBumpFunctionConstructionSubgateStatus NonnegativeBumpWitness
    nonnegativeBumpWitnessStatusIsCanonical :
      nonnegativeBumpWitnessStatus
      ≡ canonicalNonnegativeBumpWitnessStatus
    annularDifferenceBumpStatus :
      RadialBumpFunctionConstructionSubgateStatus AnnularDifferenceBump
    annularDifferenceBumpStatusIsCanonical :
      annularDifferenceBumpStatus
      ≡ canonicalAnnularDifferenceBumpStatus
    nonCircularRadialBumpSourceStatus :
      RadialBumpFunctionConstructionSubgateStatus NonCircularRadialBumpSource
    nonCircularRadialBumpSourceStatusIsCanonical :
      nonCircularRadialBumpSourceStatus
      ≡ canonicalNonCircularRadialBumpSourceStatus
    decompositionStatus :
      RadialBumpFunctionConstructionDecompositionStatus
    decompositionStatusIsCanonical :
      decompositionStatus
      ≡ canonicalRadialBumpFunctionConstructionDecompositionStatus
    flags :
      RadialBumpFunctionConstructionFlags
    flagsAreCanonical :
      flags ≡ canonicalRadialBumpFunctionConstructionFlags
    requiredSubgates :
      List String
    requiredSubgatesAreCanonical :
      requiredSubgates ≡ requiredRadialBumpFunctionConstructionSubgates
    noClayClaim :
      String

open NSSprint108RadialBumpFunctionConstruction public

canonicalNSSprint108RadialBumpFunctionConstruction :
  NSSprint108RadialBumpFunctionConstruction
canonicalNSSprint108RadialBumpFunctionConstruction =
  nsSprint108RadialBumpFunctionConstructionReceipt
    canonicalSprint107RadialBumpFunctionConstructionAnchor
    refl
    canonicalSmoothCompactSupportWitnessStatus
    refl
    canonicalRadialProfileDefinitionStatus
    refl
    canonicalNonnegativeBumpWitnessStatus
    refl
    canonicalAnnularDifferenceBumpStatus
    refl
    canonicalNonCircularRadialBumpSourceStatus
    refl
    canonicalRadialBumpFunctionConstructionDecompositionStatus
    refl
    canonicalRadialBumpFunctionConstructionFlags
    refl
    requiredRadialBumpFunctionConstructionSubgates
    refl
    "Sprint 108 closes only the radial bump-function construction decomposition ledger; all five analytic bump subgates and downstream Navier-Stokes Clay flags remain false."

canonicalNSSprint108RadialBumpFunctionConstructionReceipt :
  NSSprint108RadialBumpFunctionConstruction
canonicalNSSprint108RadialBumpFunctionConstructionReceipt =
  canonicalNSSprint108RadialBumpFunctionConstruction

canonicalSprint108RadialBumpFunctionConstructionFlags :
  (radialBumpFunctionConstructionDecompositionLedgerClosed ≡ true)
  × (smoothCompactSupportWitnessClosed ≡ false)
  × (radialProfileDefinitionClosed ≡ false)
  × (nonnegativeBumpWitnessClosed ≡ false)
  × (annularDifferenceBumpClosed ≡ false)
  × (nonCircularRadialBumpSourceClosed ≡ false)
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
  × (failClosedRadialBumpFunctionConstructionDecomposition ≡ true)
canonicalSprint108RadialBumpFunctionConstructionFlags =
  refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl
