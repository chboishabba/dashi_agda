module DASHI.Physics.Closure.NSSprint110BaseExpSmoothFunction where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint109SmoothCompactSupportWitness
  as Sprint109

------------------------------------------------------------------------
-- Sprint 110 base exp smooth-function decomposition.
--
-- Sprint 109 recorded BaseExpSmoothFunction as the first open subgate of
-- SmoothCompactSupportWitness.  Sprint 110 records the five concrete
-- obligations needed for that base exp smooth function.  The decomposition
-- ledger closes; every analytic subgate, the parent base exp smooth
-- function, the compact-support witness chain, and every downstream
-- Navier-Stokes Clay flag remains fail-closed.

baseExpSmoothFunctionDecompositionLedgerClosed : Bool
baseExpSmoothFunctionDecompositionLedgerClosed = true

expNegativeInverseSeedDefinitionClosed : Bool
expNegativeInverseSeedDefinitionClosed = false

smoothnessOnPositiveRadiusDomainClosed : Bool
smoothnessOnPositiveRadiusDomainClosed = false

derivativeHierarchyPolynomialOverPowerClosed : Bool
derivativeHierarchyPolynomialOverPowerClosed = false

positiveInteriorNonzeroWitnessClosed : Bool
positiveInteriorNonzeroWitnessClosed = false

nonCircularBaseExpSourceClosed : Bool
nonCircularBaseExpSourceClosed = false

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

failClosedBaseExpSmoothFunctionDecomposition : Bool
failClosedBaseExpSmoothFunctionDecomposition = true

data ExpNegativeInverseSeedDefinition : Set where
  ExpNegativeInverseSeedDefinitionOpen :
    ExpNegativeInverseSeedDefinition

data SmoothnessOnPositiveRadiusDomain : Set where
  SmoothnessOnPositiveRadiusDomainOpen :
    SmoothnessOnPositiveRadiusDomain

data DerivativeHierarchyPolynomialOverPower : Set where
  DerivativeHierarchyPolynomialOverPowerOpen :
    DerivativeHierarchyPolynomialOverPower

data PositiveInteriorNonzeroWitness : Set where
  PositiveInteriorNonzeroWitnessOpen :
    PositiveInteriorNonzeroWitness

data NonCircularBaseExpSource : Set where
  NonCircularBaseExpSourceOpen :
    NonCircularBaseExpSource

data BaseExpSmoothFunctionDecomposition : Set where
  BaseExpSmoothFunctionSplitsIntoFiveSubgates :
    BaseExpSmoothFunctionDecomposition

record Sprint109BaseExpSmoothFunctionAnchor : Set where
  constructor sprint109BaseExpSmoothFunctionAnchorReceipt
  field
    sprint109Receipt :
      Sprint109.NSSprint109SmoothCompactSupportWitness
    sprint109ReceiptIsCanonical :
      sprint109Receipt
      ≡ Sprint109.canonicalNSSprint109SmoothCompactSupportWitness
    sprint109BaseExpSmoothFunction :
      Sprint109.BaseExpSmoothFunction
    sprint109BaseExpSmoothFunctionIsCanonical :
      sprint109BaseExpSmoothFunction
      ≡ Sprint109.BaseExpSmoothFunctionOpen
    sprint109DecompositionLedgerClosed :
      Sprint109.smoothCompactSupportWitnessDecompositionLedgerClosed
      ≡ true
    sprint109BaseExpSmoothFunctionStillFalse :
      Sprint109.baseExpSmoothFunctionClosed ≡ false
    sprint109SmoothCompactSupportWitnessStillFalse :
      Sprint109.smoothCompactSupportWitnessClosed ≡ false
    sprint109ClayPromotionStillFalse :
      Sprint109.clayNavierStokesPromoted ≡ false

open Sprint109BaseExpSmoothFunctionAnchor public

canonicalSprint109BaseExpSmoothFunctionAnchor :
  Sprint109BaseExpSmoothFunctionAnchor
canonicalSprint109BaseExpSmoothFunctionAnchor =
  sprint109BaseExpSmoothFunctionAnchorReceipt
    Sprint109.canonicalNSSprint109SmoothCompactSupportWitness
    refl
    Sprint109.BaseExpSmoothFunctionOpen
    refl
    refl
    refl
    refl
    refl

record BaseExpSmoothFunctionSubgateStatus (Gate : Set) : Set where
  constructor baseExpSmoothFunctionSubgateStatusReceipt
  field
    gate :
      Gate
    gateClosed :
      Bool
    gateClosedIsFalse :
      gateClosed ≡ false
    note :
      String

open BaseExpSmoothFunctionSubgateStatus public

canonicalExpNegativeInverseSeedDefinitionStatus :
  BaseExpSmoothFunctionSubgateStatus ExpNegativeInverseSeedDefinition
canonicalExpNegativeInverseSeedDefinitionStatus =
  baseExpSmoothFunctionSubgateStatusReceipt
    ExpNegativeInverseSeedDefinitionOpen
    false
    refl
    "Requires the explicit negative-inverse exponential seed definition before the base exp smooth function can close."

canonicalSmoothnessOnPositiveRadiusDomainStatus :
  BaseExpSmoothFunctionSubgateStatus SmoothnessOnPositiveRadiusDomain
canonicalSmoothnessOnPositiveRadiusDomainStatus =
  baseExpSmoothFunctionSubgateStatusReceipt
    SmoothnessOnPositiveRadiusDomainOpen
    false
    refl
    "Requires smoothness of the exp seed on the positive-radius domain."

canonicalDerivativeHierarchyPolynomialOverPowerStatus :
  BaseExpSmoothFunctionSubgateStatus DerivativeHierarchyPolynomialOverPower
canonicalDerivativeHierarchyPolynomialOverPowerStatus =
  baseExpSmoothFunctionSubgateStatusReceipt
    DerivativeHierarchyPolynomialOverPowerOpen
    false
    refl
    "Requires the full derivative hierarchy as polynomial-over-power factors times the seed."

canonicalPositiveInteriorNonzeroWitnessStatus :
  BaseExpSmoothFunctionSubgateStatus PositiveInteriorNonzeroWitness
canonicalPositiveInteriorNonzeroWitnessStatus =
  baseExpSmoothFunctionSubgateStatusReceipt
    PositiveInteriorNonzeroWitnessOpen
    false
    refl
    "Requires a positive interior nonzero witness for the selected base exp seed."

canonicalNonCircularBaseExpSourceStatus :
  BaseExpSmoothFunctionSubgateStatus NonCircularBaseExpSource
canonicalNonCircularBaseExpSourceStatus =
  baseExpSmoothFunctionSubgateStatusReceipt
    NonCircularBaseExpSourceOpen
    false
    refl
    "Requires an explicit non-circular source for the base exp smooth function."

record BaseExpSmoothFunctionDecompositionStatus : Set where
  constructor baseExpSmoothFunctionDecompositionStatusReceipt
  field
    decomposition :
      BaseExpSmoothFunctionDecomposition
    decompositionClosed :
      Bool
    decompositionClosedIsTrue :
      decompositionClosed ≡ true
    expNegativeInverseSeedDefinition :
      ExpNegativeInverseSeedDefinition
    expNegativeInverseSeedDefinitionIsCanonical :
      expNegativeInverseSeedDefinition
      ≡ ExpNegativeInverseSeedDefinitionOpen
    smoothnessOnPositiveRadiusDomain :
      SmoothnessOnPositiveRadiusDomain
    smoothnessOnPositiveRadiusDomainIsCanonical :
      smoothnessOnPositiveRadiusDomain
      ≡ SmoothnessOnPositiveRadiusDomainOpen
    derivativeHierarchyPolynomialOverPower :
      DerivativeHierarchyPolynomialOverPower
    derivativeHierarchyPolynomialOverPowerIsCanonical :
      derivativeHierarchyPolynomialOverPower
      ≡ DerivativeHierarchyPolynomialOverPowerOpen
    positiveInteriorNonzeroWitness :
      PositiveInteriorNonzeroWitness
    positiveInteriorNonzeroWitnessIsCanonical :
      positiveInteriorNonzeroWitness
      ≡ PositiveInteriorNonzeroWitnessOpen
    nonCircularBaseExpSource :
      NonCircularBaseExpSource
    nonCircularBaseExpSourceIsCanonical :
      nonCircularBaseExpSource ≡ NonCircularBaseExpSourceOpen
    sprint109Gate :
      Sprint109.BaseExpSmoothFunction
    sprint109GateIsCanonical :
      sprint109Gate ≡ Sprint109.BaseExpSmoothFunctionOpen
    sprint109GateClosed :
      Bool
    sprint109GateClosedIsFalse :
      sprint109GateClosed ≡ false
    note :
      String

open BaseExpSmoothFunctionDecompositionStatus public

canonicalBaseExpSmoothFunctionDecompositionStatus :
  BaseExpSmoothFunctionDecompositionStatus
canonicalBaseExpSmoothFunctionDecompositionStatus =
  baseExpSmoothFunctionDecompositionStatusReceipt
    BaseExpSmoothFunctionSplitsIntoFiveSubgates
    true
    refl
    ExpNegativeInverseSeedDefinitionOpen
    refl
    SmoothnessOnPositiveRadiusDomainOpen
    refl
    DerivativeHierarchyPolynomialOverPowerOpen
    refl
    PositiveInteriorNonzeroWitnessOpen
    refl
    NonCircularBaseExpSourceOpen
    refl
    Sprint109.BaseExpSmoothFunctionOpen
    refl
    false
    refl
    "Sprint 110 decomposes the Sprint 109 base exp smooth-function gate into five obligations without closing them."

requiredBaseExpSmoothFunctionSubgates :
  List String
requiredBaseExpSmoothFunctionSubgates =
  "ExpNegativeInverseSeedDefinition"
  ∷ "SmoothnessOnPositiveRadiusDomain"
  ∷ "DerivativeHierarchyPolynomialOverPower"
  ∷ "PositiveInteriorNonzeroWitness"
  ∷ "NonCircularBaseExpSource"
  ∷ []

record BaseExpSmoothFunctionFlags : Set where
  constructor baseExpSmoothFunctionFlagsReceipt
  field
    baseExpSmoothFunctionDecompositionLedgerClosedFlag :
      baseExpSmoothFunctionDecompositionLedgerClosed ≡ true
    expNegativeInverseSeedDefinitionClosedFlag :
      expNegativeInverseSeedDefinitionClosed ≡ false
    smoothnessOnPositiveRadiusDomainClosedFlag :
      smoothnessOnPositiveRadiusDomainClosed ≡ false
    derivativeHierarchyPolynomialOverPowerClosedFlag :
      derivativeHierarchyPolynomialOverPowerClosed ≡ false
    positiveInteriorNonzeroWitnessClosedFlag :
      positiveInteriorNonzeroWitnessClosed ≡ false
    nonCircularBaseExpSourceClosedFlag :
      nonCircularBaseExpSourceClosed ≡ false
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
    failClosedBaseExpSmoothFunctionDecompositionFlag :
      failClosedBaseExpSmoothFunctionDecomposition ≡ true

open BaseExpSmoothFunctionFlags public

canonicalBaseExpSmoothFunctionFlags :
  BaseExpSmoothFunctionFlags
canonicalBaseExpSmoothFunctionFlags =
  baseExpSmoothFunctionFlagsReceipt
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
    refl
    refl
    refl
    refl
    refl

record NSSprint110BaseExpSmoothFunction : Set where
  constructor nsSprint110BaseExpSmoothFunctionReceipt
  field
    sprint109Anchor :
      Sprint109BaseExpSmoothFunctionAnchor
    sprint109AnchorIsCanonical :
      sprint109Anchor ≡ canonicalSprint109BaseExpSmoothFunctionAnchor
    expNegativeInverseSeedDefinitionStatus :
      BaseExpSmoothFunctionSubgateStatus ExpNegativeInverseSeedDefinition
    expNegativeInverseSeedDefinitionStatusIsCanonical :
      expNegativeInverseSeedDefinitionStatus
      ≡ canonicalExpNegativeInverseSeedDefinitionStatus
    smoothnessOnPositiveRadiusDomainStatus :
      BaseExpSmoothFunctionSubgateStatus SmoothnessOnPositiveRadiusDomain
    smoothnessOnPositiveRadiusDomainStatusIsCanonical :
      smoothnessOnPositiveRadiusDomainStatus
      ≡ canonicalSmoothnessOnPositiveRadiusDomainStatus
    derivativeHierarchyPolynomialOverPowerStatus :
      BaseExpSmoothFunctionSubgateStatus
        DerivativeHierarchyPolynomialOverPower
    derivativeHierarchyPolynomialOverPowerStatusIsCanonical :
      derivativeHierarchyPolynomialOverPowerStatus
      ≡ canonicalDerivativeHierarchyPolynomialOverPowerStatus
    positiveInteriorNonzeroWitnessStatus :
      BaseExpSmoothFunctionSubgateStatus PositiveInteriorNonzeroWitness
    positiveInteriorNonzeroWitnessStatusIsCanonical :
      positiveInteriorNonzeroWitnessStatus
      ≡ canonicalPositiveInteriorNonzeroWitnessStatus
    nonCircularBaseExpSourceStatus :
      BaseExpSmoothFunctionSubgateStatus NonCircularBaseExpSource
    nonCircularBaseExpSourceStatusIsCanonical :
      nonCircularBaseExpSourceStatus
      ≡ canonicalNonCircularBaseExpSourceStatus
    decompositionStatus :
      BaseExpSmoothFunctionDecompositionStatus
    decompositionStatusIsCanonical :
      decompositionStatus
      ≡ canonicalBaseExpSmoothFunctionDecompositionStatus
    flags :
      BaseExpSmoothFunctionFlags
    flagsAreCanonical :
      flags ≡ canonicalBaseExpSmoothFunctionFlags
    requiredSubgates :
      List String
    requiredSubgatesAreCanonical :
      requiredSubgates ≡ requiredBaseExpSmoothFunctionSubgates
    noClayClaim :
      String

open NSSprint110BaseExpSmoothFunction public

canonicalNSSprint110BaseExpSmoothFunction :
  NSSprint110BaseExpSmoothFunction
canonicalNSSprint110BaseExpSmoothFunction =
  nsSprint110BaseExpSmoothFunctionReceipt
    canonicalSprint109BaseExpSmoothFunctionAnchor
    refl
    canonicalExpNegativeInverseSeedDefinitionStatus
    refl
    canonicalSmoothnessOnPositiveRadiusDomainStatus
    refl
    canonicalDerivativeHierarchyPolynomialOverPowerStatus
    refl
    canonicalPositiveInteriorNonzeroWitnessStatus
    refl
    canonicalNonCircularBaseExpSourceStatus
    refl
    canonicalBaseExpSmoothFunctionDecompositionStatus
    refl
    canonicalBaseExpSmoothFunctionFlags
    refl
    requiredBaseExpSmoothFunctionSubgates
    refl
    "Sprint 110 closes only the base exp smooth-function decomposition ledger; all five analytic subgates and downstream Navier-Stokes Clay flags remain false."

canonicalNSSprint110BaseExpSmoothFunctionReceipt :
  NSSprint110BaseExpSmoothFunction
canonicalNSSprint110BaseExpSmoothFunctionReceipt =
  canonicalNSSprint110BaseExpSmoothFunction

canonicalSprint110BaseExpSmoothFunctionFlags :
  (baseExpSmoothFunctionDecompositionLedgerClosed ≡ true)
  × (expNegativeInverseSeedDefinitionClosed ≡ false)
  × (smoothnessOnPositiveRadiusDomainClosed ≡ false)
  × (derivativeHierarchyPolynomialOverPowerClosed ≡ false)
  × (positiveInteriorNonzeroWitnessClosed ≡ false)
  × (nonCircularBaseExpSourceClosed ≡ false)
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
  × (failClosedBaseExpSmoothFunctionDecomposition ≡ true)
canonicalSprint110BaseExpSmoothFunctionFlags =
  refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl
