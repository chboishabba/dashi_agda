module DASHI.Physics.Closure.NSLeiRenTianGreatCircleCriterionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSMicrolocalDefectMassConstructionBoundary as Micro
import DASHI.Physics.Closure.NSRankOneProjectionCommutatorFormula as RankOne
import DASHI.Physics.Closure.NSZeroModeSetClassificationBoundary as ZeroMode

------------------------------------------------------------------------
-- Lei-Ren-Tian great-circle criterion boundary.
--
-- External deterministic theorem boundary:
--
--   Lei-Ren-Tian, arXiv:2501.08976.
--
-- Conservative DASHI interpretation:
--
--   A singular high-vorticity direction set I must intersect every great
--   circle on S^2.  Equivalently, if high-vorticity directions are trapped
--   in a double cone / cone-like angular set avoiding some great circle,
--   the singularity mechanism is ruled out by the external theorem.
--
-- This module does not internally prove Lei-Ren-Tian, does not prove that
-- any DASHI zero-mode set avoids a great circle, does not transfer the
-- qualitative vorticity-direction set I to a quantitative microlocal defect
-- measure, and does not promote Clay Navier-Stokes.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- External source and theorem metadata.

leiRenTianArxivId : String
leiRenTianArxivId =
  "arXiv:2501.08976"

leiRenTianPaperTitle : String
leiRenTianPaperTitle =
  "A geometric characterization of potential Navier-Stokes singularities"

leiRenTianGreatCircleClaim : String
leiRenTianGreatCircleClaim =
  "A singular high-vorticity direction set I must intersect every great circle on S^2."

leiRenTianConeCriterionClaim : String
leiRenTianConeCriterionClaim =
  "If high-vorticity directions remain in a double cone avoiding a great circle, the point is regular."

leiRenTianBoundaryUse : String
leiRenTianBoundaryUse =
  "External deterministic angular-spread authority boundary; not an internal DASHI proof or Clay promotion."

data LeiRenTianCriterionSourceRow : Set where
  sourceAuthorsLeiRenTian2025 :
    LeiRenTianCriterionSourceRow

  sourceArxiv250108976 :
    LeiRenTianCriterionSourceRow

  sourceGeometricCharacterizationTitle :
    LeiRenTianCriterionSourceRow

  singularDirectionSetHitsEveryGreatCircle :
    LeiRenTianCriterionSourceRow

  doubleConeAvoidanceRegularityCriterion :
    LeiRenTianCriterionSourceRow

  externalDeterministicTheoremBoundary :
    LeiRenTianCriterionSourceRow

canonicalLeiRenTianCriterionSourceRows :
  List LeiRenTianCriterionSourceRow
canonicalLeiRenTianCriterionSourceRows =
  sourceAuthorsLeiRenTian2025
  ∷ sourceArxiv250108976
  ∷ sourceGeometricCharacterizationTitle
  ∷ singularDirectionSetHitsEveryGreatCircle
  ∷ doubleConeAvoidanceRegularityCriterion
  ∷ externalDeterministicTheoremBoundary
  ∷ []

leiRenTianCriterionSourceRowCount : Nat
leiRenTianCriterionSourceRowCount =
  listLength canonicalLeiRenTianCriterionSourceRows

leiRenTianCriterionSourceRowCountIs6 :
  leiRenTianCriterionSourceRowCount ≡ 6
leiRenTianCriterionSourceRowCountIs6 =
  refl

------------------------------------------------------------------------
-- Direction-set and great-circle carriers.

data SphereDirectionCarrier : Set where
  unitFrequencySphereS2 :
    SphereDirectionCarrier

data HighVorticityDirectionSet : Set where
  leiRenTianDirectionSetI :
    SphereDirectionCarrier →
    HighVorticityDirectionSet

data GreatCircleCarrier : Set where
  arbitraryGreatCircleOnS2 :
    SphereDirectionCarrier →
    GreatCircleCarrier

data GreatCircleHittingProperty : Set where
  intersectsEveryGreatCircle :
    HighVorticityDirectionSet →
    GreatCircleHittingProperty

data ConeAvoidanceProperty : Set where
  containedInDoubleConeAvoidingSomeGreatCircle :
    HighVorticityDirectionSet →
    ConeAvoidanceProperty

data RegularityConsequenceBoundary : Set where
  regularityFromDoubleConeAvoidanceAuthority :
    ConeAvoidanceProperty →
    RegularityConsequenceBoundary

data SingularityNecessaryConditionBoundary : Set where
  singularityRequiresGreatCircleHittingAuthority :
    GreatCircleHittingProperty →
    SingularityNecessaryConditionBoundary

data GreatCircleConeCriterionEquivalenceBoundary : Set where
  contrapositiveBoundary :
    SingularityNecessaryConditionBoundary →
    RegularityConsequenceBoundary →
    GreatCircleConeCriterionEquivalenceBoundary

canonicalSphereDirectionCarrier : SphereDirectionCarrier
canonicalSphereDirectionCarrier =
  unitFrequencySphereS2

canonicalHighVorticityDirectionSet :
  HighVorticityDirectionSet
canonicalHighVorticityDirectionSet =
  leiRenTianDirectionSetI canonicalSphereDirectionCarrier

canonicalGreatCircleCarrier : GreatCircleCarrier
canonicalGreatCircleCarrier =
  arbitraryGreatCircleOnS2 canonicalSphereDirectionCarrier

canonicalGreatCircleHittingProperty :
  GreatCircleHittingProperty
canonicalGreatCircleHittingProperty =
  intersectsEveryGreatCircle canonicalHighVorticityDirectionSet

canonicalConeAvoidanceProperty :
  ConeAvoidanceProperty
canonicalConeAvoidanceProperty =
  containedInDoubleConeAvoidingSomeGreatCircle
    canonicalHighVorticityDirectionSet

canonicalRegularityConsequenceBoundary :
  RegularityConsequenceBoundary
canonicalRegularityConsequenceBoundary =
  regularityFromDoubleConeAvoidanceAuthority
    canonicalConeAvoidanceProperty

canonicalSingularityNecessaryConditionBoundary :
  SingularityNecessaryConditionBoundary
canonicalSingularityNecessaryConditionBoundary =
  singularityRequiresGreatCircleHittingAuthority
    canonicalGreatCircleHittingProperty

canonicalGreatCircleConeCriterionEquivalenceBoundary :
  GreatCircleConeCriterionEquivalenceBoundary
canonicalGreatCircleConeCriterionEquivalenceBoundary =
  contrapositiveBoundary
    canonicalSingularityNecessaryConditionBoundary
    canonicalRegularityConsequenceBoundary

------------------------------------------------------------------------
-- Zero-mode trap boundary hook.

data ZeroModeTrapGeometryStatus : Set where
  zeroModeTrapAvoidsSomeGreatCircle :
    ZeroMode.NSZeroModeSet →
    ZeroModeTrapGeometryStatus

  zeroModeTrapGreatCircleHittingUnknown :
    ZeroMode.NSZeroModeSet →
    ZeroModeTrapGeometryStatus

data GreatCircleZeroModeTrapExclusionBoundary : Set where
  excludedWhenTrapAvoidsGreatCircle :
    ZeroModeTrapGeometryStatus →
    SingularityNecessaryConditionBoundary →
    GreatCircleZeroModeTrapExclusionBoundary

canonicalRadialZeroModeTrapStatus :
  ZeroModeTrapGeometryStatus
canonicalRadialZeroModeTrapStatus =
  zeroModeTrapGreatCircleHittingUnknown
    ZeroMode.canonicalRadialZeroModeSet

canonicalTangentialZeroModeTrapStatus :
  ZeroModeTrapGeometryStatus
canonicalTangentialZeroModeTrapStatus =
  zeroModeTrapGreatCircleHittingUnknown
    ZeroMode.canonicalTangentialZeroModeSet

canonicalRadialTrapExclusionBoundary :
  GreatCircleZeroModeTrapExclusionBoundary
canonicalRadialTrapExclusionBoundary =
  excludedWhenTrapAvoidsGreatCircle
    canonicalRadialZeroModeTrapStatus
    canonicalSingularityNecessaryConditionBoundary

canonicalTangentialTrapExclusionBoundary :
  GreatCircleZeroModeTrapExclusionBoundary
canonicalTangentialTrapExclusionBoundary =
  excludedWhenTrapAvoidsGreatCircle
    canonicalTangentialZeroModeTrapStatus
    canonicalSingularityNecessaryConditionBoundary

canonicalZeroModeTrapStatuses :
  List ZeroModeTrapGeometryStatus
canonicalZeroModeTrapStatuses =
  canonicalRadialZeroModeTrapStatus
  ∷ canonicalTangentialZeroModeTrapStatus
  ∷ []

zeroModeTrapStatusCount : Nat
zeroModeTrapStatusCount =
  listLength canonicalZeroModeTrapStatuses

zeroModeTrapStatusCountIs2 :
  zeroModeTrapStatusCount ≡ 2
zeroModeTrapStatusCountIs2 =
  refl

------------------------------------------------------------------------
-- Support rows, blockers, and statuses.

data GreatCircleCriterionSupportRow : Set where
  leiRenTianSourceMetadataRow :
    GreatCircleCriterionSupportRow

  greatCircleHittingNecessaryConditionRow :
    GreatCircleCriterionSupportRow

  doubleConeAvoidanceRegularityRow :
    GreatCircleCriterionSupportRow

  contrapositiveEquivalenceBoundaryRow :
    GreatCircleCriterionSupportRow

  zeroModeClassificationAnchorRow :
    GreatCircleCriterionSupportRow

  rankOneDefectFormulaAnchorRow :
    GreatCircleCriterionSupportRow

  microlocalDefectMassBoundaryAnchorRow :
    GreatCircleCriterionSupportRow

  zeroModeTrapGeometryTargetRow :
    GreatCircleCriterionSupportRow

  quantitativeMeasureTransferTargetRow :
    GreatCircleCriterionSupportRow

  noClayPromotionRow :
    GreatCircleCriterionSupportRow

canonicalGreatCircleCriterionSupportRows :
  List GreatCircleCriterionSupportRow
canonicalGreatCircleCriterionSupportRows =
  leiRenTianSourceMetadataRow
  ∷ greatCircleHittingNecessaryConditionRow
  ∷ doubleConeAvoidanceRegularityRow
  ∷ contrapositiveEquivalenceBoundaryRow
  ∷ zeroModeClassificationAnchorRow
  ∷ rankOneDefectFormulaAnchorRow
  ∷ microlocalDefectMassBoundaryAnchorRow
  ∷ zeroModeTrapGeometryTargetRow
  ∷ quantitativeMeasureTransferTargetRow
  ∷ noClayPromotionRow
  ∷ []

greatCircleCriterionSupportRowCount : Nat
greatCircleCriterionSupportRowCount =
  listLength canonicalGreatCircleCriterionSupportRows

greatCircleCriterionSupportRowCountIs10 :
  greatCircleCriterionSupportRowCount ≡ 10
greatCircleCriterionSupportRowCountIs10 =
  refl

data GreatCircleCriterionBlocker : Set where
  leiRenTianTheoremNotInternallyFormalized :
    GreatCircleCriterionBlocker

  missingAuthorityTokenNormalization :
    GreatCircleCriterionBlocker

  missingZeroModeGreatCircleAvoidanceClassification :
    GreatCircleCriterionBlocker

  missingConeTrapToZeroModeTrapBinding :
    GreatCircleCriterionBlocker

  missingDirectionSetIToMicrolocalMeasureTransfer :
    GreatCircleCriterionBlocker

  missingQuantitativePositiveMassOutsideZeroModes :
    GreatCircleCriterionBlocker

  missingSectorSwitchingCompactness :
    GreatCircleCriterionBlocker

  missingLeakageAwayFromZeroModes :
    GreatCircleCriterionBlocker

  missingNSCriticalResidualNonPositive :
    GreatCircleCriterionBlocker

  missingFullLocalDefectMonotonicity :
    GreatCircleCriterionBlocker

  missingMechanismExhaustionForFullClayNS :
    GreatCircleCriterionBlocker

  clayNavierStokesPromotionClosed :
    GreatCircleCriterionBlocker

canonicalGreatCircleCriterionBlockers :
  List GreatCircleCriterionBlocker
canonicalGreatCircleCriterionBlockers =
  leiRenTianTheoremNotInternallyFormalized
  ∷ missingAuthorityTokenNormalization
  ∷ missingZeroModeGreatCircleAvoidanceClassification
  ∷ missingConeTrapToZeroModeTrapBinding
  ∷ missingDirectionSetIToMicrolocalMeasureTransfer
  ∷ missingQuantitativePositiveMassOutsideZeroModes
  ∷ missingSectorSwitchingCompactness
  ∷ missingLeakageAwayFromZeroModes
  ∷ missingNSCriticalResidualNonPositive
  ∷ missingFullLocalDefectMonotonicity
  ∷ missingMechanismExhaustionForFullClayNS
  ∷ clayNavierStokesPromotionClosed
  ∷ []

greatCircleCriterionBlockerCount : Nat
greatCircleCriterionBlockerCount =
  listLength canonicalGreatCircleCriterionBlockers

greatCircleCriterionBlockerCountIs12 :
  greatCircleCriterionBlockerCount ≡ 12
greatCircleCriterionBlockerCountIs12 =
  refl

data GreatCircleCriterionStatusRow : Set where
  externalTheoremBoundaryRecordedStatus :
    GreatCircleCriterionStatusRow

  greatCircleCriterionTypedStatus :
    GreatCircleCriterionStatusRow

  doubleConeCriterionTypedStatus :
    GreatCircleCriterionStatusRow

  zeroModeClassificationImportedStatus :
    GreatCircleCriterionStatusRow

  rankOneFormulaImportedStatus :
    GreatCircleCriterionStatusRow

  microlocalBoundaryImportedStatus :
    GreatCircleCriterionStatusRow

  internalFormalizationFalseStatus :
    GreatCircleCriterionStatusRow

  quantitativeMeasureTransferFalseStatus :
    GreatCircleCriterionStatusRow

  clayPromotionFalseStatus :
    GreatCircleCriterionStatusRow

canonicalGreatCircleCriterionStatusRows :
  List GreatCircleCriterionStatusRow
canonicalGreatCircleCriterionStatusRows =
  externalTheoremBoundaryRecordedStatus
  ∷ greatCircleCriterionTypedStatus
  ∷ doubleConeCriterionTypedStatus
  ∷ zeroModeClassificationImportedStatus
  ∷ rankOneFormulaImportedStatus
  ∷ microlocalBoundaryImportedStatus
  ∷ internalFormalizationFalseStatus
  ∷ quantitativeMeasureTransferFalseStatus
  ∷ clayPromotionFalseStatus
  ∷ []

greatCircleCriterionStatusRowCount : Nat
greatCircleCriterionStatusRowCount =
  listLength canonicalGreatCircleCriterionStatusRows

greatCircleCriterionStatusRowCountIs9 :
  greatCircleCriterionStatusRowCount ≡ 9
greatCircleCriterionStatusRowCountIs9 =
  refl

------------------------------------------------------------------------
-- Promotion-closed type.

data GreatCircleCriterionPromotion : Set where

greatCircleCriterionPromotionImpossibleHere :
  GreatCircleCriterionPromotion →
  ⊥
greatCircleCriterionPromotionImpossibleHere ()

------------------------------------------------------------------------
-- Governance flags.

NSLeiRenTianGreatCircleCriterionBoundaryRecorded : Bool
NSLeiRenTianGreatCircleCriterionBoundaryRecorded =
  true

ExternalDeterministicTheoremBoundaryRecorded : Bool
ExternalDeterministicTheoremBoundaryRecorded =
  true

GreatCircleHittingCriterionTyped : Bool
GreatCircleHittingCriterionTyped =
  true

DoubleConeAvoidanceCriterionTyped : Bool
DoubleConeAvoidanceCriterionTyped =
  true

ContrapositiveEquivalenceBoundaryTyped : Bool
ContrapositiveEquivalenceBoundaryTyped =
  true

ZeroModeClassificationAnchorImported : Bool
ZeroModeClassificationAnchorImported =
  true

RankOneFormulaAnchorImported : Bool
RankOneFormulaAnchorImported =
  true

MicrolocalDefectMassBoundaryAnchorImported : Bool
MicrolocalDefectMassBoundaryAnchorImported =
  true

LeiRenTianTheoremInternallyFormalized : Bool
LeiRenTianTheoremInternallyFormalized =
  false

LeiRenTianAuthorityTokenAccepted : Bool
LeiRenTianAuthorityTokenAccepted =
  false

ZeroModeGreatCircleAvoidanceClassified : Bool
ZeroModeGreatCircleAvoidanceClassified =
  false

ConeTrapToZeroModeTrapBindingProved : Bool
ConeTrapToZeroModeTrapBindingProved =
  false

DirectionSetIToMicrolocalMeasureTransferProved : Bool
DirectionSetIToMicrolocalMeasureTransferProved =
  false

QuantitativePositiveMassOutsideZeroModesProved : Bool
QuantitativePositiveMassOutsideZeroModesProved =
  false

SectorSwitchingCompactnessProved : Bool
SectorSwitchingCompactnessProved =
  false

LeakageAwayFromZeroModesProved : Bool
LeakageAwayFromZeroModesProved =
  false

MicrolocalDefectMassConstructed : Bool
MicrolocalDefectMassConstructed =
  false

NSCriticalResidualNonPositive : Bool
NSCriticalResidualNonPositive =
  false

FullLocalDefectMonotonicity : Bool
FullLocalDefectMonotonicity =
  false

MechanismExhaustionForFullClayNS : Bool
MechanismExhaustionForFullClayNS =
  false

full_clay_ns_solved : Bool
full_clay_ns_solved =
  false

fullClayNSSolved : Bool
fullClayNSSolved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

greatCircleCriterionBoundaryRecordedIsTrue :
  NSLeiRenTianGreatCircleCriterionBoundaryRecorded ≡ true
greatCircleCriterionBoundaryRecordedIsTrue =
  refl

externalDeterministicTheoremBoundaryRecordedIsTrue :
  ExternalDeterministicTheoremBoundaryRecorded ≡ true
externalDeterministicTheoremBoundaryRecordedIsTrue =
  refl

greatCircleHittingCriterionTypedIsTrue :
  GreatCircleHittingCriterionTyped ≡ true
greatCircleHittingCriterionTypedIsTrue =
  refl

doubleConeAvoidanceCriterionTypedIsTrue :
  DoubleConeAvoidanceCriterionTyped ≡ true
doubleConeAvoidanceCriterionTypedIsTrue =
  refl

contrapositiveEquivalenceBoundaryTypedIsTrue :
  ContrapositiveEquivalenceBoundaryTyped ≡ true
contrapositiveEquivalenceBoundaryTypedIsTrue =
  refl

zeroModeClassificationAnchorImportedIsTrue :
  ZeroModeClassificationAnchorImported ≡ true
zeroModeClassificationAnchorImportedIsTrue =
  refl

rankOneFormulaAnchorImportedIsTrue :
  RankOneFormulaAnchorImported ≡ true
rankOneFormulaAnchorImportedIsTrue =
  refl

microlocalDefectMassBoundaryAnchorImportedIsTrue :
  MicrolocalDefectMassBoundaryAnchorImported ≡ true
microlocalDefectMassBoundaryAnchorImportedIsTrue =
  refl

leiRenTianTheoremInternallyFormalizedIsFalse :
  LeiRenTianTheoremInternallyFormalized ≡ false
leiRenTianTheoremInternallyFormalizedIsFalse =
  refl

leiRenTianAuthorityTokenAcceptedIsFalse :
  LeiRenTianAuthorityTokenAccepted ≡ false
leiRenTianAuthorityTokenAcceptedIsFalse =
  refl

zeroModeGreatCircleAvoidanceClassifiedIsFalse :
  ZeroModeGreatCircleAvoidanceClassified ≡ false
zeroModeGreatCircleAvoidanceClassifiedIsFalse =
  refl

coneTrapToZeroModeTrapBindingProvedIsFalse :
  ConeTrapToZeroModeTrapBindingProved ≡ false
coneTrapToZeroModeTrapBindingProvedIsFalse =
  refl

directionSetIToMicrolocalMeasureTransferProvedIsFalse :
  DirectionSetIToMicrolocalMeasureTransferProved ≡ false
directionSetIToMicrolocalMeasureTransferProvedIsFalse =
  refl

quantitativePositiveMassOutsideZeroModesProvedIsFalse :
  QuantitativePositiveMassOutsideZeroModesProved ≡ false
quantitativePositiveMassOutsideZeroModesProvedIsFalse =
  refl

sectorSwitchingCompactnessProvedIsFalse :
  SectorSwitchingCompactnessProved ≡ false
sectorSwitchingCompactnessProvedIsFalse =
  refl

leakageAwayFromZeroModesProvedIsFalse :
  LeakageAwayFromZeroModesProved ≡ false
leakageAwayFromZeroModesProvedIsFalse =
  refl

microlocalDefectMassConstructedIsFalse :
  MicrolocalDefectMassConstructed ≡ false
microlocalDefectMassConstructedIsFalse =
  refl

nsCriticalResidualNonPositiveIsFalse :
  NSCriticalResidualNonPositive ≡ false
nsCriticalResidualNonPositiveIsFalse =
  refl

fullLocalDefectMonotonicityIsFalse :
  FullLocalDefectMonotonicity ≡ false
fullLocalDefectMonotonicityIsFalse =
  refl

mechanismExhaustionForFullClayNSIsFalse :
  MechanismExhaustionForFullClayNS ≡ false
mechanismExhaustionForFullClayNSIsFalse =
  refl

fullClayNSSolvedSnakeIsFalse :
  full_clay_ns_solved ≡ false
fullClayNSSolvedSnakeIsFalse =
  refl

fullClayNSSolvedIsFalse :
  fullClayNSSolved ≡ false
fullClayNSSolvedIsFalse =
  refl

clayNavierStokesPromotedIsFalse :
  clayNavierStokesPromoted ≡ false
clayNavierStokesPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

------------------------------------------------------------------------
-- Fail-closed criterion policy.

data GreatCircleCriterionGate : Set where
  gateExternalTheoremRecorded :
    GreatCircleCriterionGate

  gateAuthorityTokenAccepted :
    GreatCircleCriterionGate

  gateZeroModeAvoidanceClassified :
    GreatCircleCriterionGate

  gateConeTrapBinding :
    GreatCircleCriterionGate

  gateDirectionSetMeasureTransfer :
    GreatCircleCriterionGate

  gateQuantitativeMassOutsideZeroModes :
    GreatCircleCriterionGate

  gateLeakageResidualClosure :
    GreatCircleCriterionGate

  gateClayPromotion :
    GreatCircleCriterionGate

canonicalGreatCircleCriterionGates :
  List GreatCircleCriterionGate
canonicalGreatCircleCriterionGates =
  gateExternalTheoremRecorded
  ∷ gateAuthorityTokenAccepted
  ∷ gateZeroModeAvoidanceClassified
  ∷ gateConeTrapBinding
  ∷ gateDirectionSetMeasureTransfer
  ∷ gateQuantitativeMassOutsideZeroModes
  ∷ gateLeakageResidualClosure
  ∷ gateClayPromotion
  ∷ []

greatCircleCriterionGateCount : Nat
greatCircleCriterionGateCount =
  listLength canonicalGreatCircleCriterionGates

greatCircleCriterionGateCountIs8 :
  greatCircleCriterionGateCount ≡ 8
greatCircleCriterionGateCountIs8 =
  refl

data GreatCircleGateDisposition : Set where
  gateRecordedAsExternalDeterministicBoundary :
    GreatCircleCriterionGate →
    GreatCircleGateDisposition

  gateClosedUntilAuthorityTokenNormalized :
    GreatCircleCriterionGate →
    GreatCircleCriterionBlocker →
    GreatCircleGateDisposition

  gateClosedUntilZeroModeGeometrySupplied :
    GreatCircleCriterionGate →
    GreatCircleCriterionBlocker →
    GreatCircleGateDisposition

  gateClosedUntilMeasureTransferSupplied :
    GreatCircleCriterionGate →
    GreatCircleCriterionBlocker →
    GreatCircleCriterionBlocker →
    GreatCircleGateDisposition

  gateClosedUntilLeakageResidualSupplied :
    GreatCircleCriterionGate →
    GreatCircleCriterionBlocker →
    GreatCircleCriterionBlocker →
    GreatCircleCriterionBlocker →
    GreatCircleGateDisposition

  gateClosedToClayPromotion :
    GreatCircleCriterionGate →
    GreatCircleCriterionBlocker →
    GreatCircleGateDisposition

greatCircleCriterionGateDisposition :
  GreatCircleCriterionGate →
  GreatCircleGateDisposition
greatCircleCriterionGateDisposition gateExternalTheoremRecorded =
  gateRecordedAsExternalDeterministicBoundary
    gateExternalTheoremRecorded
greatCircleCriterionGateDisposition gateAuthorityTokenAccepted =
  gateClosedUntilAuthorityTokenNormalized
    gateAuthorityTokenAccepted
    missingAuthorityTokenNormalization
greatCircleCriterionGateDisposition gateZeroModeAvoidanceClassified =
  gateClosedUntilZeroModeGeometrySupplied
    gateZeroModeAvoidanceClassified
    missingZeroModeGreatCircleAvoidanceClassification
greatCircleCriterionGateDisposition gateConeTrapBinding =
  gateClosedUntilZeroModeGeometrySupplied
    gateConeTrapBinding
    missingConeTrapToZeroModeTrapBinding
greatCircleCriterionGateDisposition gateDirectionSetMeasureTransfer =
  gateClosedUntilMeasureTransferSupplied
    gateDirectionSetMeasureTransfer
    missingDirectionSetIToMicrolocalMeasureTransfer
    missingQuantitativePositiveMassOutsideZeroModes
greatCircleCriterionGateDisposition gateQuantitativeMassOutsideZeroModes =
  gateClosedUntilMeasureTransferSupplied
    gateQuantitativeMassOutsideZeroModes
    missingQuantitativePositiveMassOutsideZeroModes
    missingDirectionSetIToMicrolocalMeasureTransfer
greatCircleCriterionGateDisposition gateLeakageResidualClosure =
  gateClosedUntilLeakageResidualSupplied
    gateLeakageResidualClosure
    missingLeakageAwayFromZeroModes
    missingNSCriticalResidualNonPositive
    missingFullLocalDefectMonotonicity
greatCircleCriterionGateDisposition gateClayPromotion =
  gateClosedToClayPromotion
    gateClayPromotion
    clayNavierStokesPromotionClosed

record NSLeiRenTianGreatCircleCriterionFailClosedReceipt : Setω where
  constructor nsLeiRenTianGreatCircleCriterionFailClosedReceipt
  field
    criterionGates :
      List GreatCircleCriterionGate
    criterionGatesAreCanonical :
      criterionGates ≡ canonicalGreatCircleCriterionGates
    criterionGateCount :
      Nat
    criterionGateCountIsCanonical :
      criterionGateCount ≡ greatCircleCriterionGateCount
    criterionGateCountProof :
      criterionGateCount ≡ 8

    externalTheoremGateDisposition :
      greatCircleCriterionGateDisposition gateExternalTheoremRecorded
      ≡
      gateRecordedAsExternalDeterministicBoundary
        gateExternalTheoremRecorded
    authorityTokenGateDisposition :
      greatCircleCriterionGateDisposition gateAuthorityTokenAccepted
      ≡
      gateClosedUntilAuthorityTokenNormalized
        gateAuthorityTokenAccepted
        missingAuthorityTokenNormalization
    zeroModeAvoidanceGateDisposition :
      greatCircleCriterionGateDisposition gateZeroModeAvoidanceClassified
      ≡
      gateClosedUntilZeroModeGeometrySupplied
        gateZeroModeAvoidanceClassified
        missingZeroModeGreatCircleAvoidanceClassification
    coneTrapBindingGateDisposition :
      greatCircleCriterionGateDisposition gateConeTrapBinding
      ≡
      gateClosedUntilZeroModeGeometrySupplied
        gateConeTrapBinding
        missingConeTrapToZeroModeTrapBinding
    directionSetTransferGateDisposition :
      greatCircleCriterionGateDisposition gateDirectionSetMeasureTransfer
      ≡
      gateClosedUntilMeasureTransferSupplied
        gateDirectionSetMeasureTransfer
        missingDirectionSetIToMicrolocalMeasureTransfer
        missingQuantitativePositiveMassOutsideZeroModes
    quantitativeMassGateDisposition :
      greatCircleCriterionGateDisposition gateQuantitativeMassOutsideZeroModes
      ≡
      gateClosedUntilMeasureTransferSupplied
        gateQuantitativeMassOutsideZeroModes
        missingQuantitativePositiveMassOutsideZeroModes
        missingDirectionSetIToMicrolocalMeasureTransfer
    leakageResidualGateDisposition :
      greatCircleCriterionGateDisposition gateLeakageResidualClosure
      ≡
      gateClosedUntilLeakageResidualSupplied
        gateLeakageResidualClosure
        missingLeakageAwayFromZeroModes
        missingNSCriticalResidualNonPositive
        missingFullLocalDefectMonotonicity
    clayPromotionGateDisposition :
      greatCircleCriterionGateDisposition gateClayPromotion
      ≡
      gateClosedToClayPromotion
        gateClayPromotion
        clayNavierStokesPromotionClosed

    theoremRecordedStillTrue :
      ExternalDeterministicTheoremBoundaryRecorded ≡ true
    criterionTypedStillTrue :
      GreatCircleHittingCriterionTyped ≡ true
    doubleConeTypedStillTrue :
      DoubleConeAvoidanceCriterionTyped ≡ true
    internalFormalizationStillFalse :
      LeiRenTianTheoremInternallyFormalized ≡ false
    authorityTokenStillFalse :
      LeiRenTianAuthorityTokenAccepted ≡ false
    zeroModeAvoidanceStillFalse :
      ZeroModeGreatCircleAvoidanceClassified ≡ false
    coneTrapBindingStillFalse :
      ConeTrapToZeroModeTrapBindingProved ≡ false
    directionSetTransferStillFalse :
      DirectionSetIToMicrolocalMeasureTransferProved ≡ false
    quantitativeMassStillFalse :
      QuantitativePositiveMassOutsideZeroModesProved ≡ false
    leakageStillFalse :
      LeakageAwayFromZeroModesProved ≡ false
    residualStillFalse :
      NSCriticalResidualNonPositive ≡ false
    monotonicityStillFalse :
      FullLocalDefectMonotonicity ≡ false
    mechanismExhaustionStillFalse :
      MechanismExhaustionForFullClayNS ≡ false
    clayPromotionStillFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionStillFalse :
      terminalPromotion ≡ false
    promotionWitnesses :
      List GreatCircleCriterionPromotion
    promotionWitnessesAreEmpty :
      promotionWitnesses ≡ []

open NSLeiRenTianGreatCircleCriterionFailClosedReceipt public

canonicalNSLeiRenTianGreatCircleCriterionFailClosedReceipt :
  NSLeiRenTianGreatCircleCriterionFailClosedReceipt
canonicalNSLeiRenTianGreatCircleCriterionFailClosedReceipt =
  nsLeiRenTianGreatCircleCriterionFailClosedReceipt
    canonicalGreatCircleCriterionGates
    refl
    greatCircleCriterionGateCount
    refl
    greatCircleCriterionGateCountIs8
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
    []
    refl

------------------------------------------------------------------------
-- ORCSLPGF.

organizationString : String
organizationString =
  "O: Worker 1 owns NSLeiRenTianGreatCircleCriterionBoundary as a single Agda authority-boundary lane."

requirementString : String
requirementString =
  "R: Encode the conservative Lei-Ren-Tian criterion: singular high-vorticity direction set I hits every great circle; double-cone avoidance is a regularity criterion."

codeArtifactString : String
codeArtifactString =
  "C: The module exports source metadata, direction/great-circle/cone carriers, contrapositive boundary, zero-mode trap hooks, support/blocker/status rows, fail-closed gates, false promotion guards, ORCSLPGF, and canonical receipts."

stateString : String
stateString =
  "S: Zero-mode classification, rank-one defect formula, and microlocal defect-mass boundary are imported; Lei-Ren-Tian is external and quantitative measure transfer remains missing."

latticeString : String
latticeString =
  "L: external great-circle criterion -> cone/double-cone regularity boundary -> zero-mode trap exclusion target -> quantitative microlocal transfer -> leakage/residual/Clay blockers."

proposalString : String
proposalString =
  "P: Promote only the checked criterion-boundary surface; leave internal theorem formalization, measure transfer, residual closure, Clay NS, and terminal promotion false."

governanceString : String
governanceString =
  "G: External theorem metadata is recorded; no internal Lei-Ren-Tian proof, no authority-token acceptance, no quantitative measure transfer, no Clay promotion."

gapString : String
gapString =
  "F: Remaining gaps are zero-mode great-circle avoidance classification, cone-trap binding, direction-set-I to microlocal-measure transfer, positive mass outside zero modes, sector switching compactness, leakage, and NS residual closure."

record NSLeiRenTianGreatCircleCriterionORCSLPGF : Set where
  constructor nsLeiRenTianGreatCircleCriterionORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ organizationString
    R : String
    RIsCanonical : R ≡ requirementString
    C : String
    CIsCanonical : C ≡ codeArtifactString
    S : String
    SIsCanonical : S ≡ stateString
    L : String
    LIsCanonical : L ≡ latticeString
    P : String
    PIsCanonical : P ≡ proposalString
    G : String
    GIsCanonical : G ≡ governanceString
    F : String
    FIsCanonical : F ≡ gapString

open NSLeiRenTianGreatCircleCriterionORCSLPGF public

canonicalNSLeiRenTianGreatCircleCriterionORCSLPGF :
  NSLeiRenTianGreatCircleCriterionORCSLPGF
canonicalNSLeiRenTianGreatCircleCriterionORCSLPGF =
  nsLeiRenTianGreatCircleCriterionORCSLPGF
    organizationString
    refl
    requirementString
    refl
    codeArtifactString
    refl
    stateString
    refl
    latticeString
    refl
    proposalString
    refl
    governanceString
    refl
    gapString
    refl

------------------------------------------------------------------------
-- Canonical receipt.

record NSLeiRenTianGreatCircleCriterionBoundaryReceipt : Setω where
  constructor nsLeiRenTianGreatCircleCriterionBoundaryReceipt
  field
    gateName :
      String
    gateNameIsCanonical :
      gateName ≡ "NSLeiRenTianGreatCircleCriterionBoundary"

    sourceArxivId :
      String
    sourceArxivIdIsCanonical :
      sourceArxivId ≡ leiRenTianArxivId
    sourceTitle :
      String
    sourceTitleIsCanonical :
      sourceTitle ≡ leiRenTianPaperTitle
    greatCircleClaim :
      String
    greatCircleClaimIsCanonical :
      greatCircleClaim ≡ leiRenTianGreatCircleClaim
    coneCriterionClaim :
      String
    coneCriterionClaimIsCanonical :
      coneCriterionClaim ≡ leiRenTianConeCriterionClaim
    boundaryUse :
      String
    boundaryUseIsCanonical :
      boundaryUse ≡ leiRenTianBoundaryUse

    sourceRows :
      List LeiRenTianCriterionSourceRow
    sourceRowsAreCanonical :
      sourceRows ≡ canonicalLeiRenTianCriterionSourceRows
    sourceRowCount :
      Nat
    sourceRowCountIsCanonical :
      sourceRowCount ≡ leiRenTianCriterionSourceRowCount
    sourceRowCountProof :
      sourceRowCount ≡ 6

    zeroModeClassificationAnchor :
      ZeroMode.NSZeroModeSetClassificationBoundaryReceipt
    zeroModeClassificationRecorded :
      ZeroMode.NSZeroModeSetClassificationBoundaryRecorded ≡ true
    zeroModeClassificationAuthorityStillFalse :
      ZeroMode.LeiRenTianAuthorityAccepted ≡ false
    zeroModeClassificationClayStillFalse :
      ZeroMode.clayNavierStokesPromoted ≡ false

    rankOneAnchor :
      RankOne.NSRankOneProjectionCommutatorFormula
    rankOneCorrectedFormulaRecorded :
      RankOne.correctedFormulaRecorded rankOneAnchor ≡ true
    rankOneClayStillFalse :
      RankOne.navierStokesClayPromoted rankOneAnchor ≡ false

    microlocalAnchor :
      Micro.NSMicrolocalDefectMassConstructionBoundaryReceipt
    microlocalBoundaryRecorded :
      Micro.NSMicrolocalDefectMassConstructionBoundaryRecorded ≡ true
    microlocalMassStillFalse :
      Micro.MicrolocalDefectMassConstructed ≡ false

    sphereDirectionCarrier :
      SphereDirectionCarrier
    sphereDirectionCarrierIsCanonical :
      sphereDirectionCarrier ≡ canonicalSphereDirectionCarrier
    highVorticityDirectionSet :
      HighVorticityDirectionSet
    highVorticityDirectionSetIsCanonical :
      highVorticityDirectionSet ≡ canonicalHighVorticityDirectionSet
    greatCircleCarrier :
      GreatCircleCarrier
    greatCircleCarrierIsCanonical :
      greatCircleCarrier ≡ canonicalGreatCircleCarrier
    greatCircleHittingProperty :
      GreatCircleHittingProperty
    greatCircleHittingPropertyIsCanonical :
      greatCircleHittingProperty ≡ canonicalGreatCircleHittingProperty
    coneAvoidanceProperty :
      ConeAvoidanceProperty
    coneAvoidancePropertyIsCanonical :
      coneAvoidanceProperty ≡ canonicalConeAvoidanceProperty
    singularityNecessaryCondition :
      SingularityNecessaryConditionBoundary
    singularityNecessaryConditionIsCanonical :
      singularityNecessaryCondition
      ≡
      canonicalSingularityNecessaryConditionBoundary
    regularityConsequence :
      RegularityConsequenceBoundary
    regularityConsequenceIsCanonical :
      regularityConsequence
      ≡
      canonicalRegularityConsequenceBoundary
    contrapositiveCriterionBoundary :
      GreatCircleConeCriterionEquivalenceBoundary
    contrapositiveCriterionBoundaryIsCanonical :
      contrapositiveCriterionBoundary
      ≡
      canonicalGreatCircleConeCriterionEquivalenceBoundary

    zeroModeTrapStatuses :
      List ZeroModeTrapGeometryStatus
    zeroModeTrapStatusesAreCanonical :
      zeroModeTrapStatuses ≡ canonicalZeroModeTrapStatuses
    receiptZeroModeTrapStatusCount :
      Nat
    receiptZeroModeTrapStatusCountIsCanonical :
      receiptZeroModeTrapStatusCount ≡ zeroModeTrapStatusCount
    zeroModeTrapStatusCountProof :
      receiptZeroModeTrapStatusCount ≡ 2
    radialTrapExclusionBoundary :
      GreatCircleZeroModeTrapExclusionBoundary
    radialTrapExclusionBoundaryIsCanonical :
      radialTrapExclusionBoundary
      ≡
      canonicalRadialTrapExclusionBoundary
    tangentialTrapExclusionBoundary :
      GreatCircleZeroModeTrapExclusionBoundary
    tangentialTrapExclusionBoundaryIsCanonical :
      tangentialTrapExclusionBoundary
      ≡
      canonicalTangentialTrapExclusionBoundary

    supportRows :
      List GreatCircleCriterionSupportRow
    supportRowsAreCanonical :
      supportRows ≡ canonicalGreatCircleCriterionSupportRows
    supportRowCount :
      Nat
    supportRowCountIsCanonical :
      supportRowCount ≡ greatCircleCriterionSupportRowCount
    supportRowCountProof :
      supportRowCount ≡ 10

    blockerRows :
      List GreatCircleCriterionBlocker
    blockerRowsAreCanonical :
      blockerRows ≡ canonicalGreatCircleCriterionBlockers
    blockerRowCount :
      Nat
    blockerRowCountIsCanonical :
      blockerRowCount ≡ greatCircleCriterionBlockerCount
    blockerRowCountProof :
      blockerRowCount ≡ 12

    statusRows :
      List GreatCircleCriterionStatusRow
    statusRowsAreCanonical :
      statusRows ≡ canonicalGreatCircleCriterionStatusRows
    statusRowCount :
      Nat
    statusRowCountIsCanonical :
      statusRowCount ≡ greatCircleCriterionStatusRowCount
    statusRowCountProof :
      statusRowCount ≡ 9

    boundaryRecorded :
      NSLeiRenTianGreatCircleCriterionBoundaryRecorded ≡ true
    externalTheoremBoundaryRecorded :
      ExternalDeterministicTheoremBoundaryRecorded ≡ true
    greatCircleHittingCriterionTyped :
      GreatCircleHittingCriterionTyped ≡ true
    doubleConeAvoidanceCriterionTyped :
      DoubleConeAvoidanceCriterionTyped ≡ true
    contrapositiveEquivalenceBoundaryTyped :
      ContrapositiveEquivalenceBoundaryTyped ≡ true
    zeroModeClassificationAnchorImported :
      ZeroModeClassificationAnchorImported ≡ true
    rankOneFormulaAnchorImported :
      RankOneFormulaAnchorImported ≡ true
    microlocalBoundaryAnchorImported :
      MicrolocalDefectMassBoundaryAnchorImported ≡ true

    leiRenTianTheoremInternallyFormalizedFalse :
      LeiRenTianTheoremInternallyFormalized ≡ false
    leiRenTianAuthorityTokenAcceptedFalse :
      LeiRenTianAuthorityTokenAccepted ≡ false
    zeroModeGreatCircleAvoidanceClassifiedFalse :
      ZeroModeGreatCircleAvoidanceClassified ≡ false
    coneTrapToZeroModeTrapBindingProvedFalse :
      ConeTrapToZeroModeTrapBindingProved ≡ false
    directionSetIToMicrolocalMeasureTransferProvedFalse :
      DirectionSetIToMicrolocalMeasureTransferProved ≡ false
    quantitativePositiveMassOutsideZeroModesProvedFalse :
      QuantitativePositiveMassOutsideZeroModesProved ≡ false
    sectorSwitchingCompactnessProvedFalse :
      SectorSwitchingCompactnessProved ≡ false
    leakageAwayFromZeroModesProvedFalse :
      LeakageAwayFromZeroModesProved ≡ false
    microlocalDefectMassConstructedFalse :
      MicrolocalDefectMassConstructed ≡ false
    nsCriticalResidualNonPositiveFalse :
      NSCriticalResidualNonPositive ≡ false
    fullLocalDefectMonotonicityFalse :
      FullLocalDefectMonotonicity ≡ false
    mechanismExhaustionForFullClayNSFalse :
      MechanismExhaustionForFullClayNS ≡ false
    fullClayNSSolvedSnakeFalse :
      full_clay_ns_solved ≡ false
    fullClayNSSolvedFalse :
      fullClayNSSolved ≡ false
    clayNavierStokesPromotedFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false

    promotionFlags :
      List GreatCircleCriterionPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    failClosedReceipt :
      NSLeiRenTianGreatCircleCriterionFailClosedReceipt

    orcslpgf :
      NSLeiRenTianGreatCircleCriterionORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSLeiRenTianGreatCircleCriterionORCSLPGF

open NSLeiRenTianGreatCircleCriterionBoundaryReceipt public

canonicalNSLeiRenTianGreatCircleCriterionBoundaryReceipt :
  NSLeiRenTianGreatCircleCriterionBoundaryReceipt
canonicalNSLeiRenTianGreatCircleCriterionBoundaryReceipt =
  nsLeiRenTianGreatCircleCriterionBoundaryReceipt
    "NSLeiRenTianGreatCircleCriterionBoundary"
    refl
    leiRenTianArxivId
    refl
    leiRenTianPaperTitle
    refl
    leiRenTianGreatCircleClaim
    refl
    leiRenTianConeCriterionClaim
    refl
    leiRenTianBoundaryUse
    refl
    canonicalLeiRenTianCriterionSourceRows
    refl
    leiRenTianCriterionSourceRowCount
    refl
    leiRenTianCriterionSourceRowCountIs6
    ZeroMode.canonicalNSZeroModeSetClassificationBoundaryReceipt
    refl
    refl
    refl
    RankOne.canonicalNSRankOneProjectionCommutatorFormula
    refl
    refl
    Micro.canonicalNSMicrolocalDefectMassConstructionBoundaryReceipt
    refl
    refl
    canonicalSphereDirectionCarrier
    refl
    canonicalHighVorticityDirectionSet
    refl
    canonicalGreatCircleCarrier
    refl
    canonicalGreatCircleHittingProperty
    refl
    canonicalConeAvoidanceProperty
    refl
    canonicalSingularityNecessaryConditionBoundary
    refl
    canonicalRegularityConsequenceBoundary
    refl
    canonicalGreatCircleConeCriterionEquivalenceBoundary
    refl
    canonicalZeroModeTrapStatuses
    refl
    zeroModeTrapStatusCount
    refl
    zeroModeTrapStatusCountIs2
    canonicalRadialTrapExclusionBoundary
    refl
    canonicalTangentialTrapExclusionBoundary
    refl
    canonicalGreatCircleCriterionSupportRows
    refl
    greatCircleCriterionSupportRowCount
    refl
    greatCircleCriterionSupportRowCountIs10
    canonicalGreatCircleCriterionBlockers
    refl
    greatCircleCriterionBlockerCount
    refl
    greatCircleCriterionBlockerCountIs12
    canonicalGreatCircleCriterionStatusRows
    refl
    greatCircleCriterionStatusRowCount
    refl
    greatCircleCriterionStatusRowCountIs9
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
    refl
    []
    refl
    canonicalNSLeiRenTianGreatCircleCriterionFailClosedReceipt
    canonicalNSLeiRenTianGreatCircleCriterionORCSLPGF
    refl
