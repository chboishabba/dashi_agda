module DASHI.Physics.Closure.NSPhysicalAngularMeasureConstructionBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSAbelTriadicDefectMeasureConstructionBoundary
  as AbelDefect
import DASHI.Physics.Closure.NSLeiRenTianGreatCircleCriterionBoundary
  as LRT
import DASHI.Physics.Closure.NSLeiRenTianOutputSupportTransferBoundary
  as OutputSupport
import DASHI.Physics.Closure.NSTriadicAngularDefectSheafLeakageBoundary
  as Sheaf

------------------------------------------------------------------------
-- NS A4 child boundary: physical angular measure construction.
--
-- Analytic target:
--
--   localized CKN/Type-I vorticity packets
--     -> normalized physical vorticity-direction angular measure on S^2
--     -> Lei-Ren-Tian great-circle hitting carrier
--     -> input for A4 physical-to-Fourier output coupling.
--
-- This module records a proof contract for the first A4 rung only.  It
-- does not prove Lei-Ren-Tian internally, does not prove quantitative
-- density equivalence with surface measure, does not transfer the measure
-- to Fourier output directions, does not prove the A4 coupling theorem, and
-- does not promote Navier-Stokes Clay.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Imported support anchors.

leiRenTianCriterionBoundaryReference : String
leiRenTianCriterionBoundaryReference =
  "DASHI.Physics.Closure.NSLeiRenTianGreatCircleCriterionBoundary"

abelDefectMeasureBoundaryReference : String
abelDefectMeasureBoundaryReference =
  "DASHI.Physics.Closure.NSAbelTriadicDefectMeasureConstructionBoundary"

outputSupportTransferBoundaryReference : String
outputSupportTransferBoundaryReference =
  "DASHI.Physics.Closure.NSLeiRenTianOutputSupportTransferBoundary"

triadicSheafLeakageBoundaryReference : String
triadicSheafLeakageBoundaryReference =
  "DASHI.Physics.Closure.NSTriadicAngularDefectSheafLeakageBoundary"

leiRenTianCriterionBoundaryImported : Bool
leiRenTianCriterionBoundaryImported =
  true

abelDefectMeasureBoundaryImported : Bool
abelDefectMeasureBoundaryImported =
  true

outputSupportTransferBoundaryImported : Bool
outputSupportTransferBoundaryImported =
  true

triadicSheafLeakageBoundaryImported : Bool
triadicSheafLeakageBoundaryImported =
  true

record ImportedPhysicalAngularMeasureSupport : Set where
  field
    lrtHighVorticityDirectionSet :
      LRT.HighVorticityDirectionSet
    lrtHighVorticityDirectionSetIsCanonical :
      lrtHighVorticityDirectionSet ≡ LRT.canonicalHighVorticityDirectionSet
    lrtGreatCircleHitting :
      LRT.GreatCircleHittingProperty
    lrtGreatCircleHittingIsCanonical :
      lrtGreatCircleHitting ≡ LRT.canonicalGreatCircleHittingProperty
    abelBlowupProfile :
      AbelDefect.SuitableWeakBlowupProfileCarrier
    abelBlowupProfileIsCanonical :
      abelBlowupProfile ≡ AbelDefect.canonicalBlowupProfile
    abelParabolicScale :
      AbelDefect.ParabolicScaleCarrier
    abelParabolicScaleIsCanonical :
      abelParabolicScale ≡ AbelDefect.canonicalParabolicScale
    outputPhysicalRichness :
      OutputSupport.PhysicalVorticityDirectionRichness
    outputPhysicalRichnessIsCanonical :
      outputPhysicalRichness
        ≡ OutputSupport.canonicalPhysicalVorticityDirectionRichness
    sheafLRTOutputCondition :
      Sheaf.LeiRenTianOutputGreatCircleCondition
    sheafLRTOutputConditionIsCanonical :
      sheafLRTOutputCondition ≡ Sheaf.canonicalLRTOutputCondition
    lrtCriterionImportedTrue :
      leiRenTianCriterionBoundaryImported ≡ true
    abelDefectImportedTrue :
      abelDefectMeasureBoundaryImported ≡ true
    outputSupportImportedTrue :
      outputSupportTransferBoundaryImported ≡ true
    triadicSheafImportedTrue :
      triadicSheafLeakageBoundaryImported ≡ true

canonicalImportedPhysicalAngularMeasureSupport :
  ImportedPhysicalAngularMeasureSupport
canonicalImportedPhysicalAngularMeasureSupport =
  record
    { lrtHighVorticityDirectionSet =
        LRT.canonicalHighVorticityDirectionSet
    ; lrtHighVorticityDirectionSetIsCanonical =
        refl
    ; lrtGreatCircleHitting =
        LRT.canonicalGreatCircleHittingProperty
    ; lrtGreatCircleHittingIsCanonical =
        refl
    ; abelBlowupProfile =
        AbelDefect.canonicalBlowupProfile
    ; abelBlowupProfileIsCanonical =
        refl
    ; abelParabolicScale =
        AbelDefect.canonicalParabolicScale
    ; abelParabolicScaleIsCanonical =
        refl
    ; outputPhysicalRichness =
        OutputSupport.canonicalPhysicalVorticityDirectionRichness
    ; outputPhysicalRichnessIsCanonical =
        refl
    ; sheafLRTOutputCondition =
        Sheaf.canonicalLRTOutputCondition
    ; sheafLRTOutputConditionIsCanonical =
        refl
    ; lrtCriterionImportedTrue =
        refl
    ; abelDefectImportedTrue =
        refl
    ; outputSupportImportedTrue =
        refl
    ; triadicSheafImportedTrue =
        refl
    }

------------------------------------------------------------------------
-- Physical packet and angular-measure carriers.

data LocalizedCKNCylinderCarrier : Set where
  parabolicCylinderQrAroundCandidateSingularity :
    AbelDefect.ParabolicScaleCarrier →
    LocalizedCKNCylinderCarrier

data TypeIVorticityPacketCarrier : Set where
  localizedTypeIVorticityPacket :
    AbelDefect.SuitableWeakBlowupProfileCarrier →
    LocalizedCKNCylinderCarrier →
    TypeIVorticityPacketCarrier

data NonzeroVorticityDirectionFieldCarrier : Set where
  normalizedOmegaOverNonzeroVorticitySet :
    TypeIVorticityPacketCarrier →
    LRT.SphereDirectionCarrier →
    NonzeroVorticityDirectionFieldCarrier

data HighVorticityThresholdCarrier : Set where
  cknScaleInvariantHighVorticityThreshold :
    LocalizedCKNCylinderCarrier →
    HighVorticityThresholdCarrier

data HighVorticityPacketSetCarrier : Set where
  thresholdedHighVorticityPacketSet :
    TypeIVorticityPacketCarrier →
    HighVorticityThresholdCarrier →
    LRT.HighVorticityDirectionSet →
    HighVorticityPacketSetCarrier

data PhysicalAngularMeasureCarrier : Set where
  pushforwardVorticityEnergyByDirection :
    HighVorticityPacketSetCarrier →
    NonzeroVorticityDirectionFieldCarrier →
    LRT.GreatCircleHittingProperty →
    PhysicalAngularMeasureCarrier

data PhysicalAngularMeasureNormalizationCarrier : Set where
  normalizeByLocalizedEnstrophyMass :
    PhysicalAngularMeasureCarrier →
    AbelDefect.CriticalDissipationCarrier →
    PhysicalAngularMeasureNormalizationCarrier

data PhysicalAngularMeasureGreatCircleSupportCarrier : Set where
  lrtGreatCircleSupportForPhysicalAngularMeasure :
    PhysicalAngularMeasureCarrier →
    LRT.GreatCircleHittingProperty →
    OutputSupport.PhysicalVorticityDirectionRichness →
    PhysicalAngularMeasureGreatCircleSupportCarrier

canonicalLocalizedCKNCylinder :
  LocalizedCKNCylinderCarrier
canonicalLocalizedCKNCylinder =
  parabolicCylinderQrAroundCandidateSingularity
    AbelDefect.canonicalParabolicScale

canonicalTypeIVorticityPacket :
  TypeIVorticityPacketCarrier
canonicalTypeIVorticityPacket =
  localizedTypeIVorticityPacket
    AbelDefect.canonicalBlowupProfile
    canonicalLocalizedCKNCylinder

canonicalNonzeroVorticityDirectionField :
  NonzeroVorticityDirectionFieldCarrier
canonicalNonzeroVorticityDirectionField =
  normalizedOmegaOverNonzeroVorticitySet
    canonicalTypeIVorticityPacket
    LRT.canonicalSphereDirectionCarrier

canonicalHighVorticityThreshold :
  HighVorticityThresholdCarrier
canonicalHighVorticityThreshold =
  cknScaleInvariantHighVorticityThreshold
    canonicalLocalizedCKNCylinder

canonicalHighVorticityPacketSet :
  HighVorticityPacketSetCarrier
canonicalHighVorticityPacketSet =
  thresholdedHighVorticityPacketSet
    canonicalTypeIVorticityPacket
    canonicalHighVorticityThreshold
    LRT.canonicalHighVorticityDirectionSet

canonicalPhysicalAngularMeasure :
  PhysicalAngularMeasureCarrier
canonicalPhysicalAngularMeasure =
  pushforwardVorticityEnergyByDirection
    canonicalHighVorticityPacketSet
    canonicalNonzeroVorticityDirectionField
    LRT.canonicalGreatCircleHittingProperty

canonicalPhysicalAngularMeasureNormalization :
  PhysicalAngularMeasureNormalizationCarrier
canonicalPhysicalAngularMeasureNormalization =
  normalizeByLocalizedEnstrophyMass
    canonicalPhysicalAngularMeasure
    AbelDefect.canonicalDissipationDr

canonicalPhysicalAngularMeasureGreatCircleSupport :
  PhysicalAngularMeasureGreatCircleSupportCarrier
canonicalPhysicalAngularMeasureGreatCircleSupport =
  lrtGreatCircleSupportForPhysicalAngularMeasure
    canonicalPhysicalAngularMeasure
    LRT.canonicalGreatCircleHittingProperty
    OutputSupport.canonicalPhysicalVorticityDirectionRichness

------------------------------------------------------------------------
-- Construction obligations.

data PhysicalAngularMeasureConstructionObligation : Set where
  selectCandidateCKNParabolicCylinder :
    PhysicalAngularMeasureConstructionObligation
  restrictTypeIBlowupProfileToLocalizedVorticityPacket :
    PhysicalAngularMeasureConstructionObligation
  removeZeroVorticityNullSetBeforeDirectionNormalization :
    PhysicalAngularMeasureConstructionObligation
  normalizeOmegaToSphereDirectionField :
    PhysicalAngularMeasureConstructionObligation
  chooseScaleInvariantHighVorticityThreshold :
    PhysicalAngularMeasureConstructionObligation
  pushForwardLocalizedEnstrophyByDirectionMap :
    PhysicalAngularMeasureConstructionObligation
  normalizeByLocalizedEnstrophyOrCriticalDissipation :
    PhysicalAngularMeasureConstructionObligation
  attachLeiRenTianGreatCircleHittingAuthority :
    PhysicalAngularMeasureConstructionObligation
  proveTightnessUnderShrinkingParabolicScales :
    PhysicalAngularMeasureConstructionObligation
  preserveQualitativeSupportAfterCutoffAndThreshold :
    PhysicalAngularMeasureConstructionObligation
  exposeOutputSupportTransferInputCarrier :
    PhysicalAngularMeasureConstructionObligation

canonicalPhysicalAngularMeasureConstructionObligations :
  List PhysicalAngularMeasureConstructionObligation
canonicalPhysicalAngularMeasureConstructionObligations =
  selectCandidateCKNParabolicCylinder
  ∷ restrictTypeIBlowupProfileToLocalizedVorticityPacket
  ∷ removeZeroVorticityNullSetBeforeDirectionNormalization
  ∷ normalizeOmegaToSphereDirectionField
  ∷ chooseScaleInvariantHighVorticityThreshold
  ∷ pushForwardLocalizedEnstrophyByDirectionMap
  ∷ normalizeByLocalizedEnstrophyOrCriticalDissipation
  ∷ attachLeiRenTianGreatCircleHittingAuthority
  ∷ proveTightnessUnderShrinkingParabolicScales
  ∷ preserveQualitativeSupportAfterCutoffAndThreshold
  ∷ exposeOutputSupportTransferInputCarrier
  ∷ []

physicalAngularMeasureConstructionObligationCount : Nat
physicalAngularMeasureConstructionObligationCount =
  listLength canonicalPhysicalAngularMeasureConstructionObligations

physicalAngularMeasureConstructionObligationCountIs11 :
  physicalAngularMeasureConstructionObligationCount ≡ 11
physicalAngularMeasureConstructionObligationCountIs11 =
  refl

data PhysicalAngularMeasurePremise : Set where
  typeIBoundOnRescaledProfile :
    PhysicalAngularMeasurePremise
  localizedCKNEnstrophyFinite :
    PhysicalAngularMeasurePremise
  nonzeroVorticityDirectionDefinedModuloNullSet :
    PhysicalAngularMeasurePremise
  lrtExternalGreatCircleAuthorityAvailable :
    PhysicalAngularMeasurePremise
  parabolicCutoffDoesNotEraseHighVorticitySupport :
    PhysicalAngularMeasurePremise
  thresholdChoiceCompatibleWithLRTDirectionSet :
    PhysicalAngularMeasurePremise
  weakStarCompactnessForAngularProbabilityMeasures :
    PhysicalAngularMeasurePremise
  abelWindowCompatibleWithPhysicalPacketScale :
    PhysicalAngularMeasurePremise

canonicalPhysicalAngularMeasurePremises :
  List PhysicalAngularMeasurePremise
canonicalPhysicalAngularMeasurePremises =
  typeIBoundOnRescaledProfile
  ∷ localizedCKNEnstrophyFinite
  ∷ nonzeroVorticityDirectionDefinedModuloNullSet
  ∷ lrtExternalGreatCircleAuthorityAvailable
  ∷ parabolicCutoffDoesNotEraseHighVorticitySupport
  ∷ thresholdChoiceCompatibleWithLRTDirectionSet
  ∷ weakStarCompactnessForAngularProbabilityMeasures
  ∷ abelWindowCompatibleWithPhysicalPacketScale
  ∷ []

physicalAngularMeasurePremiseCount : Nat
physicalAngularMeasurePremiseCount =
  listLength canonicalPhysicalAngularMeasurePremises

physicalAngularMeasurePremiseCountIs8 :
  physicalAngularMeasurePremiseCount ≡ 8
physicalAngularMeasurePremiseCountIs8 =
  refl

data PhysicalAngularMeasureBlocker : Set where
  missingQuantitativeDensityEquivalenceToSurfaceMeasure :
    PhysicalAngularMeasureBlocker
  missingCutoffThresholdMassRetentionProof :
    PhysicalAngularMeasureBlocker
  missingPhysicalToFourierAngularCoupling :
    PhysicalAngularMeasureBlocker
  missingOutputDirectionSupportLift :
    PhysicalAngularMeasureBlocker
  missingPDEAbelMeasureSupportTheorem :
    PhysicalAngularMeasureBlocker
  missingTriadicCompensatedLeakageIdentity :
    PhysicalAngularMeasureBlocker
  missingCKNBKMClosure :
    PhysicalAngularMeasureBlocker
  missingClayPromotion :
    PhysicalAngularMeasureBlocker

canonicalPhysicalAngularMeasureBlockers :
  List PhysicalAngularMeasureBlocker
canonicalPhysicalAngularMeasureBlockers =
  missingQuantitativeDensityEquivalenceToSurfaceMeasure
  ∷ missingCutoffThresholdMassRetentionProof
  ∷ missingPhysicalToFourierAngularCoupling
  ∷ missingOutputDirectionSupportLift
  ∷ missingPDEAbelMeasureSupportTheorem
  ∷ missingTriadicCompensatedLeakageIdentity
  ∷ missingCKNBKMClosure
  ∷ missingClayPromotion
  ∷ []

physicalAngularMeasureBlockerCount : Nat
physicalAngularMeasureBlockerCount =
  listLength canonicalPhysicalAngularMeasureBlockers

physicalAngularMeasureBlockerCountIs8 :
  physicalAngularMeasureBlockerCount ≡ 8
physicalAngularMeasureBlockerCountIs8 =
  refl

data PhysicalAngularMeasureStatusRow : Set where
  childBoundaryRecordedStatus :
    PhysicalAngularMeasureStatusRow
  localizedCKNPacketCarrierRecordedStatus :
    PhysicalAngularMeasureStatusRow
  normalizedDirectionFieldCarrierRecordedStatus :
    PhysicalAngularMeasureStatusRow
  highVorticityThresholdCarrierRecordedStatus :
    PhysicalAngularMeasureStatusRow
  physicalAngularMeasureCarrierRecordedStatus :
    PhysicalAngularMeasureStatusRow
  lrtGreatCircleSupportCarrierRecordedStatus :
    PhysicalAngularMeasureStatusRow
  outputSupportTransferInputRecordedStatus :
    PhysicalAngularMeasureStatusRow
  allTheoremAndPromotionFlagsFalseStatus :
    PhysicalAngularMeasureStatusRow

canonicalPhysicalAngularMeasureStatusRows :
  List PhysicalAngularMeasureStatusRow
canonicalPhysicalAngularMeasureStatusRows =
  childBoundaryRecordedStatus
  ∷ localizedCKNPacketCarrierRecordedStatus
  ∷ normalizedDirectionFieldCarrierRecordedStatus
  ∷ highVorticityThresholdCarrierRecordedStatus
  ∷ physicalAngularMeasureCarrierRecordedStatus
  ∷ lrtGreatCircleSupportCarrierRecordedStatus
  ∷ outputSupportTransferInputRecordedStatus
  ∷ allTheoremAndPromotionFlagsFalseStatus
  ∷ []

physicalAngularMeasureStatusRowCount : Nat
physicalAngularMeasureStatusRowCount =
  listLength canonicalPhysicalAngularMeasureStatusRows

physicalAngularMeasureStatusRowCountIs8 :
  physicalAngularMeasureStatusRowCount ≡ 8
physicalAngularMeasureStatusRowCountIs8 =
  refl

------------------------------------------------------------------------
-- Promotion-closed type.

data PhysicalAngularMeasurePromotion : Set where

physicalAngularMeasurePromotionImpossibleHere :
  PhysicalAngularMeasurePromotion →
  ⊥
physicalAngularMeasurePromotionImpossibleHere ()

------------------------------------------------------------------------
-- Fail-closed governance flags.

NSPhysicalAngularMeasureConstructionBoundaryRecorded : Bool
NSPhysicalAngularMeasureConstructionBoundaryRecorded =
  true

localizedCKNPacketCarrierRecorded : Bool
localizedCKNPacketCarrierRecorded =
  true

normalizedDirectionFieldCarrierRecorded : Bool
normalizedDirectionFieldCarrierRecorded =
  true

highVorticityThresholdCarrierRecorded : Bool
highVorticityThresholdCarrierRecorded =
  true

physicalAngularMeasureCarrierRecorded : Bool
physicalAngularMeasureCarrierRecorded =
  true

physicalAngularMeasureNormalizationRecorded : Bool
physicalAngularMeasureNormalizationRecorded =
  true

physicalAngularMeasureGreatCircleSupportRecorded : Bool
physicalAngularMeasureGreatCircleSupportRecorded =
  true

outputSupportTransferInputRecorded : Bool
outputSupportTransferInputRecorded =
  true

physicalAngularMeasureConstructionProved : Bool
physicalAngularMeasureConstructionProved =
  false

quantitativeDensityEquivalenceProved : Bool
quantitativeDensityEquivalenceProved =
  false

cutoffThresholdMassRetentionProved : Bool
cutoffThresholdMassRetentionProved =
  false

physicalToFourierAngularCouplingProved : Bool
physicalToFourierAngularCouplingProved =
  false

outputDirectionSupportLiftProved : Bool
outputDirectionSupportLiftProved =
  false

pdeAbelMeasureSupportTheoremProved : Bool
pdeAbelMeasureSupportTheoremProved =
  false

triadicCompensatedLeakageIdentityProved : Bool
triadicCompensatedLeakageIdentityProved =
  false

cknBkmClosureProved : Bool
cknBkmClosureProved =
  false

full_clay_ns_solved : Bool
full_clay_ns_solved =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

recordsBoundary :
  NSPhysicalAngularMeasureConstructionBoundaryRecorded ≡ true
recordsBoundary =
  refl

recordsLocalizedCKNPacketCarrier :
  localizedCKNPacketCarrierRecorded ≡ true
recordsLocalizedCKNPacketCarrier =
  refl

recordsNormalizedDirectionFieldCarrier :
  normalizedDirectionFieldCarrierRecorded ≡ true
recordsNormalizedDirectionFieldCarrier =
  refl

recordsHighVorticityThresholdCarrier :
  highVorticityThresholdCarrierRecorded ≡ true
recordsHighVorticityThresholdCarrier =
  refl

recordsPhysicalAngularMeasureCarrier :
  physicalAngularMeasureCarrierRecorded ≡ true
recordsPhysicalAngularMeasureCarrier =
  refl

recordsPhysicalAngularMeasureNormalization :
  physicalAngularMeasureNormalizationRecorded ≡ true
recordsPhysicalAngularMeasureNormalization =
  refl

recordsPhysicalAngularMeasureGreatCircleSupport :
  physicalAngularMeasureGreatCircleSupportRecorded ≡ true
recordsPhysicalAngularMeasureGreatCircleSupport =
  refl

recordsOutputSupportTransferInput :
  outputSupportTransferInputRecorded ≡ true
recordsOutputSupportTransferInput =
  refl

keepsPhysicalAngularMeasureConstructionFalse :
  physicalAngularMeasureConstructionProved ≡ false
keepsPhysicalAngularMeasureConstructionFalse =
  refl

keepsQuantitativeDensityEquivalenceFalse :
  quantitativeDensityEquivalenceProved ≡ false
keepsQuantitativeDensityEquivalenceFalse =
  refl

keepsCutoffThresholdMassRetentionFalse :
  cutoffThresholdMassRetentionProved ≡ false
keepsCutoffThresholdMassRetentionFalse =
  refl

keepsPhysicalToFourierAngularCouplingFalse :
  physicalToFourierAngularCouplingProved ≡ false
keepsPhysicalToFourierAngularCouplingFalse =
  refl

keepsOutputDirectionSupportLiftFalse :
  outputDirectionSupportLiftProved ≡ false
keepsOutputDirectionSupportLiftFalse =
  refl

keepsPDEAbelMeasureSupportTheoremFalse :
  pdeAbelMeasureSupportTheoremProved ≡ false
keepsPDEAbelMeasureSupportTheoremFalse =
  refl

keepsTriadicCompensatedLeakageIdentityFalse :
  triadicCompensatedLeakageIdentityProved ≡ false
keepsTriadicCompensatedLeakageIdentityFalse =
  refl

keepsCKNBKMClosureFalse :
  cknBkmClosureProved ≡ false
keepsCKNBKMClosureFalse =
  refl

keepsClayPromotionFalse :
  clayNavierStokesPromoted ≡ false
keepsClayPromotionFalse =
  refl

keepsTerminalPromotionFalse :
  terminalPromotion ≡ false
keepsTerminalPromotionFalse =
  refl

------------------------------------------------------------------------
-- FORMAL MODEL: O, R, C, S, L, P, G, F.

organizationString : String
organizationString =
  "O: NS A4 child lane records the physical angular measure construction before Whitney/frame Fourier-output coupling."

requirementString : String
requirementString =
  "R: Construct a localized CKN/Type-I vorticity-direction measure carrier, attach LRT great-circle richness, and keep all theorem/promotion gates closed."

codeArtifactString : String
codeArtifactString =
  "C: NSPhysicalAngularMeasureConstructionBoundary imports LRT, Abel defect measure, A4 output support transfer, and triadic sheaf output-condition anchors."

stateString : String
stateString =
  "S: Carriers and obligations are typed; the analytic measure construction, cutoff mass retention, physical-to-Fourier coupling, and Clay closure are not proved."

latticeString : String
latticeString =
  "L: CKN packet -> nonzero vorticity direction field -> high-vorticity threshold set -> angular pushforward measure -> LRT support carrier -> A4 coupling input."

proposalString : String
proposalString =
  "P: Prove this rung by a localized enstrophy pushforward and weak-star compactness argument, then feed the resulting support carrier to the Whitney coupling theorem."

governanceString : String
governanceString =
  "G: Fail-closed receipt only; no quantitative density, Fourier output lift, PDE Abel support theorem, A6 leakage identity, CKN/BKM closure, Clay, or terminal promotion."

gapString : String
gapString =
  "F: Remaining blockers are cutoff/threshold mass retention, quantitative angular control if needed, physical-to-Fourier coupling, output support lift, A6, and CKN/BKM."

------------------------------------------------------------------------
-- Canonical receipt.

record NSPhysicalAngularMeasureConstructionBoundary : Set where
  constructor nsPhysicalAngularMeasureConstructionBoundary
  field
    importedSupport :
      ImportedPhysicalAngularMeasureSupport
    importedSupportIsCanonical :
      importedSupport ≡ canonicalImportedPhysicalAngularMeasureSupport
    localizedCKNCylinder :
      LocalizedCKNCylinderCarrier
    localizedCKNCylinderIsCanonical :
      localizedCKNCylinder ≡ canonicalLocalizedCKNCylinder
    vorticityPacket :
      TypeIVorticityPacketCarrier
    vorticityPacketIsCanonical :
      vorticityPacket ≡ canonicalTypeIVorticityPacket
    directionField :
      NonzeroVorticityDirectionFieldCarrier
    directionFieldIsCanonical :
      directionField ≡ canonicalNonzeroVorticityDirectionField
    highVorticityThreshold :
      HighVorticityThresholdCarrier
    highVorticityThresholdIsCanonical :
      highVorticityThreshold ≡ canonicalHighVorticityThreshold
    highVorticityPacketSet :
      HighVorticityPacketSetCarrier
    highVorticityPacketSetIsCanonical :
      highVorticityPacketSet ≡ canonicalHighVorticityPacketSet
    physicalAngularMeasure :
      PhysicalAngularMeasureCarrier
    physicalAngularMeasureIsCanonical :
      physicalAngularMeasure ≡ canonicalPhysicalAngularMeasure
    physicalAngularMeasureNormalization :
      PhysicalAngularMeasureNormalizationCarrier
    physicalAngularMeasureNormalizationIsCanonical :
      physicalAngularMeasureNormalization
        ≡ canonicalPhysicalAngularMeasureNormalization
    greatCircleSupport :
      PhysicalAngularMeasureGreatCircleSupportCarrier
    greatCircleSupportIsCanonical :
      greatCircleSupport
        ≡ canonicalPhysicalAngularMeasureGreatCircleSupport
    constructionObligations :
      List PhysicalAngularMeasureConstructionObligation
    constructionObligationsAreCanonical :
      constructionObligations
        ≡ canonicalPhysicalAngularMeasureConstructionObligations
    constructionObligationCount :
      physicalAngularMeasureConstructionObligationCount ≡ 11
    premises :
      List PhysicalAngularMeasurePremise
    premisesAreCanonical :
      premises ≡ canonicalPhysicalAngularMeasurePremises
    premiseCount :
      physicalAngularMeasurePremiseCount ≡ 8
    blockers :
      List PhysicalAngularMeasureBlocker
    blockersAreCanonical :
      blockers ≡ canonicalPhysicalAngularMeasureBlockers
    blockerCount :
      physicalAngularMeasureBlockerCount ≡ 8
    statusRows :
      List PhysicalAngularMeasureStatusRow
    statusRowsAreCanonical :
      statusRows ≡ canonicalPhysicalAngularMeasureStatusRows
    statusRowCount :
      physicalAngularMeasureStatusRowCount ≡ 8
    recordsBoundaryTrue :
      NSPhysicalAngularMeasureConstructionBoundaryRecorded ≡ true
    constructionProvedFalse :
      physicalAngularMeasureConstructionProved ≡ false
    densityEquivalenceProvedFalse :
      quantitativeDensityEquivalenceProved ≡ false
    cutoffThresholdMassRetentionProvedFalse :
      cutoffThresholdMassRetentionProved ≡ false
    physicalToFourierCouplingProvedFalse :
      physicalToFourierAngularCouplingProved ≡ false
    outputDirectionSupportLiftProvedFalse :
      outputDirectionSupportLiftProved ≡ false
    pdeAbelMeasureSupportTheoremProvedFalse :
      pdeAbelMeasureSupportTheoremProved ≡ false
    triadicCompensatedLeakageIdentityProvedFalse :
      triadicCompensatedLeakageIdentityProved ≡ false
    cknBkmClosureProvedFalse :
      cknBkmClosureProved ≡ false
    clayNavierStokesPromotedFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionFalse :
      terminalPromotion ≡ false
    organization :
      String
    requirement :
      String
    codeArtifact :
      String
    state :
      String
    lattice :
      String
    proposal :
      String
    governance :
      String
    gap :
      String

canonicalNSPhysicalAngularMeasureConstructionBoundary :
  NSPhysicalAngularMeasureConstructionBoundary
canonicalNSPhysicalAngularMeasureConstructionBoundary =
  nsPhysicalAngularMeasureConstructionBoundary
    canonicalImportedPhysicalAngularMeasureSupport
    refl
    canonicalLocalizedCKNCylinder
    refl
    canonicalTypeIVorticityPacket
    refl
    canonicalNonzeroVorticityDirectionField
    refl
    canonicalHighVorticityThreshold
    refl
    canonicalHighVorticityPacketSet
    refl
    canonicalPhysicalAngularMeasure
    refl
    canonicalPhysicalAngularMeasureNormalization
    refl
    canonicalPhysicalAngularMeasureGreatCircleSupport
    refl
    canonicalPhysicalAngularMeasureConstructionObligations
    refl
    physicalAngularMeasureConstructionObligationCountIs11
    canonicalPhysicalAngularMeasurePremises
    refl
    physicalAngularMeasurePremiseCountIs8
    canonicalPhysicalAngularMeasureBlockers
    refl
    physicalAngularMeasureBlockerCountIs8
    canonicalPhysicalAngularMeasureStatusRows
    refl
    physicalAngularMeasureStatusRowCountIs8
    recordsBoundary
    keepsPhysicalAngularMeasureConstructionFalse
    keepsQuantitativeDensityEquivalenceFalse
    keepsCutoffThresholdMassRetentionFalse
    keepsPhysicalToFourierAngularCouplingFalse
    keepsOutputDirectionSupportLiftFalse
    keepsPDEAbelMeasureSupportTheoremFalse
    keepsTriadicCompensatedLeakageIdentityFalse
    keepsCKNBKMClosureFalse
    keepsClayPromotionFalse
    keepsTerminalPromotionFalse
    organizationString
    requirementString
    codeArtifactString
    stateString
    latticeString
    proposalString
    governanceString
    gapString

------------------------------------------------------------------------
-- Contradictions: this boundary is not theorem promotion.

physicalAngularMeasureConstructionNotProvedHere :
  physicalAngularMeasureConstructionProved ≡ true →
  ⊥
physicalAngularMeasureConstructionNotProvedHere ()

physicalToFourierCouplingNotProvedHere :
  physicalToFourierAngularCouplingProved ≡ true →
  ⊥
physicalToFourierCouplingNotProvedHere ()

outputSupportLiftNotProvedHere :
  outputDirectionSupportLiftProved ≡ true →
  ⊥
outputSupportLiftNotProvedHere ()

nsPhysicalAngularMeasureDoesNotPromoteClay :
  clayNavierStokesPromoted ≡ true →
  ⊥
nsPhysicalAngularMeasureDoesNotPromoteClay ()

nsPhysicalAngularMeasureDoesNotPromoteTerminal :
  terminalPromotion ≡ true →
  ⊥
nsPhysicalAngularMeasureDoesNotPromoteTerminal ()
