module DASHI.Physics.Closure.W4StrictPhysicalNextObligation where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlRetargetPolicyDecision as Policy
import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRRetargetedChannel as Retargeted
import DASHI.Physics.Closure.ChemistryPhysicalHandoffDiagnostic as Handoff
import DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCandidate256Witness as Candidate256
import DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCouplingRequirement as CrossBand
import DASHI.Physics.Closure.ChemistryStrictPhysicalSemanticsBlocker as Blocker

------------------------------------------------------------------------
-- W4g strict-physical next-obligation surface.
--
-- This module does not promote Candidate256 to physical chemistry.  It only
-- packages the exact fields that a later worker must inhabit before making
-- scale-setting, spectra, bonding, or empirical physical-validation claims.

canonicalCandidate256AcceptedRetargetedCarrier :
  Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted
canonicalCandidate256AcceptedRetargetedCarrier =
  Policy.canonicalToNoncanonicalMdlCRRetargetPolicyAccepted

canonicalCandidate256QuotientLaw :
  CrossBand.ChemistryRightLimitsQuotientCrossBandLaw
canonicalCandidate256QuotientLaw =
  Candidate256.canonicalCandidate256QuotientCrossBandLaw

canonicalCandidate256PrePhysicalConsumer :
  Handoff.ChemistryPhysicalConsumer
    canonicalCandidate256AcceptedRetargetedCarrier
    canonicalCandidate256QuotientLaw
canonicalCandidate256PrePhysicalConsumer =
  Handoff.canonicalRetargetedQuotientChemistryPhysicalConsumer

record StrictPhysicalNextObligationFields
  (acceptedCarrier :
    Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted)
  (quotientLaw :
    CrossBand.ChemistryRightLimitsQuotientCrossBandLaw) :
  Setω where
  field
    availablePrePhysicalConsumer :
      Handoff.ChemistryPhysicalConsumer acceptedCarrier quotientLaw

    physicalScaleCarrier : Set
    spectralObservableCarrier : Set
    bondingInterpretationCarrier : Set
    empiricalValidationCarrier : Set

    scaleSettingMap :
      Handoff.QuotientCarrier quotientLaw →
      physicalScaleCarrier

    spectralObservableMap :
      Handoff.QuotientCarrier quotientLaw →
      spectralObservableCarrier

    bondingInterpretationMap :
      Handoff.QuotientCarrier quotientLaw →
      bondingInterpretationCarrier

    empiricalPhysicalValidationMap :
      Handoff.QuotientCarrier quotientLaw →
      empiricalValidationCarrier

    scaleSettingLaw :
      Handoff.QuotientLawAtWitness quotientLaw →
      Set

    spectralObservableLaw :
      Handoff.QuotientLawAtWitness quotientLaw →
      Set

    bondingInterpretationLaw :
      Handoff.QuotientLawAtWitness quotientLaw →
      Set

    empiricalPhysicalValidationLaw :
      Handoff.QuotientLawAtWitness quotientLaw →
      Set

    scaleSettingPreservesLeftRight :
      (law : Handoff.QuotientLawAtWitness quotientLaw) →
      scaleSettingLaw law

    spectralObservablePreservesLeftRight :
      (law : Handoff.QuotientLawAtWitness quotientLaw) →
      spectralObservableLaw law

    bondingInterpretationPreservesLeftRight :
      (law : Handoff.QuotientLawAtWitness quotientLaw) →
      bondingInterpretationLaw law

    empiricalPhysicalValidationPreservesLeftRight :
      (law : Handoff.QuotientLawAtWitness quotientLaw) →
      empiricalPhysicalValidationLaw law

    noPromotionBoundary : List String

strictPhysicalNextObligationFieldsToBoundaryFields :
  {acceptedCarrier :
    Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted}
  {quotientLaw :
    CrossBand.ChemistryRightLimitsQuotientCrossBandLaw} →
  StrictPhysicalNextObligationFields acceptedCarrier quotientLaw →
  Blocker.StrictPhysicalBoundaryFields quotientLaw
strictPhysicalNextObligationFieldsToBoundaryFields obligations =
  record
    { physicalScaleCarrier =
        StrictPhysicalNextObligationFields.physicalScaleCarrier obligations
    ; spectralObservableCarrier =
        StrictPhysicalNextObligationFields.spectralObservableCarrier obligations
    ; bondingInterpretationCarrier =
        StrictPhysicalNextObligationFields.bondingInterpretationCarrier obligations
    ; empiricalValidationCarrier =
        StrictPhysicalNextObligationFields.empiricalValidationCarrier obligations
    ; scaleSettingMap =
        StrictPhysicalNextObligationFields.scaleSettingMap obligations
    ; spectralObservableMap =
        StrictPhysicalNextObligationFields.spectralObservableMap obligations
    ; bondingInterpretationMap =
        StrictPhysicalNextObligationFields.bondingInterpretationMap obligations
    ; empiricalPhysicalValidationMap =
        StrictPhysicalNextObligationFields.empiricalPhysicalValidationMap
          obligations
    }

strictPhysicalNextObligationFieldsToBoundaryPreservation :
  {acceptedCarrier :
    Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted}
  {quotientLaw :
    CrossBand.ChemistryRightLimitsQuotientCrossBandLaw} →
  (obligations :
    StrictPhysicalNextObligationFields acceptedCarrier quotientLaw) →
  Blocker.StrictPhysicalBoundaryPreservation
    quotientLaw
    (strictPhysicalNextObligationFieldsToBoundaryFields obligations)
strictPhysicalNextObligationFieldsToBoundaryPreservation obligations =
  record
    { scaleSettingLaw =
        StrictPhysicalNextObligationFields.scaleSettingLaw obligations
    ; spectralObservableLaw =
        StrictPhysicalNextObligationFields.spectralObservableLaw obligations
    ; bondingInterpretationLaw =
        StrictPhysicalNextObligationFields.bondingInterpretationLaw obligations
    ; empiricalPhysicalValidationLaw =
        StrictPhysicalNextObligationFields.empiricalPhysicalValidationLaw
          obligations
    ; scaleSettingPreservesLeftRight =
        StrictPhysicalNextObligationFields.scaleSettingPreservesLeftRight
          obligations
    ; spectralObservablePreservesLeftRight =
        StrictPhysicalNextObligationFields.spectralObservablePreservesLeftRight
          obligations
    ; bondingInterpretationPreservesLeftRight =
        StrictPhysicalNextObligationFields.bondingInterpretationPreservesLeftRight
          obligations
    ; empiricalPhysicalValidationPreservesLeftRight =
        StrictPhysicalNextObligationFields.empiricalPhysicalValidationPreservesLeftRight
          obligations
    }

strictPhysicalNextObligationFieldsToStrictConsumer :
  {acceptedCarrier :
    Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted}
  {quotientLaw :
    CrossBand.ChemistryRightLimitsQuotientCrossBandLaw} →
  StrictPhysicalNextObligationFields acceptedCarrier quotientLaw →
  Blocker.StrictChemistryPhysicalSemanticsConsumer
    acceptedCarrier
    quotientLaw
strictPhysicalNextObligationFieldsToStrictConsumer obligations =
  record
    { prePhysicalConsumer =
        StrictPhysicalNextObligationFields.availablePrePhysicalConsumer
          obligations
    ; strictBoundaryFields =
        strictPhysicalNextObligationFieldsToBoundaryFields obligations
    ; strictBoundaryPreservation =
        strictPhysicalNextObligationFieldsToBoundaryPreservation obligations
    ; doesNotCollapseToPreSpectralPreScale =
        StrictPhysicalNextObligationFields.noPromotionBoundary obligations
    }

Candidate256StrictPhysicalNextObligations : Setω
Candidate256StrictPhysicalNextObligations =
  StrictPhysicalNextObligationFields
    canonicalCandidate256AcceptedRetargetedCarrier
    canonicalCandidate256QuotientLaw

record Candidate256StrictPhysicalNextObligationReceipt : Setω where
  field
    blocker :
      Blocker.ChemistryStrictPhysicalSemanticsBlocker
        canonicalCandidate256AcceptedRetargetedCarrier
        canonicalCandidate256QuotientLaw

    currentHandoffStatus :
      Handoff.ChemistryPhysicalHandoffStatus

    nextObligations :
      List Blocker.StrictPhysicalMissingIngredient

    nextObligationSurface :
      Candidate256StrictPhysicalNextObligations →
      Set

    requiredScaleSettingLaw : String
    requiredSpectralObservableMap : String
    requiredBondingInterpretation : String
    requiredEmpiricalPhysicalValidation : String

    noPromotionBoundary : List String

data W4StrictPhysicalBoundaryToken : Set where
  strictPhysicalObligationsNeeded : W4StrictPhysicalBoundaryToken

canonicalCandidate256StrictPhysicalNextObligationReceipt :
  Candidate256StrictPhysicalNextObligationReceipt
canonicalCandidate256StrictPhysicalNextObligationReceipt =
  record
    { blocker =
        Blocker.canonicalCandidate256StrictPhysicalSemanticsBlocker
    ; currentHandoffStatus =
        Handoff.retargetedQuotientPrePhysicalConsumerAvailable
    ; nextObligations =
        Blocker.missingScaleSettingLaw
        ∷ Blocker.missingSpectralObservableMap
        ∷ Blocker.missingBondingInterpretation
        ∷ Blocker.missingEmpiricalPhysicalValidation
        ∷ []
    ; nextObligationSurface =
        λ obligations →
          Blocker.ChemistryStrictPhysicalSemanticsBlocker.strictConsumerWouldNeed
            Blocker.canonicalCandidate256StrictPhysicalSemanticsBlocker
            (strictPhysicalNextObligationFieldsToStrictConsumer obligations)
    ; requiredScaleSettingLaw =
        "supply a physical scale carrier, quotient-class scale map, and L_chem preservation law over Candidate256"
    ; requiredSpectralObservableMap =
        "supply a spectral observable carrier, quotient-class observable map, and L_chem preservation law over Candidate256"
    ; requiredBondingInterpretation =
        "supply a bonding interpretation carrier, quotient-class bonding map, and L_chem preservation law over Candidate256"
    ; requiredEmpiricalPhysicalValidation =
        "supply an empirical validation carrier, quotient-class validation map, and L_chem preservation law over Candidate256"
    ; noPromotionBoundary =
        "This receipt is only a W4 strict-physical next-obligation surface"
        ∷ "The available consumer is still the retargeted quotient pre-physical consumer"
        ∷ "No scale-setting, spectral, bonding, wet-lab, or physical-closure theorem is inhabited here"
        ∷ []
    }

canonicalCandidate256StrictPhysicalBoundaryToken :
  W4StrictPhysicalBoundaryToken
canonicalCandidate256StrictPhysicalBoundaryToken =
  strictPhysicalObligationsNeeded
