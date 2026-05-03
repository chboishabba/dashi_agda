module DASHI.Physics.Closure.ChemistryPhysicalHandoffDiagnostic where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRRetargetedChannel as Retargeted
import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlRetargetPolicyDecision as Policy
import DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCandidate256Witness as Candidate256
import DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCouplingRequirement as CrossBand

------------------------------------------------------------------------
-- W4c chemistry physical-handoff diagnostic.
--
-- The carrier policy and the quotient/cross-band chemistry law are accepted
-- only as pre-handoff structure.  Promotion still requires a physical
-- interpretation consumer for the quotient classes over the accepted carrier.

data ChemistryPhysicalHandoffStatus : Set where
  missingPhysicalConsumer : ChemistryPhysicalHandoffStatus
  missingRetargetedQuotientInterpretationCarrierOrPreservationLaw :
    ChemistryPhysicalHandoffStatus
  retargetedQuotientPrePhysicalConsumerAvailable :
    ChemistryPhysicalHandoffStatus

QuotientSupport :
  CrossBand.ChemistryRightLimitsQuotientCrossBandLaw →
  Set
QuotientSupport quotientLaw =
  CrossBand.RequirementSupport
    (CrossBand.ChemistryRightLimitsQuotientCrossBandCouplingRequirement.tripleLaw
      (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.requirement
        quotientLaw))

QuotientCarrier :
  CrossBand.ChemistryRightLimitsQuotientCrossBandLaw →
  Set
QuotientCarrier quotientLaw =
  CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.Q quotientLaw

leftQuotientClass :
  (quotientLaw : CrossBand.ChemistryRightLimitsQuotientCrossBandLaw) →
  QuotientCarrier quotientLaw
leftQuotientClass quotientLaw =
  CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.q
    quotientLaw
    (CrossBand.ChemistryRightLimitsQuotientCrossBandCouplingRequirement.left
      (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.requirement
        quotientLaw))

rightQuotientClass :
  (quotientLaw : CrossBand.ChemistryRightLimitsQuotientCrossBandLaw) →
  QuotientCarrier quotientLaw
rightQuotientClass quotientLaw =
  CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.q
    quotientLaw
    (CrossBand.ChemistryRightLimitsQuotientCrossBandCouplingRequirement.right
      (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.requirement
        quotientLaw))

QuotientLawAtWitness :
  (quotientLaw : CrossBand.ChemistryRightLimitsQuotientCrossBandLaw) →
  Set₁
QuotientLawAtWitness quotientLaw =
  CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.Lchem
    quotientLaw
    (leftQuotientClass quotientLaw)
    (rightQuotientClass quotientLaw)

RetargetedCarrierPreservation :
  Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted →
  Set
RetargetedCarrierPreservation acceptedCarrier =
  ∀ x →
  Retargeted.transportedScheduleMdlChannel x
    ≡
  Retargeted.CanonicalToNoncanonicalMdlCRRetargetedChannel.replacementNoncanonicalMdl
    (Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted.channel
      acceptedCarrier)
    x

PhysicalQuotientLawPreservation :
  (quotientLaw : CrossBand.ChemistryRightLimitsQuotientCrossBandLaw) →
  (PhysicalCarrier : Set) →
  (interpretQuotientClass : QuotientCarrier quotientLaw → PhysicalCarrier) →
  (physicalMeaning : PhysicalCarrier → Set) →
  Set₁
PhysicalQuotientLawPreservation
  quotientLaw
  PhysicalCarrier
  interpretQuotientClass
  physicalMeaning =
  QuotientLawAtWitness quotientLaw →
  physicalMeaning (interpretQuotientClass (leftQuotientClass quotientLaw))
  ×
  physicalMeaning (interpretQuotientClass (rightQuotientClass quotientLaw))

PreSpectralPreScaleQuotientMeaning :
  (quotientLaw : CrossBand.ChemistryRightLimitsQuotientCrossBandLaw) →
  QuotientCarrier quotientLaw →
  Set
PreSpectralPreScaleQuotientMeaning quotientLaw _ =
  CrossBand.ChemistryRightLimitsQuotientCrossBandCouplingRequirement.preSpectralBoundary
    (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.requirement
      quotientLaw)
  ×
  CrossBand.ChemistryRightLimitsQuotientCrossBandCouplingRequirement.preScaleSettingBoundary
    (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.requirement
      quotientLaw)

record ChemistryPhysicalConsumer
  (acceptedCarrier :
    Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted)
  (quotientLaw :
    CrossBand.ChemistryRightLimitsQuotientCrossBandLaw) :
  Setω where
  field
    physicalInterpretationCarrier : Set
    physicalMeaning : physicalInterpretationCarrier → Set

    interpretQuotientClass :
      QuotientCarrier quotientLaw →
      physicalInterpretationCarrier

    consumesAcceptedCarrier :
      RetargetedCarrierPreservation acceptedCarrier

    consumesQuotientClasses :
      (support : QuotientSupport quotientLaw) →
      physicalMeaning
        (interpretQuotientClass
          (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.q
            quotientLaw
            support))

    preservesQuotientLawAtWitness :
      PhysicalQuotientLawPreservation
        quotientLaw
        physicalInterpretationCarrier
        interpretQuotientClass
        physicalMeaning

    preservesPreSpectralBoundary :
      CrossBand.ChemistryRightLimitsQuotientCrossBandCouplingRequirement.preSpectralBoundary
        (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.requirement
          quotientLaw)

    preservesPreScaleSettingBoundary :
      CrossBand.ChemistryRightLimitsQuotientCrossBandCouplingRequirement.preScaleSettingBoundary
        (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.requirement
          quotientLaw)

    nonClaimBoundary : List String

record ChemistryPhysicalConsumerMissingIngredient
  (acceptedCarrier :
    Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted)
  (quotientLaw :
    CrossBand.ChemistryRightLimitsQuotientCrossBandLaw) :
  Setω where
  field
    requiredPhysicalInterpretationCarrier : Set

    requiredPhysicalMeaning :
      requiredPhysicalInterpretationCarrier →
      Set

    requiredQuotientClassInterpreter :
      QuotientCarrier quotientLaw →
      requiredPhysicalInterpretationCarrier

    requiredRetargetedCarrierPreservation :
      RetargetedCarrierPreservation acceptedCarrier

    requiredQuotientLawPreservation :
      PhysicalQuotientLawPreservation
        quotientLaw
        requiredPhysicalInterpretationCarrier
        requiredQuotientClassInterpreter
        requiredPhysicalMeaning

    requiredPreSpectralBoundaryPreservation :
      CrossBand.ChemistryRightLimitsQuotientCrossBandCouplingRequirement.preSpectralBoundary
        (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.requirement
          quotientLaw)

    requiredPreScaleSettingBoundaryPreservation :
      CrossBand.ChemistryRightLimitsQuotientCrossBandCouplingRequirement.preScaleSettingBoundary
        (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.requirement
          quotientLaw)

    diagnosticBoundary : List String

record ChemistryPhysicalHandoffPreReceipt : Setω where
  field
    acceptedCarrier :
      Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted

    quotientLaw :
      CrossBand.ChemistryRightLimitsQuotientCrossBandLaw

    tsfvKernel :
      CrossBand.TimeSymmetricCrossBandKernel

    physicalConsumerNeeded :
      ChemistryPhysicalConsumer acceptedCarrier quotientLaw →
      Set

    missingIngredientNeeded :
      ChemistryPhysicalConsumerMissingIngredient acceptedCarrier quotientLaw →
      Set

    currentStatus :
      ChemistryPhysicalHandoffStatus

    nonClaimBoundary : List String

canonicalChemistryPhysicalHandoffPreReceipt :
  ChemistryPhysicalHandoffPreReceipt
canonicalChemistryPhysicalHandoffPreReceipt =
  record
    { acceptedCarrier =
        Policy.canonicalToNoncanonicalMdlCRRetargetPolicyAccepted
    ; quotientLaw =
        Candidate256.canonicalCandidate256QuotientCrossBandLaw
    ; tsfvKernel =
        CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.timeSymmetricKernel
          Candidate256.canonicalCandidate256QuotientCrossBandLaw
    ; physicalConsumerNeeded =
        λ consumer →
          ChemistryPhysicalConsumer.physicalInterpretationCarrier consumer
    ; missingIngredientNeeded =
        λ ingredient →
          ChemistryPhysicalConsumerMissingIngredient.requiredPhysicalInterpretationCarrier
            ingredient
    ; currentStatus =
        retargetedQuotientPrePhysicalConsumerAvailable
    ; nonClaimBoundary =
        "Carrier policy is accepted only for the retargeted transported schedule-MDL channel"
        ∷ "The quotient/cross-band chemistry law is pre-spectral and pre-scale-setting"
        ∷ "A physical consumer now means a carrier, quotient-class interpreter, retargeted-carrier preservation law, and quotient-law preservation law"
        ∷ "No spectra, bonding, wet-lab chemistry, or physical interpretation is claimed here"
        ∷ "W4e adds only a proof-thin retargeted-quotient pre-physical carrier and preservation law"
        ∷ []
    }

canonicalRetargetedCarrierPreservation :
  RetargetedCarrierPreservation
    Policy.canonicalToNoncanonicalMdlCRRetargetPolicyAccepted
canonicalRetargetedCarrierPreservation =
  Retargeted.CanonicalToNoncanonicalMdlCRRetargetPolicyAccepted.acceptedReplacementIsTransportedSchedule
    Policy.canonicalToNoncanonicalMdlCRRetargetPolicyAccepted

canonicalPreSpectralBoundaryPreservation :
  CrossBand.ChemistryRightLimitsQuotientCrossBandCouplingRequirement.preSpectralBoundary
    (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.requirement
      Candidate256.canonicalCandidate256QuotientCrossBandLaw)
canonicalPreSpectralBoundaryPreservation =
  λ _ → refl

canonicalPreScaleSettingBoundaryPreservation :
  CrossBand.ChemistryRightLimitsQuotientCrossBandCouplingRequirement.preScaleSettingBoundary
    (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.requirement
      Candidate256.canonicalCandidate256QuotientCrossBandLaw)
canonicalPreScaleSettingBoundaryPreservation =
  λ _ → refl

canonicalPreSpectralPreScaleQuotientMeaning :
  (q :
    QuotientCarrier
      Candidate256.canonicalCandidate256QuotientCrossBandLaw) →
  PreSpectralPreScaleQuotientMeaning
    Candidate256.canonicalCandidate256QuotientCrossBandLaw
    q
canonicalPreSpectralPreScaleQuotientMeaning _ =
  canonicalPreSpectralBoundaryPreservation
  ,
  canonicalPreScaleSettingBoundaryPreservation

canonicalPhysicalQuotientLawPreservation :
  PhysicalQuotientLawPreservation
    Candidate256.canonicalCandidate256QuotientCrossBandLaw
    (QuotientCarrier
      Candidate256.canonicalCandidate256QuotientCrossBandLaw)
    (λ q → q)
    (PreSpectralPreScaleQuotientMeaning
      Candidate256.canonicalCandidate256QuotientCrossBandLaw)
canonicalPhysicalQuotientLawPreservation _ =
  canonicalPreSpectralPreScaleQuotientMeaning
    (leftQuotientClass
      Candidate256.canonicalCandidate256QuotientCrossBandLaw)
  ,
  canonicalPreSpectralPreScaleQuotientMeaning
    (rightQuotientClass
      Candidate256.canonicalCandidate256QuotientCrossBandLaw)

canonicalRetargetedQuotientChemistryPhysicalConsumer :
  ChemistryPhysicalConsumer
    Policy.canonicalToNoncanonicalMdlCRRetargetPolicyAccepted
    Candidate256.canonicalCandidate256QuotientCrossBandLaw
canonicalRetargetedQuotientChemistryPhysicalConsumer =
  record
    { physicalInterpretationCarrier =
        QuotientCarrier
          Candidate256.canonicalCandidate256QuotientCrossBandLaw
    ; physicalMeaning =
        PreSpectralPreScaleQuotientMeaning
          Candidate256.canonicalCandidate256QuotientCrossBandLaw
    ; interpretQuotientClass =
        λ q → q
    ; consumesAcceptedCarrier =
        canonicalRetargetedCarrierPreservation
    ; consumesQuotientClasses =
        λ support →
          canonicalPreSpectralPreScaleQuotientMeaning
            (CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.q
              Candidate256.canonicalCandidate256QuotientCrossBandLaw
              support)
    ; preservesQuotientLawAtWitness =
        canonicalPhysicalQuotientLawPreservation
    ; preservesPreSpectralBoundary =
        canonicalPreSpectralBoundaryPreservation
    ; preservesPreScaleSettingBoundary =
        canonicalPreScaleSettingBoundaryPreservation
    ; nonClaimBoundary =
        "The carrier is exactly the accepted quotient carrier; no new spectral, bonding, or wet-lab carrier is introduced"
        ∷ "The interpretation meaning is only the pre-spectral and pre-scale-setting boundary pair"
        ∷ "The quotient law is consumed only by preserving those boundary witnesses at the landed left/right quotient classes"
        ∷ "Retargeted-carrier preservation is exactly the accepted transported schedule-MDL replacement law"
        ∷ "This is a pre-physical handoff consumer, not a scale-setting, spectra, bonding, wet-lab, or physical-closure theorem"
        ∷ []
    }

canonicalChemistryPhysicalHandoffPreReceiptConsumer :
  ChemistryPhysicalConsumer
    (ChemistryPhysicalHandoffPreReceipt.acceptedCarrier
      canonicalChemistryPhysicalHandoffPreReceipt)
    (ChemistryPhysicalHandoffPreReceipt.quotientLaw
      canonicalChemistryPhysicalHandoffPreReceipt)
canonicalChemistryPhysicalHandoffPreReceiptConsumer =
  canonicalRetargetedQuotientChemistryPhysicalConsumer

canonicalChemistryPhysicalHandoffPreReceiptConsumerCarrierWitness :
  ChemistryPhysicalHandoffPreReceipt.physicalConsumerNeeded
    canonicalChemistryPhysicalHandoffPreReceipt
    canonicalChemistryPhysicalHandoffPreReceiptConsumer
canonicalChemistryPhysicalHandoffPreReceiptConsumerCarrierWitness =
  leftQuotientClass
    (ChemistryPhysicalHandoffPreReceipt.quotientLaw
      canonicalChemistryPhysicalHandoffPreReceipt)

canonicalChemistryPhysicalHandoffMissingConsumer :
  ChemistryPhysicalHandoffStatus
canonicalChemistryPhysicalHandoffMissingConsumer =
  ChemistryPhysicalHandoffPreReceipt.currentStatus
    canonicalChemistryPhysicalHandoffPreReceipt
