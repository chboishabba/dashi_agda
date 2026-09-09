module DASHI.Cognition.PNF.SensibLawCullenResidualAdmissionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawApplicabilityPrerequisiteMeetExact as Meet
import DASHI.Cognition.PNF.SensibLawLegalSourceAuthorityEvidenceExact as Authority
import DASHI.Cognition.PNF.SensibLawWrongTypeLegalElementAlgebraExact as Elements
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawCullenConsumerCollisionMissingCoordinateExact as Collision
import DASHI.Cognition.PNF.SensibLawCullenSourceCorrectDutyRoutesExact as Routes
import DASHI.Cognition.PNF.SensibLawCullenEdelman64WrongTypeSourceRealisationExact as Source64

------------------------------------------------------------------------
-- CULLEN RESIDUAL ADMISSION BIDI
------------------------------------------------------------------------

record CullenAdmittedResidual
    (state : Status.SemanticCommitmentState) : Set₁ where
  constructor cullen-admitted-residual
  field
    separator :
      Synthesis.BundleSeparates
        Collision.statutoryPowerInspectionBundle
        (Consumer.left Collision.cullenLegacyConsumerCollision)
        (Consumer.right Collision.cullenLegacyConsumerCollision)

    sourceRealisation : Source64.Edelman64WrongTypeDutyReceipt
    sourceRouteIsEdelman :
      Source64.route (Source64.sourceRoute sourceRealisation)
      ≡ Routes.edelmanReasons

    applicabilityMeet : Meet.ApplicabilityMeetInput state
    legalSourceAuthority : Authority.LegalSourceAuthorityReceiptInState state
    authorityIsMeetAuthority :
      legalSourceAuthority ≡
      Meet.legalSourceAuthority (Meet.prerequisites applicabilityMeet)

    -- The WrongType in the live applicability meet must be the same WrongType
    -- carried by the exact source realisation, not merely equal to some generic
    -- negligence label elsewhere in the graph.
    meetWrongTypeMatchesSource :
      Meet.wrongType applicabilityMeet ≡ Source64.wrongType sourceRealisation

    targetElement : Elements.LegalElement Negligence.negligenceWrongType
    targetIsDuty : targetElement ≡ Negligence.dutyElement
    targetElementMatchesSource :
      targetElement ≡ Source64.targetElement sourceRealisation

    wrongTypeSystemMatchesCullenSystem :
      Ontology.WrongType.definingSystem (Meet.wrongType applicabilityMeet)
      ≡ Negligence.auCommonLawSystem

    residualRepair :
      Consumer.ResidualRepair
        Collision.observePoliceFunctionContext
        Collision.inspectStatutoryPower
        Collision.legacyBundledPremiseConsumer

    admissionReference : String

open CullenAdmittedResidual public

admittedResidualStrictlyRefinesLegacyObserver :
  ∀ {state} →
  CullenAdmittedResidual state →
  Observer.StrictRefinement
    Collision.observePoliceFunctionContext
    Collision.jointCullenObserver
admittedResidualStrictlyRefinesLegacyObserver admitted =
  Consumer.consumerRelevantResidualGivesStrictRefinement
    Collision.cullenLegacyConsumerCollision
    (residualRepair admitted)

------------------------------------------------------------------------
-- WrongType-target projections.
------------------------------------------------------------------------

admittedResidualTargetsNegligenceWrongType :
  ∀ {state} →
  (admitted : CullenAdmittedResidual state) →
  Meet.wrongType (applicabilityMeet admitted) ≡ Negligence.negligenceWrongType
admittedResidualTargetsNegligenceWrongType admitted =
  trans
    (meetWrongTypeMatchesSource admitted)
    (Source64.wrongTypeIsNegligence (sourceRealisation admitted))

admittedResidualTargetsDutyElement :
  ∀ {state} →
  (admitted : CullenAdmittedResidual state) →
  targetElement admitted ≡ Negligence.dutyElement
admittedResidualTargetsDutyElement = targetIsDuty

------------------------------------------------------------------------
-- Install only after exact source/applicability AND WrongType/duty welds.
------------------------------------------------------------------------

installCullenResidual :
  ∀ {state} →
  (meet : Meet.ApplicabilityMeetInput state) →
  (authority : Authority.LegalSourceAuthorityReceiptInState state) →
  authority ≡ Meet.legalSourceAuthority (Meet.prerequisites meet) →
  Meet.wrongType meet ≡ Source64.wrongType Source64.edelman64NegligenceDutyReceipt →
  Ontology.WrongType.definingSystem (Meet.wrongType meet)
    ≡ Negligence.auCommonLawSystem →
  CullenAdmittedResidual state
installCullenResidual meet authority sameAuthority sameWrongType sameSystem =
  cullen-admitted-residual
    Collision.statutoryPowerInspectionSeparatesCollision
    Source64.edelman64NegligenceDutyReceipt
    refl
    meet
    authority
    sameAuthority
    sameWrongType
    Negligence.dutyElement
    refl
    refl
    sameSystem
    Collision.cullenStatutoryPowerResidualRepair
    "Cullen residual installed only after the live applicability/authority meet is welded to the exact Edelman [64] source realisation and its canonical negligence WrongType / duty element."

------------------------------------------------------------------------
-- Hard non-promotions.
------------------------------------------------------------------------

data SeparatorAloneInstallsLegalResidual : Set where
data LegalSourceAuthorityAloneProvesConsumerSufficiency : Set where
data ApplicabilityMeetTurnsDashReconstructionIntoRatio : Set where
data ResidualRepairAloneEstablishesApplicability : Set where
data SeparatorDeterminesWrongType : Set where
data LegalAuthorityDeterminesWrongTypeElement : Set where
data NegligenceWrongTypeAutomaticallyPaysDutyElement : Set where
data DutyResidualCanBorrowWrongTypeFromAnotherSystem : Set where
data WrongTypeReceiptMayFloatFreeOfSourceProposition : Set where

data DirectSourceFactAutomaticallyPaysReconstructedRoute : Set where

separatorAloneCannotInstall : SeparatorAloneInstallsLegalResidual → ⊥
separatorAloneCannotInstall ()

authorityAloneDoesNotProveConsumerSufficiency :
  LegalSourceAuthorityAloneProvesConsumerSufficiency → ⊥
authorityAloneDoesNotProveConsumerSufficiency ()

applicabilityDoesNotUpgradeReconstructionAuthority :
  ApplicabilityMeetTurnsDashReconstructionIntoRatio → ⊥
applicabilityDoesNotUpgradeReconstructionAuthority ()

repairAloneDoesNotEstablishApplicability :
  ResidualRepairAloneEstablishesApplicability → ⊥
repairAloneDoesNotEstablishApplicability ()

separatorDoesNotDetermineWrongType : SeparatorDeterminesWrongType → ⊥
separatorDoesNotDetermineWrongType ()

authorityDoesNotDetermineWrongTypeElement :
  LegalAuthorityDeterminesWrongTypeElement → ⊥
authorityDoesNotDetermineWrongTypeElement ()

wrongTypeIdentityDoesNotPayDutyElement :
  NegligenceWrongTypeAutomaticallyPaysDutyElement → ⊥
wrongTypeIdentityDoesNotPayDutyElement ()

wrongTypeCannotBeBorrowedAcrossSystems :
  DutyResidualCanBorrowWrongTypeFromAnotherSystem → ⊥
wrongTypeCannotBeBorrowedAcrossSystems ()

wrongTypeCannotFloatFreeOfSource :
  WrongTypeReceiptMayFloatFreeOfSourceProposition → ⊥
wrongTypeCannotFloatFreeOfSource ()

directSourceFactDoesNotAutoPayReconstruction :
  DirectSourceFactAutomaticallyPaysReconstructedRoute → ⊥
directSourceFactDoesNotAutoPayReconstruction ()

cullenResidualAdmissionReading : String
cullenResidualAdmissionReading =
  "Separation identifies a consumer-relevant discriminator, but installation into the Cullen legal consumer fibre additionally requires the live applicability/source-authority meet to be welded to the exact Edelman [64] source realisation, the canonical Australian negligence WrongType, and its duty element. Direct source facts, DASHI reconstruction, WrongType identity, legal-element identity, applicability, and consumer sufficiency remain distinct obligations."
