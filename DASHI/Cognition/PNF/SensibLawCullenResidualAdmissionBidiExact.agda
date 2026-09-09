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

------------------------------------------------------------------------
-- CULLEN RESIDUAL ADMISSION BIDI
--
-- Thin bridge over existing owners:
--
--   collision/separation      -> ConsumerIndexedResidualRefinementExact
--   discriminator             -> DiscriminatorSynthesisExact
--   source/authority/apply    -> ApplicabilityPrerequisiteMeetExact
--   WrongType / legal element -> NegligenceDutyWrongTypeSpecializationExact
--   source-correct legal term -> SensibLawCullenSourceCorrectDutyRoutesExact
--
-- No new factorisation, authority, applicability, WrongType, legal-element or
-- proof-search calculus is introduced here.
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

    sourceCorrectCoordinate : Routes.CullenReasoningRoute
    coordinateIsEdelmanRoute : sourceCorrectCoordinate ≡ Routes.edelmanReasons

    applicabilityMeet : Meet.ApplicabilityMeetInput state
    legalSourceAuthority : Authority.LegalSourceAuthorityReceiptInState state
    authorityIsMeetAuthority :
      legalSourceAuthority ≡
      Meet.legalSourceAuthority (Meet.prerequisites applicabilityMeet)

    wrongTypeIsNegligence :
      Meet.wrongType applicabilityMeet ≡ Negligence.negligenceWrongType

    targetElement : Elements.LegalElement Negligence.negligenceWrongType
    targetIsDuty : targetElement ≡ Negligence.dutyElement

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

------------------------------------------------------------------------
-- Once admission exists, the generic residual repair installs the strict
-- refinement. The source/applicability/WrongType gate does not create the
-- repair; it authorises use of a repair already proved consumer-sufficient.
------------------------------------------------------------------------

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
-- WrongType-target projection.
------------------------------------------------------------------------

admittedResidualTargetsNegligenceWrongType :
  ∀ {state} →
  (admitted : CullenAdmittedResidual state) →
  Meet.wrongType (applicabilityMeet admitted) ≡ Negligence.negligenceWrongType
admittedResidualTargetsNegligenceWrongType = wrongTypeIsNegligence

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
  Meet.wrongType meet ≡ Negligence.negligenceWrongType →
  Ontology.WrongType.definingSystem (Meet.wrongType meet)
    ≡ Negligence.auCommonLawSystem →
  CullenAdmittedResidual state
installCullenResidual meet authority sameAuthority sameWrongType sameSystem =
  cullen-admitted-residual
    Collision.statutoryPowerInspectionSeparatesCollision
    Routes.edelmanReasons
    refl
    meet
    authority
    sameAuthority
    sameWrongType
    Negligence.dutyElement
    refl
    sameSystem
    Collision.cullenStatutoryPowerResidualRepair
    "Cullen source-correct Edelman residual admitted only after the same-state applicability/source-authority meet is paid and welded to the canonical Australian negligence WrongType and duty element."

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

------------------------------------------------------------------------
-- Reading exported to the legal runtime.
------------------------------------------------------------------------

cullenResidualAdmissionReading : String
cullenResidualAdmissionReading =
  "Separation identifies a consumer-relevant discriminator, but installation into the Cullen legal consumer fibre additionally requires the existing same-object applicability/source-authority meet AND an exact weld to the canonical Australian negligence WrongType and its duty element. Discrimination, source authority, WrongType identity, legal-element identity, applicability, and consumer sufficiency remain separate proof obligations."
