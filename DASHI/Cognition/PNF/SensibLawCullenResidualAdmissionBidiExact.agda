module DASHI.Cognition.PNF.SensibLawCullenResidualAdmissionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.DiscriminatorSynthesisExact as Synthesis
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawApplicabilityPrerequisiteMeetExact as Meet
import DASHI.Cognition.PNF.SensibLawLegalSourceAuthorityEvidenceExact as Authority
import DASHI.Cognition.PNF.SensibLawCullenConsumerCollisionMissingCoordinateExact as Collision
import DASHI.Cognition.PNF.SensibLawCullenSourceCorrectDutyRoutesExact as Routes

------------------------------------------------------------------------
-- CULLEN RESIDUAL ADMISSION BIDI
--
-- This is intentionally a thin bridge over existing owners:
--
--   collision/separation      -> ConsumerIndexedResidualRefinementExact
--   discriminator             -> DiscriminatorSynthesisExact
--   source/authority/apply    -> ApplicabilityPrerequisiteMeetExact
--   source-correct legal term -> SensibLawCullenSourceCorrectDutyRoutesExact
--
-- No new factorisation, authority, applicability or proof-search calculus is
-- introduced here.
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

    residualRepair :
      Consumer.ResidualRepair
        Collision.observePoliceFunctionContext
        Collision.inspectStatutoryPower
        Collision.legacyBundledPremiseConsumer

    admissionReference : String

open CullenAdmittedResidual public

------------------------------------------------------------------------
-- Once admission exists, the generic residual repair installs the strict
-- refinement. The source/applicability gate does not create the repair; it
-- authorises use of a repair already proved consumer-sufficient.
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
-- The canonical Cullen separator/repair can be lifted into this gate whenever
-- the existing legal-source/applicability meet has been paid on the same state.
------------------------------------------------------------------------

installCullenResidual :
  ∀ {state} →
  (meet : Meet.ApplicabilityMeetInput state) →
  (authority : Authority.LegalSourceAuthorityReceiptInState state) →
  authority ≡ Meet.legalSourceAuthority (Meet.prerequisites meet) →
  CullenAdmittedResidual state
installCullenResidual meet authority sameAuthority =
  cullen-admitted-residual
    Collision.statutoryPowerInspectionSeparatesCollision
    Routes.edelmanReasons
    refl
    meet
    authority
    sameAuthority
    Collision.cullenStatutoryPowerResidualRepair
    "Cullen source-correct Edelman residual admitted only after the existing same-state applicability/source-authority meet is paid."

------------------------------------------------------------------------
-- Hard non-promotions.
------------------------------------------------------------------------

data SeparatorAloneInstallsLegalResidual : Set where
data LegalSourceAuthorityAloneProvesConsumerSufficiency : Set where
data ApplicabilityMeetTurnsDashReconstructionIntoRatio : Set where
data ResidualRepairAloneEstablishesApplicability : Set where

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

------------------------------------------------------------------------
-- Reading exported to the legal runtime.
------------------------------------------------------------------------

cullenResidualAdmissionReading : String
cullenResidualAdmissionReading =
  "Separation identifies a consumer-relevant discriminator, but installation into the legal consumer fibre additionally requires the existing same-object applicability/source-authority meet. Applicability/authority does not construct the separator, separator does not construct authority, and the compiled Cullen route remains DASHI reconstruction unless independently classified otherwise."
