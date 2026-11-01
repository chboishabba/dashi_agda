module DASHI.Law.HerzogColonialWrongTypeParetoProofPromotionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierProofPromotionExact as Proof
import DASHI.Law.HerzogColonialWrongTypeGenericParetoFrontierBridgeExact as Herzog

------------------------------------------------------------------------
-- HERZOG / COLONIAL WRONGTYPE PROOF PROMOTION
--
-- The executable frontier is promoted to explicit eligibility and
-- non-domination certificates at each live-fibre phase. This does not pay the
-- underlying translation requirement or create legal authority.
------------------------------------------------------------------------

currentAuthorityEligible : Proof.EligibleCertificate Herzog.currentAuthorityCell
currentAuthorityEligible = Proof.eligible-certificate refl refl refl refl

currentAuthorityNoDominator :
  ∀ {alternative} →
  Proof._∈_ alternative Herzog.currentPortfolio →
  Pareto.strictlyDominates? alternative Herzog.currentAuthorityCell ≡ false
currentAuthorityNoDominator Proof.here = refl
currentAuthorityNoDominator (Proof.there Proof.here) = refl
currentAuthorityNoDominator (Proof.there (Proof.there Proof.here)) = refl
currentAuthorityNoDominator (Proof.there (Proof.there (Proof.there ())))

currentAuthorityUndominated :
  Proof.UndominatedCertificate Herzog.currentPortfolio Herzog.currentAuthorityCell
currentAuthorityUndominated = Proof.undominated-certificate currentAuthorityNoDominator

currentAuthorityMembership :
  Proof.ParetoMembershipCertificate Herzog.currentPortfolio Herzog.currentAuthorityCell
currentAuthorityMembership =
  Proof.pareto-membership-certificate currentAuthorityEligible currentAuthorityUndominated

currentAuthorityPromotion :
  Proof.FrontierPromotion Herzog.currentPortfolio Herzog.currentAuthorityCell
currentAuthorityPromotion =
  Proof.frontier-promotion Herzog.currentAuthorityOnParetoFrontier currentAuthorityMembership

afterAuthorityPowerEligible :
  Proof.EligibleCertificate Herzog.afterAuthorityPowerCell
afterAuthorityPowerEligible = Proof.eligible-certificate refl refl refl refl

afterAuthorityPowerNoDominator :
  ∀ {alternative} →
  Proof._∈_ alternative Herzog.afterAuthorityPortfolio →
  Pareto.strictlyDominates? alternative Herzog.afterAuthorityPowerCell ≡ false
afterAuthorityPowerNoDominator Proof.here = refl
afterAuthorityPowerNoDominator (Proof.there Proof.here) = refl
afterAuthorityPowerNoDominator (Proof.there (Proof.there Proof.here)) = refl
afterAuthorityPowerNoDominator (Proof.there (Proof.there (Proof.there ())))

afterAuthorityPowerUndominated :
  Proof.UndominatedCertificate
    Herzog.afterAuthorityPortfolio Herzog.afterAuthorityPowerCell
afterAuthorityPowerUndominated =
  Proof.undominated-certificate afterAuthorityPowerNoDominator

afterAuthorityPowerMembership :
  Proof.ParetoMembershipCertificate
    Herzog.afterAuthorityPortfolio Herzog.afterAuthorityPowerCell
afterAuthorityPowerMembership =
  Proof.pareto-membership-certificate
    afterAuthorityPowerEligible afterAuthorityPowerUndominated

afterAuthorityPowerPromotion :
  Proof.FrontierPromotion
    Herzog.afterAuthorityPortfolio Herzog.afterAuthorityPowerCell
afterAuthorityPowerPromotion =
  Proof.frontier-promotion
    Herzog.afterAuthorityPowerOnParetoFrontier
    afterAuthorityPowerMembership

afterPowerIncidentEligible :
  Proof.EligibleCertificate Herzog.afterPowerIncidentCell
afterPowerIncidentEligible = Proof.eligible-certificate refl refl refl refl

afterPowerIncidentNoDominator :
  ∀ {alternative} →
  Proof._∈_ alternative Herzog.afterPowerPortfolio →
  Pareto.strictlyDominates? alternative Herzog.afterPowerIncidentCell ≡ false
afterPowerIncidentNoDominator Proof.here = refl
afterPowerIncidentNoDominator (Proof.there Proof.here) = refl
afterPowerIncidentNoDominator (Proof.there (Proof.there Proof.here)) = refl
afterPowerIncidentNoDominator (Proof.there (Proof.there (Proof.there ())))

afterPowerIncidentUndominated :
  Proof.UndominatedCertificate
    Herzog.afterPowerPortfolio Herzog.afterPowerIncidentCell
afterPowerIncidentUndominated =
  Proof.undominated-certificate afterPowerIncidentNoDominator

afterPowerIncidentMembership :
  Proof.ParetoMembershipCertificate
    Herzog.afterPowerPortfolio Herzog.afterPowerIncidentCell
afterPowerIncidentMembership =
  Proof.pareto-membership-certificate
    afterPowerIncidentEligible afterPowerIncidentUndominated

afterPowerIncidentPromotion :
  Proof.FrontierPromotion
    Herzog.afterPowerPortfolio Herzog.afterPowerIncidentCell
afterPowerIncidentPromotion =
  Proof.frontier-promotion refl afterPowerIncidentMembership

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data HerzogParetoCertificatePaysTranslation : Set where
data HerzogParetoCertificateCreatesColonialMechanism : Set where
data HerzogParetoCertificateCreatesApplicability : Set where

certificateDoesNotPayTranslation : HerzogParetoCertificatePaysTranslation → ⊥
certificateDoesNotPayTranslation ()

certificateDoesNotCreateMechanism : HerzogParetoCertificateCreatesColonialMechanism → ⊥
certificateDoesNotCreateMechanism ()

certificateDoesNotCreateApplicability : HerzogParetoCertificateCreatesApplicability → ⊥
certificateDoesNotCreateApplicability ()
