module DASHI.Cognition.PNF.SensibLawNegligenceDutyParetoProofPromotionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierProofPromotionExact as Proof
import DASHI.Cognition.PNF.SensibLawNegligenceDutyGenericParetoFrontierExact as Duty

------------------------------------------------------------------------
-- DUTY-OF-CARE PROOF PROMOTION
--
-- DASHI scheduler synthesis over the already sourced negligence/duty
-- coordinates. This proves Pareto membership in the declared finite portfolio;
-- it does not turn the selected research question into a duty holding.
------------------------------------------------------------------------

corePolicyEligible : Proof.EligibleCertificate Duty.currentCorePolicyCell
corePolicyEligible = Proof.eligible-certificate refl refl refl refl

corePolicyNoDominator :
  ∀ {alternative} →
  Proof._∈_ alternative Duty.currentDutyPortfolio →
  Pareto.strictlyDominates? alternative Duty.currentCorePolicyCell ≡ false
corePolicyNoDominator Proof.here = refl
corePolicyNoDominator (Proof.there Proof.here) = refl
corePolicyNoDominator (Proof.there (Proof.there Proof.here)) = refl
corePolicyNoDominator (Proof.there (Proof.there (Proof.there ())))

corePolicyUndominated :
  Proof.UndominatedCertificate Duty.currentDutyPortfolio Duty.currentCorePolicyCell
corePolicyUndominated = Proof.undominated-certificate corePolicyNoDominator

corePolicyMembership :
  Proof.ParetoMembershipCertificate Duty.currentDutyPortfolio Duty.currentCorePolicyCell
corePolicyMembership =
  Proof.pareto-membership-certificate corePolicyEligible corePolicyUndominated

corePolicyPromotion :
  Proof.FrontierPromotion Duty.currentDutyPortfolio Duty.currentCorePolicyCell
corePolicyPromotion =
  Proof.frontier-promotion Duty.corePolicyIsCurrentParetoQuestion corePolicyMembership

statutoryCoherenceEligible :
  Proof.EligibleCertificate Duty.postPolicyStatutoryCoherenceCell
statutoryCoherenceEligible = Proof.eligible-certificate refl refl refl refl

statutoryCoherenceNoDominator :
  ∀ {alternative} →
  Proof._∈_ alternative Duty.postPolicyPortfolio →
  Pareto.strictlyDominates? alternative Duty.postPolicyStatutoryCoherenceCell ≡ false
statutoryCoherenceNoDominator Proof.here = refl
statutoryCoherenceNoDominator (Proof.there Proof.here) = refl
statutoryCoherenceNoDominator (Proof.there (Proof.there Proof.here)) = refl
statutoryCoherenceNoDominator (Proof.there (Proof.there (Proof.there ())))

statutoryCoherenceUndominated :
  Proof.UndominatedCertificate
    Duty.postPolicyPortfolio
    Duty.postPolicyStatutoryCoherenceCell
statutoryCoherenceUndominated =
  Proof.undominated-certificate statutoryCoherenceNoDominator

statutoryCoherenceMembership :
  Proof.ParetoMembershipCertificate
    Duty.postPolicyPortfolio
    Duty.postPolicyStatutoryCoherenceCell
statutoryCoherenceMembership =
  Proof.pareto-membership-certificate
    statutoryCoherenceEligible statutoryCoherenceUndominated

statutoryCoherencePromotion :
  Proof.FrontierPromotion
    Duty.postPolicyPortfolio
    Duty.postPolicyStatutoryCoherenceCell
statutoryCoherencePromotion =
  Proof.frontier-promotion
    Duty.statutoryCoherenceBecomesParetoQuestion
    statutoryCoherenceMembership

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DutyParetoCertificateIsDutyHolding : Set where
data CorePolicyParetoCertificateIsCategoricalNoDutyRule : Set where
data StatutoryParetoCertificateMeansStatutoryConflictExists : Set where

certificateDoesNotCreateDuty : DutyParetoCertificateIsDutyHolding → ⊥
certificateDoesNotCreateDuty ()

corePolicyCertificateDoesNotCreateNoDutyRule :
  CorePolicyParetoCertificateIsCategoricalNoDutyRule → ⊥
corePolicyCertificateDoesNotCreateNoDutyRule ()

statutoryCertificateDoesNotDecideConflict :
  StatutoryParetoCertificateMeansStatutoryConflictExists → ⊥
statutoryCertificateDoesNotDecideConflict ()
