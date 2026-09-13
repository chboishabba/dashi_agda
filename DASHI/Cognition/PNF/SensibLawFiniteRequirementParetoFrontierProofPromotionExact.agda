module DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierProofPromotionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto

------------------------------------------------------------------------
-- PROOF-RELEVANT PROMOTION FOR THE EXECUTABLE PARETO FRONTIER
--
-- DASHI synthesis. `onParetoFrontier? = true` is an executable search result.
-- Promotion additionally carries explicit witnesses that the selected cell is
-- required/relevant/admissible/live-splitting and that no declared alternative
-- strictly dominates it. Boolean success is therefore not definitionally a
-- theorem object.
------------------------------------------------------------------------

infix 4 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

record EligibleCertificate
    {Requirement : Set}
    (cell : Pareto.RequirementCandidate Requirement) : Set where
  constructor eligible-certificate
  field
    requiredWitness : Pareto.requiredForConsumer cell ≡ true
    relevantWitness : Pareto.consumerRelevant cell ≡ true
    authorityWitness : Pareto.authorityAdmissible cell ≡ true
    liveSplitWitness : Pareto.splitsCurrentLiveFibre cell ≡ true

open EligibleCertificate public

record UndominatedCertificate
    {Requirement : Set}
    (portfolio : List (Pareto.RequirementCandidate Requirement))
    (selected : Pareto.RequirementCandidate Requirement) : Set₁ where
  constructor undominated-certificate
  field
    noStrictDominator :
      ∀ {alternative} →
      alternative ∈ portfolio →
      Pareto.strictlyDominates? alternative selected ≡ false

open UndominatedCertificate public

record ParetoMembershipCertificate
    {Requirement : Set}
    (portfolio : List (Pareto.RequirementCandidate Requirement))
    (selected : Pareto.RequirementCandidate Requirement) : Set₁ where
  constructor pareto-membership-certificate
  field
    eligibleCertificate : EligibleCertificate selected
    undominatedCertificate : UndominatedCertificate portfolio selected

open ParetoMembershipCertificate public

record FrontierPromotion
    {Requirement : Set}
    (portfolio : List (Pareto.RequirementCandidate Requirement))
    (selected : Pareto.RequirementCandidate Requirement) : Set₁ where
  constructor frontier-promotion
  field
    executableHit : Pareto.onParetoFrontier? portfolio selected ≡ true
    proofCertificate : ParetoMembershipCertificate portfolio selected

open FrontierPromotion public

------------------------------------------------------------------------
-- Exact generic calibration: both Pareto trade-off cells are promoted.
------------------------------------------------------------------------

cheapEligible : EligibleCertificate Pareto.cheapCell
cheapEligible = eligible-certificate refl refl refl refl

cheapNoDominator :
  ∀ {alternative} →
  alternative ∈ Pareto.toyPortfolio →
  Pareto.strictlyDominates? alternative Pareto.cheapCell ≡ false
cheapNoDominator here = refl
cheapNoDominator (there here) = refl
cheapNoDominator (there (there here)) = refl
cheapNoDominator (there (there (there here))) = refl
cheapNoDominator (there (there (there (there ()))))

cheapUndominated : UndominatedCertificate Pareto.toyPortfolio Pareto.cheapCell
cheapUndominated = undominated-certificate cheapNoDominator

cheapMembership : ParetoMembershipCertificate Pareto.toyPortfolio Pareto.cheapCell
cheapMembership = pareto-membership-certificate cheapEligible cheapUndominated

cheapPromotion : FrontierPromotion Pareto.toyPortfolio Pareto.cheapCell
cheapPromotion = frontier-promotion Pareto.cheapIsOnFrontier cheapMembership

highGainEligible : EligibleCertificate Pareto.highGainCell
highGainEligible = eligible-certificate refl refl refl refl

highGainNoDominator :
  ∀ {alternative} →
  alternative ∈ Pareto.toyPortfolio →
  Pareto.strictlyDominates? alternative Pareto.highGainCell ≡ false
highGainNoDominator here = refl
highGainNoDominator (there here) = refl
highGainNoDominator (there (there here)) = refl
highGainNoDominator (there (there (there here))) = refl
highGainNoDominator (there (there (there (there ()))))

highGainUndominated :
  UndominatedCertificate Pareto.toyPortfolio Pareto.highGainCell
highGainUndominated = undominated-certificate highGainNoDominator

highGainMembership :
  ParetoMembershipCertificate Pareto.toyPortfolio Pareto.highGainCell
highGainMembership = pareto-membership-certificate highGainEligible highGainUndominated

highGainPromotion : FrontierPromotion Pareto.toyPortfolio Pareto.highGainCell
highGainPromotion = frontier-promotion Pareto.highGainIsOnFrontier highGainMembership

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data BooleanFrontierHitCreatesProofCertificate : Set where
data ParetoCertificatePaysRequirement : Set where
data ParetoCertificateCreatesAuthority : Set where
data ParetoCertificateScalarisesTradeoffs : Set where

booleanHitDoesNotForgeProof : BooleanFrontierHitCreatesProofCertificate → ⊥
booleanHitDoesNotForgeProof ()

certificateDoesNotPayRequirement : ParetoCertificatePaysRequirement → ⊥
certificateDoesNotPayRequirement ()

certificateDoesNotCreateAuthority : ParetoCertificateCreatesAuthority → ⊥
certificateDoesNotCreateAuthority ()

certificateDoesNotScalarise : ParetoCertificateScalarisesTradeoffs → ⊥
certificateDoesNotScalarise ()
