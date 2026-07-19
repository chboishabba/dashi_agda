module DASHI.Foundations.CategoryPolisBoundaryTests where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.CategoryPolisBoundary

humanScientificIncluded :
  scientificAdaptiveStanding humanSubject ≡ included
humanScientificIncluded = refl

slimeMouldScientificIncluded :
  scientificAdaptiveStanding slimeMouldSubject ≡ included
slimeMouldScientificIncluded = refl

artificialSystemScientificIncluded :
  scientificAdaptiveStanding artificialSystemSubject ≡ included
artificialSystemScientificIncluded = refl

riverScientificHeld :
  scientificAdaptiveStanding riverSubject ≡ held
riverScientificHeld = refl

riverHumanOnlyExcluded :
  humanOnlyPolis riverSubject ≡ excluded
riverHumanOnlyExcluded = refl

riverEcologicalIncluded :
  ecologicalPolis riverSubject ≡ included
riverEcologicalIncluded = refl

riverPolicyCountermodel :
  ¬ (humanOnlyPolis riverSubject ≡ ecologicalPolis riverSubject)
riverPolicyCountermodel = riverPolisDivergence

slimeMouldPolicyCountermodel :
  ¬ (humanOnlyPolis slimeMouldSubject ≡
     ecologicalPolis slimeMouldSubject)
slimeMouldPolicyCountermodel = slimeMouldPolisDivergence

unbridgedSciencePromotionRejected :
  unbridgedPromotion scientificJudgement
    ecologicalPoliticalJudgement ≡ false
unbridgedSciencePromotionRejected = refl

unsafeApplicationExcluded :
  safetyPolicy unsafeEvidence ≡ excluded
unsafeApplicationExcluded = refl

unresolvedApplicationHeld :
  safetyPolicy unresolvedEvidence ≡ held
unresolvedApplicationHeld = refl

safeApplicationIncluded :
  safetyPolicy safeEvidence ≡ included
safeApplicationIncluded = refl

scienceAffectsAppliedBoundary :
  ¬ (safetyPolicy unsafeEvidence ≡ safetyPolicy safeEvidence)
scienceAffectsAppliedBoundary = safeEvidenceChangesStanding

geneTherapyBridgeApplies :
  resultingStanding geneTherapySafeCrossover ≡ included
geneTherapyBridgeApplies = refl

cloningBridgeRemainsHeld :
  resultingStanding cloningHeldCrossover ≡ held
cloningBridgeRemainsHeld = refl

fullBoundaryWitness : CategoryPolisBoundary
fullBoundaryWitness = categoryPolisBoundary
