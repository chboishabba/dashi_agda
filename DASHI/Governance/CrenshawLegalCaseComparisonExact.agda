module DASHI.Governance.CrenshawLegalCaseComparisonExact where

-- Court-attributed bounded procedural readings versus DASHI formal witnesses.
-- Each court's judgment retains its own source and disposition. Crenshaw
-- (1989) owns the scholarly critique, not these judicial holdings.
-- These are reconstruction predicates, not empirical or legal promotion.

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.IntersectionalBinaryInteractionBridgeExact as Joint
import DASHI.Core.BinaryInteractionNonseparabilityExact as Interaction
import DASHI.Governance.CrenshawLegalPrimaryCaseAtlasExact as Cases

-- Four independent questions, not one scalar judgment.
data JudicialQuestion : Set where
  recognisedCombinedClaim liabilityEstablished classRepresentable remedyOrdered : JudicialQuestion

data ProceduralState : Set where
  recognitionOnly recognitionAndLiability : ProceduralState

observedRecognition : ProceduralState → Bool
observedRecognition recognitionOnly = true
observedRecognition recognitionAndLiability = true

liability : ProceduralState → Bool
liability recognitionOnly = false
liability recognitionAndLiability = true

-- A finite logical independence model. Its worlds are not historical cases.
recognitionCannotDecideLiability :
  INF.NonFactorabilityWitness observedRecognition liability
recognitionCannotDecideLiability =
  INF.nonFactorabilityWitness
    recognitionOnly recognitionAndLiability refl (λ ())

recognitionDoesNotEstablishMerits :
  INF.FactorsThrough observedRecognition liability → ⊥
recognitionDoesNotEstablishMerits =
  INF.witnessRulesOutEveryFlatFactorisation
    recognitionCannotDecideLiability

anyRecognitionRechartCannotDecideLiability :
  ∀ {R : Set} (f : Bool → R) →
  INF.FactorsThrough (λ x → f (observedRecognition x)) liability → ⊥
anyRecognitionRechartCannotDecideLiability f =
  INF.rechartingCannotRecoverErasedPhenomenon
    f recognitionCannotDecideLiability

data CourtReading : Set where
  deGraffenreidDistrictReading : CourtReading
  deGraffenreidAppealReading : CourtReading
  jefferiesAppellateReading : CourtReading

sourceStage : CourtReading → Cases.CourtStage
sourceStage deGraffenreidDistrictReading = Cases.districtCourt
sourceStage deGraffenreidAppealReading = Cases.appellateCourt
sourceStage jefferiesAppellateReading = Cases.appellateCourt

underlyingCase : CourtReading → Cases.CaseKey
underlyingCase deGraffenreidDistrictReading = Cases.deGraffenreid
underlyingCase deGraffenreidAppealReading = Cases.deGraffenreid
underlyingCase jefferiesAppellateReading = Cases.jefferies

data CombinationTreatment : Set where
  rejectsAsSeparateCategory addressesOtherAppealGrounds
  recognisesCombinedCategory : CombinationTreatment

boundedTreatment : CourtReading → CombinationTreatment
boundedTreatment deGraffenreidDistrictReading = rejectsAsSeparateCategory
boundedTreatment deGraffenreidAppealReading = addressesOtherAppealGrounds
boundedTreatment jefferiesAppellateReading = recognisesCombinedCategory

deGraffenreidTrialVsAppealClaimSameCase :
  underlyingCase deGraffenreidDistrictReading
    ≡ underlyingCase deGraffenreidAppealReading
  × (sourceStage deGraffenreidDistrictReading
    ≡ sourceStage deGraffenreidAppealReading → ⊥)
deGraffenreidTrialVsAppealClaimSameCase =
  refl , (λ ())

jefferiesIntersectionalRecognitionPositiveControl :
  boundedTreatment jefferiesAppellateReading ≡ recognisesCombinedCategory
jefferiesIntersectionalRecognitionPositiveControl = refl

jefferiesRecognisedNotProved :
  Cases.ProceduralCaseStatus.recognition Cases.jefferiesCombinationAtRemand
    ≡ Cases.claimRecognised
  × (Cases.ProceduralCaseStatus.merits Cases.jefferiesCombinationAtRemand
    ≡ Cases.meritsNotDetermined)
jefferiesRecognisedNotProved = refl , refl

deGraffenreidDistrictNotJefferiesAppellate :
  boundedTreatment deGraffenreidDistrictReading
    ≡ boundedTreatment jefferiesAppellateReading → ⊥
deGraffenreidDistrictNotJefferiesAppellate ()

-- Reuse of intersectional interaction non-additivity is mathematical
-- DASHI prior art, NOT a theorem proved by the courts or by Crenshaw.
jointOnlyInteractionHasExistingObstruction :
  Interaction.NonseparableAdditiveInteraction
    Joint.intersectionInteractionSurface
jointOnlyInteractionHasExistingObstruction =
  Joint.intersectionInteractionNotEndpointAdditive
