module DASHI.Governance.EpistemicPowerStructuralRetentionExact where

-- Finite DASHI countermodels, not empirical claims or philosophical attributions.
-- No postulates, no unsafe pragmas. Kernel acceptance remains to be checked.

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as Intersection
import DASHI.Reasoning.TrialecticAttachedTwoCellExact as Trialectic
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

data Reform : Set where
  before after : Reform

data Vocabulary : Set where
  older newer : Vocabulary

data Authority : Set where
  sameFinalAuthority : Authority

data Material : Set where
  sameMaterialControl : Material

visible : Reform → Vocabulary
visible before = older
visible after = newer

authority : Reform → Authority
authority before = sameFinalAuthority
authority after = sameFinalAuthority

material : Reform → Material
material before = sameMaterialControl
material after = sameMaterialControl

record StructuralRetention
  {X V A M : Set}
  (view : X → V)
  (authorityMap : X → A)
  (materialMap : X → M)
  (x y : X) : Set where
  constructor retain
  field
    viewDiffers : view x ≡ view y → ⊥
    authorityEqual : authorityMap x ≡ authorityMap y
    materialEqual : materialMap x ≡ materialMap y

visibleRevisionRetainsAuthorityAndMaterial :
  StructuralRetention visible authority material before after
visibleRevisionRetainsAuthorityAndMaterial =
  retain (λ ()) refl refl

structuralRetentionDoesNotImplyAuthorityChange :
  StructuralRetention visible authority material before after →
  (authority before ≡ authority after → ⊥) → ⊥
structuralRetentionDoesNotImplyAuthorityChange evidence alleged =
  alleged (StructuralRetention.authorityEqual evidence)

data Consultation : Set where
  voiceOnly decisionRights : Consultation

data Report : Set where
  sameParticipation : Report

participation : Consultation → Report
participation voiceOnly = sameParticipation
participation decisionRights = sameParticipation

bindingAuthority : Consultation → Bool
bindingAuthority voiceOnly = false
bindingAuthority decisionRights = true

institutionalProjectionCannotRecoverAuthority :
  Intersection.NonFactorabilityWitness participation bindingAuthority
institutionalProjectionCannotRecoverAuthority =
  Intersection.nonFactorabilityWitness voiceOnly decisionRights refl (λ ())

participationRechartCannotRecoverAuthority :
  ∀ {R : Set} (rechart : Report → R) →
  Intersection.FactorsThrough
    (λ c → rechart (participation c)) bindingAuthority → ⊥
participationRechartCannotRecoverAuthority rechart =
  Intersection.rechartingCannotRecoverErasedPhenomenon
    rechart institutionalProjectionCannotRecoverAuthority

data History : Set where
  acceptedOnce repeatedlyReopened : History

data PublicFinding : Set where
  findingRetained : PublicFinding

publicFinding : History → PublicFinding
publicFinding acceptedOnce = findingRetained
publicFinding repeatedlyReopened = findingRetained

extraBurden : History → Bool
extraBurden acceptedOnce = false
extraBurden repeatedlyReopened = true

samePublicObservationDifferentHistoryBurden :
  Intersection.NonFactorabilityWitness publicFinding extraBurden
samePublicObservationDifferentHistoryBurden =
  Intersection.nonFactorabilityWitness acceptedOnce repeatedlyReopened
    refl (λ ())

rechartCannotRecoverHistoryBurden :
  ∀ {R : Set} (rechart : PublicFinding → R) →
  Intersection.FactorsThrough
    (λ h → rechart (publicFinding h)) extraBurden → ⊥
rechartCannotRecoverHistoryBurden rechart =
  Intersection.rechartingCannotRecoverErasedPhenomenon
    rechart samePublicObservationDifferentHistoryBurden

exhaustionWithoutBeliefDefeat :
  publicFinding acceptedOnce ≡ publicFinding repeatedlyReopened
  × (extraBurden acceptedOnce ≡ extraBurden repeatedlyReopened → ⊥)
exhaustionWithoutBeliefDefeat = refl , (λ ())

-- The preceding is a workload contrast, not psychological exhaustion.
data InclusionCase : Set where
  inclusionOnly inclusionPlusMaterialChange : InclusionCase

data InclusionMetric : Set where
  identicalInclusion : InclusionMetric

inclusion : InclusionCase → InclusionMetric
inclusion inclusionOnly = identicalInclusion
inclusion inclusionPlusMaterialChange = identicalInclusion

landCommitment : InclusionCase → Bool
landCommitment inclusionOnly = false
landCommitment inclusionPlusMaterialChange = true

sovereigntyCommitment : InclusionCase → Bool
sovereigntyCommitment inclusionOnly = false
sovereigntyCommitment inclusionPlusMaterialChange = true

socialJusticeEvidenceCannotAutoDischargeLandCommitment :
  Intersection.NonFactorabilityWitness inclusion landCommitment
socialJusticeEvidenceCannotAutoDischargeLandCommitment =
  Intersection.nonFactorabilityWitness
    inclusionOnly inclusionPlusMaterialChange refl (λ ())

socialJusticeEvidenceCannotAutoDischargeSovereignty :
  Intersection.NonFactorabilityWitness inclusion sovereigntyCommitment
socialJusticeEvidenceCannotAutoDischargeSovereignty =
  Intersection.nonFactorabilityWitness
    inclusionOnly inclusionPlusMaterialChange refl (λ ())

inclusionRechartCannotProveLandCommitment :
  ∀ {R : Set} (rechart : InclusionMetric → R) →
  Intersection.FactorsThrough
    (λ c → rechart (inclusion c)) landCommitment → ⊥
inclusionRechartCannotProveLandCommitment rechart =
  Intersection.rechartingCannotRecoverErasedPhenomenon
    rechart socialJusticeEvidenceCannotAutoDischargeLandCommitment

sameDyadsCannotDetermineAttachedFace :
  Descent.FactorsThrough
    Trialectic.attachedBoundaryObserver
    Trialectic.attachedFaceConsumer → ⊥
sameDyadsCannotDetermineAttachedFace =
  Trialectic.attachedFaceDoesNotFactorThroughBoundary

-- Four independent support states, not an identity with catuskoti.
data EvidenceStatus : Set where
  affirmed denied conflicting undetermined : EvidenceStatus

positive : EvidenceStatus → Bool
positive affirmed = true
positive denied = false
positive conflicting = true
positive undetermined = false

negative : EvidenceStatus → Bool
negative affirmed = false
negative denied = true
negative conflicting = true
negative undetermined = false

encode : Bool → Bool → EvidenceStatus
encode true false = affirmed
encode false true = denied
encode true true = conflicting
encode false false = undetermined

fourEvidenceStatusesExhaustive :
  (s : EvidenceStatus) → encode (positive s) (negative s) ≡ s
fourEvidenceStatusesExhaustive affirmed = refl
fourEvidenceStatusesExhaustive denied = refl
fourEvidenceStatusesExhaustive conflicting = refl
fourEvidenceStatusesExhaustive undetermined = refl

fourEvidenceStatusesEncodeBothFlags :
  (p n : Bool) →
  (positive (encode p n) ≡ p) × (negative (encode p n) ≡ n)
fourEvidenceStatusesEncodeBothFlags true true = refl , refl
fourEvidenceStatusesEncodeBothFlags true false = refl , refl
fourEvidenceStatusesEncodeBothFlags false true = refl , refl
fourEvidenceStatusesEncodeBothFlags false false = refl , refl

data ArbitraryUnsupportedClaim : Set where

conflictStatusDoesNotExplode :
  (conflicting ≡ conflicting → ArbitraryUnsupportedClaim) → ⊥
conflictStatusDoesNotExplode claim = impossible (claim refl)
  where
    impossible : ArbitraryUnsupportedClaim → ⊥
    impossible ()
