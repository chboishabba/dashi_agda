module DASHI.Culture.PowersPlantationParadiseGovernedCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.RequiredObserverAxisJoinAdequacyExact as Join
import DASHI.Core.GovernedObservationProvenanceExact as Governed
import DASHI.Core.RecognitionConstitutionNonfactorabilityExact as Recognition
import DASHI.Core.PoliticalContestabilityExact as Political
import DASHI.Core.SituatedFormalisationBoundaryExact as Situated
import DASHI.Governance.OptionConeCoercionExact as OptionCone
import DASHI.Governance.HistoryConditionedSocialEcologyOptionConeExact as HistoryCone
import DASHI.Governance.AsymmetricLegibilityContestabilityExact as Legibility
import DASHI.Culture.LanguageUseGovernedStandingBidiExact as Language
import DASHI.Culture.PowersPlantationParadiseHistoricalClaimReceiptsExact as Claims
import DASHI.Cognition.PNF.SensibLawPersistentStatementObservationEventSpineExact as Trace
import DASHI.Cognition.PNF.SensibLawChronologyContestationSpineExact as Contest
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesNarrativeGovernanceWeldExact as Rooted

------------------------------------------------------------------------
-- POWERS GOVERNED CROSS-POLLINATION
--
-- This module does not introduce another colonial-theory ontology.  It welds
-- the Powers-specific historical surface to already-merged generic owners for
-- governed provenance, recognition/constitution, political contestability,
-- consumer-relative residual refinement, required observer-axis joins,
-- asymmetric legibility/contestability, history-conditioned option cones,
-- governed language/use standing, situated formalisation and exact rooted
-- source traces.
--
-- The finite same-object witness is a DASHI construction.  It is not attributed
-- to Powers and is not an empirical population law.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. One cultural/public surface can coexist with different standing,
--    contestability and material/action-cone coordinates.
------------------------------------------------------------------------

data CulturalState : Set where
  visibleRestricted : CulturalState
  visibleExpanded : CulturalState

data CulturalSurface : Set where
  sameCulturalSurface : CulturalSurface

data StandingCode : Set where
  restrictedStanding expandedStanding : StandingCode

data ContestabilityCode : Set where
  restrictedContestability expandedContestability : ContestabilityCode

data MaterialConeCode : Set where
  contractedMaterialCone expandedMaterialCone : MaterialConeCode

data AuthorityCode : Set where
  restrictedAuthority expandedAuthority : AuthorityCode

culturalSurface : CulturalState → CulturalSurface
culturalSurface _ = sameCulturalSurface

standingCode : CulturalState → StandingCode
standingCode visibleRestricted = restrictedStanding
standingCode visibleExpanded = expandedStanding

contestabilityCode : CulturalState → ContestabilityCode
contestabilityCode visibleRestricted = restrictedContestability
contestabilityCode visibleExpanded = expandedContestability

materialConeCode : CulturalState → MaterialConeCode
materialConeCode visibleRestricted = contractedMaterialCone
materialConeCode visibleExpanded = expandedMaterialCone

authorityCode : CulturalState → AuthorityCode
authorityCode visibleRestricted = restrictedAuthority
authorityCode visibleExpanded = expandedAuthority

standingDiffers :
  standingCode visibleRestricted ≡ standingCode visibleExpanded → ⊥
standingDiffers ()

contestabilityDiffers :
  contestabilityCode visibleRestricted ≡ contestabilityCode visibleExpanded → ⊥
contestabilityDiffers ()

materialConeDiffers :
  materialConeCode visibleRestricted ≡ materialConeCode visibleExpanded → ⊥
materialConeDiffers ()

authorityDiffers :
  authorityCode visibleRestricted ≡ authorityCode visibleExpanded → ⊥
authorityDiffers ()

standingNonFactorabilityWitness :
  INF.NonFactorabilityWitness culturalSurface standingCode
standingNonFactorabilityWitness =
  INF.nonFactorabilityWitness
    visibleRestricted visibleExpanded refl standingDiffers

contestabilityNonFactorabilityWitness :
  INF.NonFactorabilityWitness culturalSurface contestabilityCode
contestabilityNonFactorabilityWitness =
  INF.nonFactorabilityWitness
    visibleRestricted visibleExpanded refl contestabilityDiffers

materialConeNonFactorabilityWitness :
  INF.NonFactorabilityWitness culturalSurface materialConeCode
materialConeNonFactorabilityWitness =
  INF.nonFactorabilityWitness
    visibleRestricted visibleExpanded refl materialConeDiffers

sameCulturalSurfaceCannotRecoverStanding :
  INF.FactorsThrough culturalSurface standingCode → ⊥
sameCulturalSurfaceCannotRecoverStanding =
  INF.witnessRulesOutEveryFlatFactorisation standingNonFactorabilityWitness

sameCulturalSurfaceCannotRecoverContestability :
  INF.FactorsThrough culturalSurface contestabilityCode → ⊥
sameCulturalSurfaceCannotRecoverContestability =
  INF.witnessRulesOutEveryFlatFactorisation contestabilityNonFactorabilityWitness

sameCulturalSurfaceCannotRecoverMaterialCone :
  INF.FactorsThrough culturalSurface materialConeCode → ⊥
sameCulturalSurfaceCannotRecoverMaterialCone =
  INF.witnessRulesOutEveryFlatFactorisation materialConeNonFactorabilityWitness

------------------------------------------------------------------------
-- 2. Required-axis join: standing, contestability and material accessibility
--    are jointly required coordinates when that consumer is declared.
------------------------------------------------------------------------

standingContestabilityJoint :
  CulturalState → StandingCode × ContestabilityCode
standingContestabilityJoint = Join.jointAxis standingCode contestabilityCode

governedSocialPositionJoint :
  CulturalState → (StandingCode × ContestabilityCode) × MaterialConeCode
governedSocialPositionJoint =
  Join.jointAxis standingContestabilityJoint materialConeCode

candidateRetainingAllThreeRetainsJointPosition :
  ∀ {Observation : Set}
    {candidate : CulturalState → Observation} →
  Join.RetainsAxis candidate standingCode →
  Join.RetainsAxis candidate contestabilityCode →
  Join.RetainsAxis candidate materialConeCode →
  Join.RetainsAxis candidate governedSocialPositionJoint
candidateRetainingAllThreeRetainsJointPosition
  standingFactor contestabilityFactor materialFactor =
  Join.candidateRetainingBothRetainsJoint
    (Join.candidateRetainingBothRetainsJoint
      standingFactor contestabilityFactor)
    materialFactor

sameCulturalSurfaceCannotRetainStandingAndContestability :
  Join.RetainsBothRequiredAxes
    culturalSurface standingCode contestabilityCode → ⊥
sameCulturalSurfaceCannotRetainStandingAndContestability =
  Join.leftAxisDefectBlocksRetainingBoth standingNonFactorabilityWitness

governedSocialPositionDiffers :
  governedSocialPositionJoint visibleRestricted
  ≡ governedSocialPositionJoint visibleExpanded → ⊥
governedSocialPositionDiffers same =
  standingDiffers (cong (λ pair → proj₁ (proj₁ pair)) same)

governedSocialPositionNonFactorabilityWitness :
  INF.NonFactorabilityWitness culturalSurface governedSocialPositionJoint
governedSocialPositionNonFactorabilityWitness =
  INF.nonFactorabilityWitness
    visibleRestricted visibleExpanded refl governedSocialPositionDiffers

sameCulturalSurfaceCannotRetainGovernedSocialPosition :
  Join.RetainsAxis culturalSurface governedSocialPositionJoint → ⊥
sameCulturalSurfaceCannotRetainGovernedSocialPosition =
  INF.witnessRulesOutEveryFlatFactorisation
    governedSocialPositionNonFactorabilityWitness

------------------------------------------------------------------------
-- 3. Asymmetric institutional legibility on the same carrier.
--
-- The institutional view retains the full governed-position joint while the
-- disclosed/public cultural surface collapses the selected pair.  Therefore an
-- exact decoder from the public surface back to institutional classification is
-- impossible.  This finite construction does not assert that a named colonial
-- theatre actually implemented such a classifier; it owns the theorem shape.
------------------------------------------------------------------------

powersLegibilityChannel : Legibility.LegibilityChannel
powersLegibilityChannel =
  Legibility.legibilityChannel
    CulturalState
    ((StandingCode × ContestabilityCode) × MaterialConeCode)
    CulturalSurface
    governedSocialPositionJoint
    (λ position → sameCulturalSurface)

powersAsymmetricLegibilityGap :
  Legibility.AsymmetricLegibilityWitness powersLegibilityChannel
powersAsymmetricLegibilityGap =
  Legibility.asymmetricLegibilityWitness
    visibleRestricted
    visibleExpanded
    governedSocialPositionDiffers
    refl

powersExactInstitutionalViewDecoderImpossible :
  Legibility.ExactInstitutionalViewDecoder powersLegibilityChannel → ⊥
powersExactInstitutionalViewDecoderImpossible =
  Legibility.asymmetricGapBlocksExactSubjectRecovery
    powersAsymmetricLegibilityGap

data ExplanationAvailable : CulturalState → Set where
  expandedExplanation : ExplanationAvailable visibleExpanded

data AppealAvailable : CulturalState → Set where
  expandedAppeal : AppealAvailable visibleExpanded

data CorrectionAvailable : CulturalState → Set where
  expandedCorrection : CorrectionAvailable visibleExpanded

powersContestabilityInterface :
  Legibility.ContestabilityInterface powersLegibilityChannel
powersContestabilityInterface =
  Legibility.contestabilityInterface
    ExplanationAvailable
    AppealAvailable
    CorrectionAvailable

expandedInstitutionalContestabilityReceipt :
  Legibility.ContestabilityReceipt
    powersContestabilityInterface visibleExpanded
expandedInstitutionalContestabilityReceipt =
  Legibility.contestabilityReceipt
    expandedExplanation
    expandedAppeal
    expandedCorrection

------------------------------------------------------------------------
-- 4. Recognition != constitution/authority on the same carrier.
------------------------------------------------------------------------

recognitionSystem :
  Recognition.RecognitionSystem CulturalState CulturalSurface AuthorityCode
recognitionSystem =
  Recognition.recognitionSystem culturalSurface authorityCode

recognitionCollision : Recognition.RecognitionCollision recognitionSystem
recognitionCollision =
  Recognition.recognitionCollision
    visibleRestricted visibleExpanded refl authorityDiffers

sameRecognitionCannotRecoverAuthority :
  Recognition.FactorsThroughRecognition recognitionSystem → ⊥
sameRecognitionCannotRecoverAuthority =
  Recognition.collisionBlocksAuthorityFactorization recognitionCollision

------------------------------------------------------------------------
-- 5. Governed-observer and consumer-relative consequences.
------------------------------------------------------------------------

standingCollision :
  Consumer.ConsumerRelevantCollision culturalSurface standingCode
standingCollision =
  Consumer.consumer-relevant-collision
    visibleRestricted visibleExpanded refl standingDiffers

contestabilityCollision :
  Consumer.ConsumerRelevantCollision culturalSurface contestabilityCode
contestabilityCollision =
  Consumer.consumer-relevant-collision
    visibleRestricted visibleExpanded refl contestabilityDiffers

materialConeCollision :
  Consumer.ConsumerRelevantCollision culturalSurface materialConeCode
materialConeCollision =
  Consumer.consumer-relevant-collision
    visibleRestricted visibleExpanded refl materialConeDiffers

culturalSurfaceCannotPayGovernedStanding :
  ∀ {Value Provenance Epistemic Permission Obligation : Set}
    {value : CulturalState → Value}
    {provenance : CulturalState → Provenance}
    {epistemic : CulturalState → Epistemic}
    {permission : CulturalState → Permission}
    {obligation : CulturalState → Obligation} →
  Governed.GovernedConsumerSufficiency
    culturalSurface value provenance epistemic standingCode permission obligation → ⊥
culturalSurfaceCannotPayGovernedStanding =
  Governed.authorityCollisionBlocksGovernedSufficiency standingCollision

everyAdequateStandingObserverSeparates :
  ∀ {Fine : Set} {fine : CulturalState → Fine} →
  Consumer.ConsumerSufficient fine standingCode →
  fine visibleRestricted ≡ fine visibleExpanded → ⊥
everyAdequateStandingObserverSeparates =
  Consumer.everySufficientObserverSeparatesRelevantCollision standingCollision

everyAdequateContestabilityObserverSeparates :
  ∀ {Fine : Set} {fine : CulturalState → Fine} →
  Consumer.ConsumerSufficient fine contestabilityCode →
  fine visibleRestricted ≡ fine visibleExpanded → ⊥
everyAdequateContestabilityObserverSeparates =
  Consumer.everySufficientObserverSeparatesRelevantCollision contestabilityCollision

everyAdequateMaterialConeObserverSeparates :
  ∀ {Fine : Set} {fine : CulturalState → Fine} →
  Consumer.ConsumerSufficient fine materialConeCode →
  fine visibleRestricted ≡ fine visibleExpanded → ⊥
everyAdequateMaterialConeObserverSeparates =
  Consumer.everySufficientObserverSeparatesRelevantCollision materialConeCollision

------------------------------------------------------------------------
-- 6. Political contestability is proof-relevant rather than inferred from
--    cultural participation or public visibility.
------------------------------------------------------------------------

data CulturalAlternative : Set where
  repertoireAlternative : CulturalAlternative

data CanContest : CulturalState → CulturalAlternative → Set where
  expandedCanContest : CanContest visibleExpanded repertoireAlternative

data CanSetAgenda : CulturalState → Set where
  expandedCanSetAgenda : CanSetAgenda visibleExpanded

data CanDeliberate : CulturalState → Set where
  expandedCanDeliberate : CanDeliberate visibleExpanded

powersContestability : Political.PoliticalContestability
powersContestability =
  Political.politicalContestability
    CulturalAlternative
    CulturalState
    CanContest
    CanSetAgenda
    CanDeliberate

expandedContestabilityReceipt :
  Political.ContestabilityReceipt powersContestability
expandedContestabilityReceipt =
  Political.contestabilityReceipt
    visibleExpanded
    repertoireAlternative
    expandedCanContest
    expandedCanSetAgenda
    expandedCanDeliberate

------------------------------------------------------------------------
-- 7. Material option cone on the same state carrier.
------------------------------------------------------------------------

data CulturalOption : Set where
  perform : CulturalOption
  exitInstitution : CulturalOption
  setAgenda : CulturalOption

data Available : CulturalState → CulturalOption → Set where
  restrictedPerform : Available visibleRestricted perform
  expandedPerform : Available visibleExpanded perform
  expandedExit : Available visibleExpanded exitInstitution
  expandedAgenda : Available visibleExpanded setAgenda

culturalReachability :
  OptionCone.SafeReachabilitySystem CulturalState CulturalOption
culturalReachability = OptionCone.safeReachabilitySystem Available

restrictedIncludedInExpanded :
  (option : CulturalOption) →
  Available visibleRestricted option →
  Available visibleExpanded option
restrictedIncludedInExpanded perform restrictedPerform = expandedPerform

strictMaterialConeContraction :
  OptionCone.StrictSafeReachabilityContraction
    culturalReachability visibleExpanded visibleRestricted
strictMaterialConeContraction =
  OptionCone.strictSafeReachabilityContraction
    restrictedIncludedInExpanded
    exitInstitution
    expandedExit
    (λ ())

historyConditionedOptionConeDonor :
  OptionCone.StrictSafeReachabilityContraction
    HistoryCone.socialReachability
    HistoryCone.regulatedSupportive
    HistoryCone.mobilisedSupportive
historyConditionedOptionConeDonor = HistoryCone.historyConditionedContraction

------------------------------------------------------------------------
-- 8. Governed performance/use donor.
------------------------------------------------------------------------

sameWordsAndUseStillCannotRecoverStanding :
  INF.FactorsThrough Language.wordsAndUse Language.standingCode → ⊥
sameWordsAndUseStillCannotRecoverStanding =
  Language.sameWordsAndUseCannotRecoverStanding

sameWordsAndUseStillCannotRecoverPermission :
  INF.FactorsThrough Language.wordsAndUse Language.permissionCode → ⊥
sameWordsAndUseStillCannotRecoverPermission =
  Language.sameWordsAndUseCannotRecoverPermission

------------------------------------------------------------------------
-- 9. Exact rooted source-trace payment for the bounded Chapter 5 public-excerpt
--    claim.  Rooted trace pays provenance/coordinates, not historical truth.
------------------------------------------------------------------------

powersChapter5Statement : Trace.PersistentStatementIdentity
powersChapter5Statement =
  Trace.persistent-statement-identity
    "statement:powers:chapter5:public-excerpt"
    "powers-2014-from-plantation-to-paradise"
    "powers-2014-jstor-public-chapter5-surface"
    "chapter-5-pp-93-104-public-excerpt"
    (Claims.claim Claims.breakingBarrierClaimReceipt)

powersChapter5Trace : Trace.SemanticTracePath
powersChapter5Trace =
  Trace.semantic-trace-path
    powersChapter5Statement
    "pnf:powers:chapter5:bounded-historical-claim"
    "review:powers:chapter5:public-excerpt"
    "receipt:powers:chapter5:inspection-evidence-coherent"
    "observation:powers:chapter5:public-excerpt"
    "event:powers:chapter5:historical-claim-registration"
    ("claim:powers:chapter5:saint-martin-directorship" ∷ [])
    ("DASHI.Culture.PowersPlantationParadiseHistoricalClaimReceiptsExact" ∷ [])
    true refl
    false refl
    false refl
    false refl

powersChapter5Root : Contest.PropositionRoot
powersChapter5Root =
  Contest.proposition-root
    "proposition:powers:chapter5:saint-martin-directorship"
    "bounded public-excerpt proposition for Chapter 5"
    true refl
    false refl
    false refl
    false refl

powersChapter5Leaf : Contest.ClaimLeaf powersChapter5Root
powersChapter5Leaf =
  Contest.claim-leaf
    "claim:powers:chapter5:saint-martin-directorship"
    Contest.qualification
    "David M. Powers"
    ("statement:powers:chapter5:public-excerpt" ∷ [])
    ("observation:powers:chapter5:public-excerpt" ∷ [])
    []
    ("scope:public-excerpt-only" ∷ [])
    Contest.qualified
    "review:powers:chapter5:public-excerpt"
    "receipt:powers:chapter5:inspection-evidence-coherent"
    true refl
    false refl
    false refl
    false refl

powersChapter5RootedTraceClaim :
  Rooted.RootedTraceClaim powersChapter5Root powersChapter5Leaf
powersChapter5RootedTraceClaim =
  Rooted.rooted-trace-claim
    powersChapter5Trace
    (Contest.PropositionRoot.propositionRef powersChapter5Root)
    refl
    (Contest.ClaimLeaf.claimRef powersChapter5Leaf)
    refl
    "receipt:powers:chapter5:rooted-trace"
    (Trace.PersistentStatementIdentity.sourceRevisionRef powersChapter5Statement)
    refl
    (Trace.PersistentStatementIdentity.exactSpanRef powersChapter5Statement)
    refl
    true refl
    false refl

powersChapter5ReverseTrace : Trace.ReverseTraceReceipt powersChapter5Trace
powersChapter5ReverseTrace = Trace.canonicalReverseTrace powersChapter5Trace

------------------------------------------------------------------------
-- 10. Reused canonical boundaries.
------------------------------------------------------------------------

requiredObserverAxisJoinBoundary : Join.RequiredObserverAxisJoinBoundary
requiredObserverAxisJoinBoundary = Join.canonicalRequiredObserverAxisJoinBoundary

asymmetricLegibilityBoundary : Legibility.AsymmetricLegibilityBoundary
asymmetricLegibilityBoundary = Legibility.canonicalAsymmetricLegibilityBoundary

governedObservationBoundary : Governed.GovernedObservationProvenanceBoundary
governedObservationBoundary = Governed.canonicalGovernedObservationProvenanceBoundary

recognitionConstitutionBoundary : Recognition.RecognitionConstitutionBoundary
recognitionConstitutionBoundary = Recognition.canonicalRecognitionConstitutionBoundary

politicalContestabilityBoundary : Political.PoliticalAuthorityBoundary
politicalContestabilityBoundary = Political.canonicalPoliticalAuthorityBoundary

historyEcologyOptionConeBoundary : HistoryCone.HistoryEcologyOptionConeBoundary
historyEcologyOptionConeBoundary = HistoryCone.canonicalHistoryEcologyOptionConeBoundary

languageUseStandingBoundary : Language.LanguageUseGovernedStandingBoundary
languageUseStandingBoundary = Language.canonicalLanguageUseGovernedStandingBoundary

situatedFormalisationBoundary : Situated.SituatedFormalisationBoundary
situatedFormalisationBoundary = Situated.canonicalSituatedFormalisationBoundary

record PowersGovernedCrossPollinationBoundary : Set where
  constructor powers-governed-cross-pollination-boundary
  field
    sameCulturalSurfaceDeterminesStanding : Bool
    sameCulturalSurfaceDeterminesStandingIsFalse :
      sameCulturalSurfaceDeterminesStanding ≡ false
    sameCulturalSurfaceDeterminesContestability : Bool
    sameCulturalSurfaceDeterminesContestabilityIsFalse :
      sameCulturalSurfaceDeterminesContestability ≡ false
    sameCulturalSurfaceDeterminesMaterialCone : Bool
    sameCulturalSurfaceDeterminesMaterialConeIsFalse :
      sameCulturalSurfaceDeterminesMaterialCone ≡ false
    oneStrongAxisCompensatesForMissingRequiredAxis : Bool
    oneStrongAxisCompensatesForMissingRequiredAxisIsFalse :
      oneStrongAxisCompensatesForMissingRequiredAxis ≡ false
    publicSurfaceReconstructsInstitutionalClassification : Bool
    publicSurfaceReconstructsInstitutionalClassificationIsFalse :
      publicSurfaceReconstructsInstitutionalClassification ≡ false
    rootedSourceTraceCreatesHistoricalTruth : Bool
    rootedSourceTraceCreatesHistoricalTruthIsFalse :
      rootedSourceTraceCreatesHistoricalTruth ≡ false
    genericCarrierIsViewFromNowhere : Bool
    genericCarrierIsViewFromNowhereIsFalse :
      genericCarrierIsViewFromNowhere ≡ false

canonicalPowersGovernedCrossPollinationBoundary :
  PowersGovernedCrossPollinationBoundary
canonicalPowersGovernedCrossPollinationBoundary =
  powers-governed-cross-pollination-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
