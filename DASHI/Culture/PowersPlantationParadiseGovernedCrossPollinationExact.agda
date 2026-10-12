module DASHI.Culture.PowersPlantationParadiseGovernedCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ConsumerIndexedResidualRefinementExact as Consumer
import DASHI.Core.GovernedObservationProvenanceExact as Governed
import DASHI.Core.RecognitionConstitutionNonfactorabilityExact as Recognition
import DASHI.Core.PoliticalContestabilityExact as Political
import DASHI.Core.SituatedFormalisationBoundaryExact as Situated
import DASHI.Governance.OptionConeCoercionExact as OptionCone
import DASHI.Governance.HistoryConditionedSocialEcologyOptionConeExact as HistoryCone
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
-- history-conditioned option cones, governed language/use standing, situated
-- formalisation and exact rooted source traces.
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

sameCulturalSurfaceCannotRecoverStanding :
  INF.FactorsThrough culturalSurface standingCode → ⊥
sameCulturalSurfaceCannotRecoverStanding =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      visibleRestricted visibleExpanded refl standingDiffers)

sameCulturalSurfaceCannotRecoverContestability :
  INF.FactorsThrough culturalSurface contestabilityCode → ⊥
sameCulturalSurfaceCannotRecoverContestability =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      visibleRestricted visibleExpanded refl contestabilityDiffers)

sameCulturalSurfaceCannotRecoverMaterialCone :
  INF.FactorsThrough culturalSurface materialConeCode → ⊥
sameCulturalSurfaceCannotRecoverMaterialCone =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      visibleRestricted visibleExpanded refl materialConeDiffers)

------------------------------------------------------------------------
-- 2. Recognition != constitution/authority on the same carrier.
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
-- 3. Governed-observer consequence: preserving the cultural surface is not
--    sufficient for a bundle that includes standing/authority.
------------------------------------------------------------------------

standingCollision :
  Consumer.ConsumerRelevantCollision culturalSurface standingCode
standingCollision =
  Consumer.consumer-relevant-collision
    visibleRestricted visibleExpanded refl standingDiffers

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

------------------------------------------------------------------------
-- 4. Political contestability is proof-relevant rather than inferred from
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
-- 5. Material option cone on the same state carrier.  Same public/cultural
--    surface does not imply the same reachable action set.
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

-- Direct reuse of the merged history-conditioned donor: changing retained
-- history at fixed ecology can change realised accessibility without deleting
-- the underlying world possibility.
historyConditionedOptionConeDonor :
  OptionCone.StrictSafeReachabilityContraction
    HistoryCone.socialReachability
    HistoryCone.regulatedSupportive
    HistoryCone.mobilisedSupportive
historyConditionedOptionConeDonor = HistoryCone.historyConditionedContraction

------------------------------------------------------------------------
-- 6. Governed performance/use donor.  Same words and same use already fail to
--    recover standing in the merged culture machinery.
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
-- 7. Exact rooted source-trace payment for the bounded Chapter 5 public-excerpt
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
-- 8. Reused canonical boundaries.
------------------------------------------------------------------------

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
