module DASHI.Law.SensibLawWoogarooOffsetSATAdversarial20261106Exact where

-- EPBC 2019/8575 source-typed SAT and finite identifiability analysis.
-- Original source authors: One Environment (Avonvale A15), Saunders Havill
-- (Mount Walker West A16); Jan 2026 PD v5, surveys conducted 2025.
-- Commonwealth decision signed by Mark Hall on 16 October 2026.
-- Original QUT/QCC submissions and all previous PR attributions retained.
-- Source reports do not certify independent measurement, statutory error,
-- agency acceptance, compliance breach, court outcome or financial transfer.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Law.SensibLawWoogarooAdversarialLogicalTests20261028Exact as Adversarial
import DASHI.Law.SensibLawWoogarooEPBC8575PleadableGroundsPrecedentCut20261028Exact as Grounds
import DASHI.Law.SensibLawWoogarooOffsetLandscapeCounterfactualExact as Landscape
import DASHI.Law.SensibLawWoogarooOffsetAttributionLineageExact as Lineage
import DASHI.Law.SensibLawExpertEvidenceProductionIntegrityExact as Expert

-- Tree counts in each of five 30-tree SATs, not koala counts, and NOT an
-- iid sample of the habitat. A zero scat result is not a species absence.
sumScatBearingTrees : List Nat → Nat
sumScatBearingTrees [] = zero
sumScatBearingTrees (n ∷ ns) = n + sumScatBearingTrees ns

numberOfSATs : List Nat → Nat
numberOfSATs [] = zero
numberOfSATs (_ ∷ ns) = suc (numberOfSATs ns)

numberOfPositiveSATs : List Nat → Nat
numberOfPositiveSATs [] = zero
numberOfPositiveSATs (zero ∷ ns) = numberOfPositiveSATs ns
numberOfPositiveSATs (suc _ ∷ ns) = suc (numberOfPositiveSATs ns)

-- A16 Table 44, labels T1,T2,T3,T7,T8.
mountWalkerWestSAT : List Nat
mountWalkerWestSAT = 0 ∷ 2 ∷ 0 ∷ 1 ∷ 0 ∷ []

-- A15 Table 33, labels T1,T6,T7,T8,T10.
avonvaleSAT : List Nat
avonvaleSAT = 11 ∷ 5 ∷ 0 ∷ 0 ∷ 1 ∷ []

mountWalkerFiveSATs : numberOfSATs mountWalkerWestSAT ≡ 5
mountWalkerFiveSATs = refl
mountWalkerThreePositiveTrees : sumScatBearingTrees mountWalkerWestSAT ≡ 3
mountWalkerThreePositiveTrees = refl
mountWalkerTwoPositiveSATs : numberOfPositiveSATs mountWalkerWestSAT ≡ 2
mountWalkerTwoPositiveSATs = refl

avonvaleFiveSATs : numberOfSATs avonvaleSAT ≡ 5
avonvaleFiveSATs = refl
avonvaleSeventeenPositiveTrees : sumScatBearingTrees avonvaleSAT ≡ 17
avonvaleSeventeenPositiveTrees = refl
avonvaleThreePositiveSATs : numberOfPositiveSATs avonvaleSAT ≡ 3
avonvaleThreePositiveSATs = refl

-- Proponent-reported observation, independent verification, agency
-- acceptance, and adjudication are different provenance stages.
data Stage : Set where
  proponentReported independentSiteVerified agencyAccepted adjudicated : Stage

record SurveyReceipt : Set where
  constructor survey-receipt
  field
    projectID propertyName sourceDocument sourceTable originalAuthor : String
    stage : Stage
    scatBearingTreesBySAT : List Nat
open SurveyReceipt public

mountWalkerReceipt : SurveyReceipt
mountWalkerReceipt = survey-receipt
  "EPBC 2019/8575" "Mount Walker West"
  "PD v5 Attachment A16 (2025 survey; January 2026 PD)"
  "A16 Table 44, page 101" "Saunders Havill"
  proponentReported mountWalkerWestSAT

avonvaleReceipt : SurveyReceipt
avonvaleReceipt = survey-receipt
  "EPBC 2019/8575" "Avonvale"
  "PD v5 Attachment A15 (2025 survey; January 2026 PD)"
  "A15 Table 33, page 72" "One Environment"
  proponentReported avonvaleSAT

-- A16 Table 45 assigns the site-level presence subscore 10/10 to all
-- four assessment units. The scoring rubric and AU location join are
-- separate evidence obligations, not silently inferred from scat data.
data AU : Set where
  au1 au2 au3 au4 : AU

reportedPresenceScore : AU → Nat
reportedPresenceScore _ = 10

allFourPresenceComponentsTotal :
  reportedPresenceScore au1 + reportedPresenceScore au2 +
  reportedPresenceScore au3 + reportedPresenceScore au4 ≡ 40
allFourPresenceComponentsTotal = refl
-- 40 is an unweighted sum of subcomponents, NOT OAG percentage.

data ProtectedMatter : Set where
  koala greyHeadedFlyingFox swiftParrot regentHoneyeater : ProtectedMatter

reportedMountWalkerContributionBasisPoints : ProtectedMatter → Nat
reportedMountWalkerContributionBasisPoints koala = 5002
reportedMountWalkerContributionBasisPoints greyHeadedFlyingFox = 6689
reportedMountWalkerContributionBasisPoints swiftParrot = 9192
reportedMountWalkerContributionBasisPoints regentHoneyeater = 3740
-- Percent times 100. Copied source claims, NOT recalculated percentages.

record PublicProjection : Set where
  constructor public-projection
  field
    sats : List Nat
    presenceAU1 presenceAU2 presenceAU3 presenceAU4 : Nat
open PublicProjection public

publishedMountWalker : PublicProjection
publishedMountWalker = public-projection mountWalkerWestSAT 10 10 10 10

record HypotheticalAUWorld : Set where
  constructor hypothetical-world
  field
    publicData : PublicProjection
    au1ActuallyUsed au2ActuallyUsed au3ActuallyUsed au4ActuallyUsed : Bool
open HypotheticalAUWorld public

-- Both worlds admit some AU use, consistent with positive site-level
-- evidence, but have different AU1 use. No mapping from the original
-- SAT locations to assessment units is assumed here.
worldWithNoAU1Use : HypotheticalAUWorld
worldWithNoAU1Use = hypothetical-world publishedMountWalker false true false false

worldWithAU1Use : HypotheticalAUWorld
worldWithAU1Use = hypothetical-world publishedMountWalker true false false false

identicalExposedEvidence :
  publicData worldWithNoAU1Use ≡ publicData worldWithAU1Use
identicalExposedEvidence = refl

falseCannotEqualTrue : false ≡ true → ⊥
falseCannotEqualTrue ()

-- Finite identifiability counterexample. Hypothetical AU worlds are not
-- factual states. A source-paid AU join is needed to distinguish them.
noUniversalAU1UseDecoder :
  (decoder : PublicProjection → Bool) →
  ((w : HypotheticalAUWorld) →
    decoder (publicData w) ≡ au1ActuallyUsed w) → ⊥
noUniversalAU1UseDecoder decoder exact =
  falseCannotEqualTrue
    (trans (sym (exact worldWithNoAU1Use)) (exact worldWithAU1Use))

-- Reuse the existing seven-ground applicant/respondent adversary.
habitatGroundCountermodel :
  Adversarial.ShortcutCountermodel Grounds.actionBaselineError
habitatGroundCountermodel = Adversarial.habitatShortcutCountermodel

data RemainingGate : Set where
  originalAUSurveyCoordinates : RemainingGate
  sourceInternalTransectIDReconciliation : RemainingGate
  originalPresenceScoreRubricAndScope : RemainingGate
  speciesSpecificImpactOffsetSameFunction : RemainingGate
  independentSurveyDesignAndDetectionModel : RemainingGate
  final20261015OffsetPlanVersionIdentity : RemainingGate
  actualOffsetDeclarationsAndPolygons : RemainingGate
  siteSpecificEcologicalMonitoring : RemainingGate
  agency95CDecisionReasoning : RemainingGate
  original95BCommentPacket : RemainingGate
  recomputedOffsetAssessmentGuideOutput : RemainingGate
  counselAndCourtMerits : RemainingGate

record CompleteOffsetDischarge : Set where
  constructor complete-offset-discharge
  field
    originalReceipts : (g : RemainingGate) → Bool
    everyGatePaid : (g : RemainingGate) → originalReceipts g ≡ true
    independentlyValidated : Bool
    independentlyValidatedIsTrue : independentlyValidated ≡ true

-- No CompleteOffsetDischarge witness is constructed. Neither document
-- retrieval nor the finite countermodel creates a Court or agency receipt.
