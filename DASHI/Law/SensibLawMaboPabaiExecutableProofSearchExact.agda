module DASHI.Law.SensibLawMaboPabaiExecutableProofSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboDawsonRecognitionResidualPlannerExact as DawsonPlan
import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Climate
import DASHI.Cognition.PNF.SensibLawMaboPabaiPositiveNegativeRegressionExact as Regression
import DASHI.Cognition.PNF.SensibLawTypedLegalAuthorityEdgeExact as Edge
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Intent
import DASHI.Law.SensibLawProviderNeutralLegalQueryAlgebraExact as Query
import DASHI.Law.SensibLawCitationAuthorityFollowExact as Follow
import DASHI.Law.SensibLawCitationUsePropositionExact as CitationUse
import DASHI.Law.SensibLawDialecticalProofSearchExact as Dialectic

------------------------------------------------------------------------
-- MABO: recognition-condition residual -> executable search family.
------------------------------------------------------------------------

maboRecognitionBudget : Intent.SearchBudget
maboRecognitionBudget = Intent.searchBudget 12 40 2
  "bounded recognition-condition proof search"

maboRecognitionIntent : Intent.SearchIntent
maboRecognitionIntent = Intent.searchIntent
  "identifyUnifiedRecognitionTheory"
  "Dawson recognition/acceptance juridical condition"
  Intent.authorityDiscoveryProducer
  Intent.exploitKnownResidual
  "AU"
  "Mabo (No 2) decision-time authority envelope"
  Intent.primaryTextRequired
  "recognition-condition hyperfabric"
  "Mabo v Queensland (No 2); Dawson J"
  "juridical condition / authoritative reasons"
  "exclude mere acquiescence evidence as substitute for the juridical condition"
  maboRecognitionBudget
  "Dawson residual -> exact authority-rule search intent"

maboDawsonRuleHypothesis : Query.SearchHypothesis
maboDawsonRuleHypothesis = Query.searchHypothesis
  maboRecognitionIntent
  "H1: Dawson expressly states a recognition/acceptance condition"
  "juridical condition proposition"
  Query.supportingProbe
  (Query.andQ
    (Query.phraseQ "recognition or acceptance")
    (Query.termQ "Dawson"))
  "recognitionConditionResidual"
  "do not accept mere factual evidence of acquiescence as the condition rule"

maboNoPresumptionDefeater : Query.SearchHypothesis
maboNoPresumptionDefeater = Query.searchHypothesis
  maboRecognitionIntent
  "H2: no-general-presumption reasoning limits or qualifies the proposed condition"
  "qualifying juridical proposition"
  Query.defeaterProbe
  (Query.nearQ 20
    (Query.phraseQ "no presumption")
    (Query.phraseQ "recognition"))
  "recognitionConditionResidual"
  "defeater search does not itself negate the condition"

maboHallComparator : Query.SearchHypothesis
maboHallComparator = Query.searchHypothesis
  maboRecognitionIntent
  "H3: Hall supplies recognition-independence comparator"
  "cross-authority comparison proposition"
  Query.comparatorProbe
  (Query.andQ
    (Query.termQ "Hall")
    (Query.phraseQ "recognition"))
  "recognitionConditionResidual"
  "comparator is not automatically controlling Australian authority"

maboAmoduComparator : Query.SearchHypothesis
maboAmoduComparator = Query.searchHypothesis
  maboRecognitionIntent
  "H4: Amodu supplies continuity comparator"
  "cross-authority continuity proposition"
  Query.comparatorProbe
  (Query.andQ
    (Query.termQ "Amodu")
    (Query.phraseQ "native title"))
  "recognitionConditionResidual"
  "source proposition must be verified rather than inferred from citation"

maboRecognitionFamily : Query.SearchHypothesisFamily
maboRecognitionFamily = Query.searchHypothesisFamily
  maboRecognitionIntent
  maboDawsonRuleHypothesis
  []
  (maboNoPresumptionDefeater ∷ [])
  (maboHallComparator ∷ maboAmoduComparator ∷ [])
  "Mabo recognition-condition proof search family"

maboCurrentPlannerStillTargetsRecognitionCondition : Bool
maboCurrentPlannerStillTargetsRecognitionCondition = true

------------------------------------------------------------------------
-- AMODU citation-follow fixture.
------------------------------------------------------------------------

amoduCitationCandidate : Follow.CitationCandidate
amoduCitationCandidate = Follow.citationCandidate
  "Mabo v Queensland (No 2)"
  "Brennan reasons / Amodu citation span"
  "Amodu Tijani v Secretary, Southern Nigeria"
  "amodu-citation-candidate"

amoduCitationIdentity : Follow.CitationIdentity amoduCitationCandidate
amoduCitationIdentity = Follow.citationIdentity
  "Amodu Tijani v Secretary, Southern Nigeria [1921] 2 AC 399"
  "Amodu-Tijani-1921-2-AC-399"
  ⊤
  "exact cited authority identity candidate"

amoduFollowPlan : Follow.CitationFollowPlan
amoduFollowPlan = Follow.citationFollowPlan
  amoduCitationCandidate
  amoduCitationIdentity
  Intent.exactCitedAuthorityProducer
  refl
  "historical Privy Council authority used in Australian common-law reasoning"
  "local corpus -> official/research case source"
  "depth 1 first; expand only if residual persists"
  "Amodu exact citation lookup before proposition-use classification"

------------------------------------------------------------------------
-- PABAI / DONOGHUE: negative calibration -> route-repair search, not desired
-- outcome promotion.
------------------------------------------------------------------------

pabaiDutyBudget : Intent.SearchBudget
pabaiDutyBudget = Intent.searchBudget 18 80 2
  "bounded novel-duty route-repair search"

pabaiDutyIntent : Intent.SearchIntent
pabaiDutyIntent = Intent.searchIntent
  "Pabai climate-duty route repair"
  "whether a narrower common-law duty formulation can avoid the current blocker without assuming legislation is logically necessary"
  Intent.discriminatorProducer
  Intent.compareAuthorities
  "AU"
  "current Australian common-law and statutory envelope"
  Intent.bindingAuthorityPreferred
  "duty-of-care issue fabric"
  "Donoghue v Stevenson; Pabai v Commonwealth (No 2)"
  "novel duty / common-law development / public-authority policy treatment"
  "do not treat Mabo as climate-negligence precedent; search only for reusable proof-topology transformations"
  pabaiDutyBudget
  "Pabai negative calibration -> discriminator search"

pabaiCommonLawDevelopmentHypothesis : Query.SearchHypothesis
pabaiCommonLawDevelopmentHypothesis = Query.searchHypothesis
  pabaiDutyIntent
  "H1: Australian authority states a common-law route for incremental or analogous development of duty"
  "common-law development condition"
  Query.supportingProbe
  Query.donoghueDevelopmentQuery
  "route-repair discriminator"
  "support must survive authority hierarchy and current treatment"

pabaiCorePolicyDefeater : Query.SearchHypothesis
pabaiCorePolicyDefeater = Query.searchHypothesis
  pabaiDutyIntent
  "H2: core-government-policy reasoning operates as a hard or effectively decisive blocker for the candidate formulation"
  "public-authority policy blocker proposition"
  Query.defeaterProbe
  Query.dutyPolicyQuery
  "route-repair discriminator"
  "policy language must be decomposed; do not model policy as an opaque terminal node"

pabaiStatutoryCoherenceComparator : Query.SearchHypothesis
pabaiStatutoryCoherenceComparator = Query.searchHypothesis
  pabaiDutyIntent
  "H3: statutory coherence distinguishes successful and unsuccessful public-authority duties"
  "coherence discriminator"
  Query.comparatorProbe
  (Query.nearQ 25
    (Query.phraseQ "duty of care")
    (Query.phraseQ "statutory coherence"))
  "route-repair discriminator"
  "descriptive comparator does not establish doctrine by frequency"

pabaiDutyFamily : Query.SearchHypothesisFamily
pabaiDutyFamily = Query.searchHypothesisFamily
  pabaiDutyIntent
  pabaiCommonLawDevelopmentHypothesis
  []
  (pabaiCorePolicyDefeater ∷ [])
  (pabaiStatutoryCoherenceComparator ∷ [])
  "Pabai route repair searches support, blocker and discriminator together"

pabaiDialecticalDiscriminator : Dialectic.SearchDiscriminator
pabaiDialecticalDiscriminator = Dialectic.searchDiscriminator
  "candidate narrower climate duty"
  "common-law development authority"
  "core policy / statutory coherence blocker"
  "minimal doctrinal or factual coordinate separating the candidate route from current Pabai closure"
  "seek the missing discriminator rather than assume the desired result"

pabaiSupportDefeaterPair : Dialectic.DialecticalProbePair
pabaiSupportDefeaterPair = Dialectic.dialecticalProbePair
  "candidate narrower climate duty"
  pabaiCommonLawDevelopmentHypothesis
  pabaiCorePolicyDefeater
  Dialectic.policyOrInstitutionalCompetenceDefeater
  ⊤
  "paired support/defeater search for Pabai route repair"

------------------------------------------------------------------------
-- Existing positive/negative regression remains authoritative for the fixture.
------------------------------------------------------------------------

maboPositiveStillReachable :
  Regression.Cut.reachableUnderCurrentAuthorities Regression.Cut.maboPositiveCalibration ≡ true
maboPositiveStillReachable = Regression.maboPositivePathIsReachable

pabaiCurrentRouteStillUnreachable :
  Regression.Cut.reachableUnderCurrentAuthorities Regression.Cut.pabaiNegativeCalibration ≡ false
pabaiCurrentRouteStillUnreachable = Regression.pabaiCandidatePathCurrentlyUnreachable

pabaiSearchStillRequiresProof :
  Regression.Cut.proofStillRequired Regression.Cut.pabaiNegativeCalibration ≡ true
pabaiSearchStillRequiresProof = Regression.pabaiCandidateStillNeedsProof

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MaboIsClimateNegligencePrecedent : Set where
data MaboPositivePathForcesPabaiReopening : Set where
data PabaiNegativePathMeansParliamentOnly : Set where
data AmoduCitationMeansMaboAdoptedEveryAmoduProposition : Set where

maboIsNotPromotedToClimateNegligencePrecedent : MaboIsClimateNegligencePrecedent → ⊥
maboIsNotPromotedToClimateNegligencePrecedent ()

maboPositiveDoesNotForcePabai : MaboPositivePathForcesPabaiReopening → ⊥
maboPositiveDoesNotForcePabai ()

pabaiNegativeDoesNotMeanParliamentOnly : PabaiNegativePathMeansParliamentOnly → ⊥
pabaiNegativeDoesNotMeanParliamentOnly ()

amoduCitationDoesNotMeanWholesaleAdoption :
  AmoduCitationMeansMaboAdoptedEveryAmoduProposition → ⊥
amoduCitationDoesNotMeanWholesaleAdoption ()

record MaboPabaiSearchBoundary : Set where
  constructor maboPabaiSearchBoundary
  field
    maboResidualCompilesToTargetedAuthoritySearch : Bool
    maboResidualCompilesToTargetedAuthoritySearchIsTrue :
      maboResidualCompilesToTargetedAuthoritySearch ≡ true
    pabaiNegativeCalibrationCompilesToRepairSearch : Bool
    pabaiNegativeCalibrationCompilesToRepairSearchIsTrue :
      pabaiNegativeCalibrationCompilesToRepairSearch ≡ true
    maboAnalogyAutomaticallyTransfersDoctrine : Bool
    maboAnalogyAutomaticallyTransfersDoctrineIsFalse :
      maboAnalogyAutomaticallyTransfersDoctrine ≡ false
    supportAndDefeaterQueriesArePaired : Bool
    supportAndDefeaterQueriesArePairedIsTrue : supportAndDefeaterQueriesArePaired ≡ true

canonicalMaboPabaiSearchBoundary : MaboPabaiSearchBoundary
canonicalMaboPabaiSearchBoundary =
  maboPabaiSearchBoundary true refl true refl false refl true refl
