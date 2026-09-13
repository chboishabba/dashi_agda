module DASHI.Culture.AliceMillerChildhoodAuthorityPluralLensExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Core.SnowballPluralLensInvariantExact as Snow
import DASHI.Culture.JohnAnthonyBrownChildReligiousPowerBidiExact as John

------------------------------------------------------------------------
-- ALICE MILLER: CHILDHOOD, AUTHORITY, SILENCING, "POISONOUS PEDAGOGY"
--
-- Source role: interpretive/clinical-author work about childhood mistreatment,
-- humiliation, repression/silencing and intergenerational repetition.
-- This owner does NOT promote Miller's broad causal claims about mental illness,
-- violence or adult outcomes into empirical theorems.
------------------------------------------------------------------------

data MillerAxis : Set where
  childExperience : MillerAxis
  parentalAuthority : MillerAxis
  humiliationViolence : MillerAxis
  emotionalNeglect : MillerAxis
  voiceSilencing : MillerAxis
  dependenceAttachment : MillerAxis
  memoryInterpretation : MillerAxis
  witnessSupport : MillerAxis
  intergenerationalTransmission : MillerAxis
  adultOutcome : MillerAxis
  sourceEvidenceStrength : MillerAxis

millerRelevant : MillerAxis → Bool
millerRelevant axis = true

millerRetained : MillerAxis → Bool
millerRetained axis = true

millerLens : Snow.PluralLens MillerAxis
millerLens = Snow.plural-lens millerRelevant millerRetained (λ axis eq → eq)

record MillerBoundary : Set where
  constructor miller-boundary
  field
    childExperienceDeservesIndependentCoordinate : Bool
    authorityCanShapeWhatCanBeSaid : Bool
    humiliationAndCareCanCoexistInSameInstitution : Bool
    retrospectiveInterpretationEqualsDirectMeasurement : Bool
    childhoodMistreatmentUniquelyCausesAdultPathology : Bool
    enlightenedWitnessGuaranteesRecovery : Bool
    sourceClaimsRequireIndependentEmpiricalAudit : Bool
open MillerBoundary public

canonicalMillerBoundary : MillerBoundary
canonicalMillerBoundary = miller-boundary
  true true true false false false true

record JohnMillerCrossPollination : Set where
  constructor john-miller-cross-pollination
  field
    authorityAsymmetryShared : Bool
    belongingDependenceShared : Bool
    childVoiceMayBeConstrained : Bool
    mechanismOutcomeSeparated : Bool
    empiricalClaimsMerged : Bool
open JohnMillerCrossPollination public

johnMillerCrossPollination : JohnMillerCrossPollination
johnMillerCrossPollination = john-miller-cross-pollination
  true true true true false

johnConditionalityRetained :
  John.JohnAnthonyBrownPaperBidiBoundary.paperPositiveAndNegativeOutcomeHypothesesPreserved
    John.canonicalJohnAnthonyBrownPaperBidiBoundary ≡ true
johnConditionalityRetained = refl

data MillerTheoryCreatesUniversalTraumaEtiology : Set where
data ChildSilenceProvesAbuseHistory : Set where
data AdultSymptomRecoversUniqueChildhoodCause : Set where

millerDoesNotCreateUniversalEtiology : MillerTheoryCreatesUniversalTraumaEtiology → ⊥
millerDoesNotCreateUniversalEtiology ()
childSilenceDoesNotProveAbuseHistory : ChildSilenceProvesAbuseHistory → ⊥
childSilenceDoesNotProveAbuseHistory ()
adultSymptomDoesNotRecoverUniqueCause : AdultSymptomRecoversUniqueChildhoodCause → ⊥
adultSymptomDoesNotRecoverUniqueCause ()
