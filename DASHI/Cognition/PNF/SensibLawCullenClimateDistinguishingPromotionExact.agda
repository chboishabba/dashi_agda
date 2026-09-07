module DASHI.Cognition.PNF.SensibLawCullenClimateDistinguishingPromotionExact where

------------------------------------------------------------------------
-- CULLEN -> CLIMATE COMPARATOR: EXECUTABLE MISMATCH -> POLICY-INDEXED
-- PROOF-RELEVANT DISTINGUISHING SET
--
-- The executable search identifies `positiveOperationalAct` as the first exact
-- feature absent from the climate comparator. That does NOT itself prove a legal
-- distinction. Promotion therefore fixes an explicit correspondence policy.
--
-- Under this fixture policy, the Cullen foreseeable-injury feature may correspond
-- to the climate foreseeability feature, but there is no admitted correspondence
-- for Cullen's positive operational act or statutory police-function feature.
-- This is a DASHI comparator policy, not a High Court holding about climate duty.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawPrecedentApplicabilityDistinguishingExact as Precedent
import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawFiniteLegalSearchRegressionExact as Regression
import DASHI.Cognition.PNF.SensibLawCullenPublicAuthorityDutyCalibrationExact as Cullen

------------------------------------------------------------------------
-- Explicit material-correspondence policy.
------------------------------------------------------------------------

data CullenClimateCorrespondence :
  Algebra.LegalProposition → Algebra.LegalProposition → Set where
  foreseeableCorrespondence :
    CullenClimateCorrespondence
      Cullen.foreseeablePhysicalInjuryRisk
      Regression.pabaiForeseeability

cullenClimatePolicy :
  Precedent.MaterialCorrespondencePolicy
    Cullen.cullenDutyHolding Regression.climateComparatorCase
cullenClimatePolicy = Precedent.material-correspondence-policy
  CullenClimateCorrespondence
  "fixture policy: source-calibrated Cullen material features compared against the climate candidate; no unsupported analogy is manufactured"
  Cullen.cullenSource
  true

------------------------------------------------------------------------
-- The executable mismatch remains the same candidate.
------------------------------------------------------------------------

executableFirstMissingFeature :
  Search.minimalDistinguishingCandidate
    Cullen.cullenDutyHolding Regression.climateComparatorCase
  ≡ Search.found Cullen.positiveOperationalAct
executableFirstMissingFeature = Regression.cullenClimateFirstMissingFeature

------------------------------------------------------------------------
-- Proof-relevant policy-specific difference.
------------------------------------------------------------------------

positiveOperationalDifference :
  Precedent.MaterialDifference
    Cullen.cullenDutyHolding Regression.climateComparatorCase
positiveOperationalDifference = Precedent.material-difference
  Cullen.positiveOperationalAct
  Regression.pabaiForeseeability
  Algebra.here
  "Cullen's positive operational crowd-control act has no admitted correspondence in the encoded climate comparator policy"
  Cullen.cullenSource

cullenClimateDistinguishingSet :
  Precedent.DistinguishingSet
    Cullen.cullenDutyHolding Regression.climateComparatorCase
cullenClimateDistinguishingSet = Precedent.distinguishing-set
  (positiveOperationalDifference ∷ [])
  ⊤
  ⊤

------------------------------------------------------------------------
-- Any policy-applicability witness must map Cullen's first material feature.
-- The only constructor of the fixed correspondence relation maps the *second*
-- Cullen feature (foreseeability), so the required positive-act mapping is
-- impossible.
------------------------------------------------------------------------

cullenClimatePolicyApplicationImpossible :
  Precedent.PolicyPrecedentApplicable cullenClimatePolicy → ⊥
cullenClimatePolicyApplicationImpossible application with
  Precedent.everyMaterialFeatureMappedUnderPolicy
    (Precedent.policyFeatureMap application)
    Algebra.here
... | current , (currentMembership , correspondence) with correspondence
... | ()

cullenClimateMinimalDistinguishingSet :
  Precedent.PolicyMinimalDistinguishingSet cullenClimatePolicy
cullenClimateMinimalDistinguishingSet =
  Precedent.policy-minimal-distinguishing-set
    cullenClimateDistinguishingSet
    cullenClimatePolicyApplicationImpossible
    (λ _ → ⊤)

record PolicyDistinguishingPromotion : Set where
  constructor policy-distinguishing-promotion
  field
    executableMismatch :
      Search.precedentFeatureFitCandidate
        Cullen.cullenDutyHolding Regression.climateComparatorCase ≡ false
    executableCandidate :
      Search.minimalDistinguishingCandidate
        Cullen.cullenDutyHolding Regression.climateComparatorCase
      ≡ Search.found Cullen.positiveOperationalAct
    proofRelevantPolicyDistinction :
      Precedent.PolicyMinimalDistinguishingSet cullenClimatePolicy

open PolicyDistinguishingPromotion public

cullenClimatePromotion : PolicyDistinguishingPromotion
cullenClimatePromotion = policy-distinguishing-promotion
  Regression.cullenClimateFeatureFitFails
  Regression.cullenClimateFirstMissingFeature
  cullenClimateMinimalDistinguishingSet

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CullenPolicyDistinctionProvesClimateNoDuty : Set where
data FixtureCorrespondencePolicyIsBindingHighCourtLaw : Set where

data MissingPositiveActMeansNoNovelPublicAuthorityDutyEver : Set where

policyDistinctionDoesNotDecideClimateDuty :
  CullenPolicyDistinctionProvesClimateNoDuty → ⊥
policyDistinctionDoesNotDecideClimateDuty ()

fixturePolicyDoesNotBecomeBindingLaw :
  FixtureCorrespondencePolicyIsBindingHighCourtLaw → ⊥
fixturePolicyDoesNotBecomeBindingLaw ()

positiveActDifferenceIsNotUniversalNoDutyRule :
  MissingPositiveActMeansNoNovelPublicAuthorityDutyEver → ⊥
positiveActDifferenceIsNotUniversalNoDutyRule ()
