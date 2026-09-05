module DASHI.Cognition.PNF.SensibLawMaboRecognitionFactorisedReversePlannerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboRecognitionCoordinateFactorisationExact as Factor

------------------------------------------------------------------------
-- FACTORISED REVERSE SEARCH
--
-- Each legal query now routes to the minimum presently relevant source probes.
-- This is a search-policy compiler only: retrieval does not itself resolve the
-- legal coordinate or promote a proposition to a holding/world truth.
------------------------------------------------------------------------

data RecognitionProbe : Set where
  inspectBrennanContinuityPassages
  inspectBrennanRadicalTitlePassages
  inspectDawsonRecognitionPassages
  inspectDawsonAcquiescencePassages
  inspectCalderHallPassages
  inspectCalderJudsonPassages
  inspectAmoduRadicalTitlePassages
  inspectAmoduRecognitionPassages
  inspectAllFactorisedCoordinates
  : RecognitionProbe

data RecognitionWorkKind : Set where
  thinkWork
  lookWork
  testWork
  : RecognitionWorkKind

record RecognitionSearchPlan : Set where
  constructor recognitionSearchPlan
  field
    query : Factor.RecognitionQuery
    requiredCoordinates : List Factor.RecognitionCoordinate
    probes : List RecognitionProbe
    workKind : RecognitionWorkKind
    wholeJudgmentRescanRequired : Bool
    wholeJudgmentRescanRequiredIsFalse : wholeJudgmentRescanRequired ≡ false
    planReference : String
open RecognitionSearchPlan public

planRecognitionSearch : Factor.RecognitionQuery → RecognitionSearchPlan
planRecognitionSearch Factor.identifyContinuityRule = recognitionSearchPlan
  Factor.identifyContinuityRule
  (Factor.antecedentRightExistence ∷ Factor.continuityAcrossSovereignty ∷ [])
  (inspectBrennanContinuityPassages ∷ inspectCalderHallPassages ∷ [])
  lookWork false refl
  "continuity query -> Brennan continuity + Calder Hall probes"
planRecognitionSearch Factor.identifyCrownRecognitionRule = recognitionSearchPlan
  Factor.identifyCrownRecognitionRule
  (Factor.crownRecognitionRequirement ∷ Factor.authorityInterpretation ∷ [])
  (inspectDawsonRecognitionPassages ∷ inspectCalderJudsonPassages ∷ inspectAmoduRecognitionPassages ∷ [])
  lookWork false refl
  "Crown-recognition query -> Dawson recognition + Calder/Amodu interpretation probes"
planRecognitionSearch Factor.identifyRecognitionByConductRule = recognitionSearchPlan
  Factor.identifyRecognitionByConductRule
  (Factor.crownRecognitionRequirement ∷ Factor.recognitionByCrownConduct ∷ Factor.evidentialInferenceOfRecognition ∷ [])
  (inspectDawsonAcquiescencePassages ∷ inspectCalderJudsonPassages ∷ [])
  testWork false refl
  "recognition-by-conduct query -> Dawson acquiescence + Calder interpretation discriminator"
planRecognitionSearch Factor.identifyEnforceabilityStructure = recognitionSearchPlan
  Factor.identifyEnforceabilityStructure
  (Factor.radicalTitleCompatibility ∷ Factor.enforceabilityAgainstCrown ∷ [])
  (inspectBrennanRadicalTitlePassages ∷ inspectAmoduRadicalTitlePassages ∷ [])
  lookWork false refl
  "enforceability query -> Brennan radical-title + Amodu Tijani radical-title probes"
planRecognitionSearch Factor.identifyExactUnifiedTheory = recognitionSearchPlan
  Factor.identifyExactUnifiedTheory
  (Factor.requiredCoordinates Factor.identifyExactUnifiedTheory)
  (inspectAllFactorisedCoordinates ∷ [])
  thinkWork false refl
  "exact unified theory remains a downstream synthesis goal over all factorised coordinates; no whole-judgment rescan is implied"

continuityPlan : RecognitionSearchPlan
continuityPlan = planRecognitionSearch Factor.identifyContinuityRule

recognitionConductPlan : RecognitionSearchPlan
recognitionConductPlan = planRecognitionSearch Factor.identifyRecognitionByConductRule

enforceabilityPlan : RecognitionSearchPlan
enforceabilityPlan = planRecognitionSearch Factor.identifyEnforceabilityStructure

continuityRoutesToBrennanCalder : probes continuityPlan ≡ (inspectBrennanContinuityPassages ∷ inspectCalderHallPassages ∷ [])
continuityRoutesToBrennanCalder = refl

recognitionConductRoutesToDawsonCalder : probes recognitionConductPlan ≡ (inspectDawsonAcquiescencePassages ∷ inspectCalderJudsonPassages ∷ [])
recognitionConductRoutesToDawsonCalder = refl

enforceabilityRoutesToBrennanAmodu : probes enforceabilityPlan ≡ (inspectBrennanRadicalTitlePassages ∷ inspectAmoduRadicalTitlePassages ∷ [])
enforceabilityRoutesToBrennanAmodu = refl

------------------------------------------------------------------------
-- No-collapse / least-search boundaries.
------------------------------------------------------------------------

data ContinuityQueryRequiresRecognitionConductProbe : Set where
data RecognitionConductQueryRequiresBrennanRadicalTitleProbe : Set where
data SearchPlanClosesLegalCoordinate : Set where
data FactorisedQueryRequiresWholeJudgmentRescan : Set where

continuityDoesNotRequireRecognitionConductProbe : ContinuityQueryRequiresRecognitionConductProbe → ⊥
continuityDoesNotRequireRecognitionConductProbe ()

recognitionConductDoesNotRequireBrennanRadicalTitleProbe : RecognitionConductQueryRequiresBrennanRadicalTitleProbe → ⊥
recognitionConductDoesNotRequireBrennanRadicalTitleProbe ()

searchPlanDoesNotCloseCoordinate : SearchPlanClosesLegalCoordinate → ⊥
searchPlanDoesNotCloseCoordinate ()

factorisedQueryDoesNotRequireWholeRescan : FactorisedQueryRequiresWholeJudgmentRescan → ⊥
factorisedQueryDoesNotRequireWholeRescan ()

record RecognitionSearchBoundary : Set where
  constructor recognitionSearchBoundary
  field
    querySpecificSourceRouting : Bool
    querySpecificSourceRoutingIsTrue : querySpecificSourceRouting ≡ true
    retrievalEqualsResolution : Bool
    retrievalEqualsResolutionIsFalse : retrievalEqualsResolution ≡ false
    wholeJudgmentRescanRequired : Bool
    wholeJudgmentRescanRequiredIsFalse : wholeJudgmentRescanRequired ≡ false

canonicalRecognitionSearchBoundary : RecognitionSearchBoundary
canonicalRecognitionSearchBoundary = recognitionSearchBoundary true refl false refl false refl
