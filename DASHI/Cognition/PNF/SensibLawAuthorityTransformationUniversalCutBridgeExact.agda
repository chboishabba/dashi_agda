module DASHI.Cognition.PNF.SensibLawAuthorityTransformationUniversalCutBridgeExact where

------------------------------------------------------------------------
-- LEGACY CALIBRATION -> EXECUTABLE CANDIDATE -> PROOF-RELEVANT UNIVERSAL CUT
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawAuthorityTransformationMinimalCutExact as Legacy
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawFiniteLegalSearchRegressionExact as Regression
import DASHI.Cognition.PNF.SensibLawFiniteLegalCutProofPromotionExact as CutProof
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawCullenPublicAuthorityDutyCalibrationExact as Cullen

record CutCalibrationTarget : Set where
  constructor cut-calibration-target
  field
    legacy : Legacy.MinimalCutResult
    typedGoal : Algebra.LegalProposition
    legacyTargetReference : String

open CutCalibrationTarget public

record ExecutableCutCandidate
  (depth : Nat)
  (graph : Algebra.LegalGraph)
  (facts : Algebra.FactSet)
  (goal : Algebra.LegalProposition)
  : Set where
  constructor executable-cut-candidate
  field
    candidateRuleIds : List String
    candidateIsMinimalAtBound :
      Search.isMinimalCutCandidate depth graph facts goal candidateRuleIds ≡ true

open ExecutableCutCandidate public

record ExecutableReachabilityCandidate
  (depth : Nat)
  (graph : Algebra.LegalGraph)
  (facts : Algebra.FactSet)
  (goal : Algebra.LegalProposition)
  : Set where
  constructor executable-reachability-candidate
  field
    executableReachable : Search.reachable depth graph facts goal ≡ true

open ExecutableReachabilityCandidate public

record ComputedCutPromotion
  (graph : Algebra.LegalGraph)
  (facts : Algebra.FactSet)
  (target : CutCalibrationTarget)
  : Set where
  constructor computed-cut-promotion
  field
    computedCut : Algebra.MinimalCut graph facts (typedGoal target)
    legacyCalibrationStillOnlyExpectation : Set
    sourceAndTransformationClassificationRechecked : Set

open ComputedCutPromotion public

record ComputedTransformationPromotion
  (graph : Algebra.LegalGraph)
  (facts : Algebra.FactSet)
  (target : CutCalibrationTarget)
  : Set where
  constructor computed-transformation-promotion
  field
    cutPromotion : ComputedCutPromotion graph facts target
    typedTransformation : Algebra.LegalTransformation
    transformedGoalDerivation : Set
    transformationLegallyAvailableUnderSourceGraph : Set

open ComputedTransformationPromotion public

data CutComputationStatus : Set where
  legacyCalibrationOnly
  typedGoalMaterialised
  finiteExecutableCandidateComputed
  proofRelevantCutComputed
  transformationCandidateReopensGoal
  transformationLegallyPromoted
  : CutComputationStatus

-- Mabo has crossed both executable and proof-relevant cut stages on the finite
-- calibration graph. Pabai remains at current-route executable-negative plus
-- counterfactual transformation-candidate status.
maboCutStatus : CutComputationStatus
maboCutStatus = proofRelevantCutComputed

cullenCutStatus : CutComputationStatus
cullenCutStatus = proofRelevantCutComputed

pabaiCutStatus : CutComputationStatus
pabaiCutStatus = finiteExecutableCandidateComputed

pabaiTransformationStatus : CutComputationStatus
pabaiTransformationStatus = transformationCandidateReopensGoal

maboExecutableReachability :
  ExecutableReachabilityCandidate
    2 Regression.maboGraph Regression.maboFacts Regression.maboSurvival
maboExecutableReachability = executable-reachability-candidate
  Regression.maboComputedReachable

maboExecutableCut :
  ExecutableCutCandidate
    2 Regression.maboGraph Regression.maboFacts Regression.maboSurvival
maboExecutableCut = executable-cut-candidate
  (Search.ruleKey Regression.maboSurvivalRule ∷ [])
  refl

maboProofRelevantCut :
  Algebra.MinimalCut Regression.maboGraph Regression.maboFacts Regression.maboSurvival
maboProofRelevantCut = CutProof.maboSurvivalMinimalCut

cullenProofRelevantCut :
  Algebra.MinimalCut Regression.cullenGraph Regression.cullenFacts
    Cullen.cullenDutyProposition
cullenProofRelevantCut = CutProof.cullenDutyMinimalCut

pabaiCurrentReachability :
  Search.reachable 1 Regression.pabaiGraph Regression.pabaiFacts
    Negligence.dutyProposition ≡ false
pabaiCurrentReachability = Regression.pabaiComputedCurrentlyUnreachable

data LegacyMinimalCutResultIsComputedCut : Set where
data ReachableBooleanIsDerivationTree : Set where
data ExecutableCandidateIsProofRelevantCut : Set where
data TransformationClassLabelProvesLegalAvailability : Set where
data CounterfactualSearchCandidateIsCurrentLaw : Set where

legacyCalibrationIsNotComputedCut : LegacyMinimalCutResultIsComputedCut → ⊥
legacyCalibrationIsNotComputedCut ()

booleanDoesNotBecomeDerivation : ReachableBooleanIsDerivationTree → ⊥
booleanDoesNotBecomeDerivation ()

executableCandidateDoesNotBecomeProofCut :
  ExecutableCandidateIsProofRelevantCut → ⊥
executableCandidateDoesNotBecomeProofCut ()

classLabelDoesNotProveAvailableTransformation :
  TransformationClassLabelProvesLegalAvailability → ⊥
classLabelDoesNotProveAvailableTransformation ()

counterfactualCandidateDoesNotBecomeCurrentLaw :
  CounterfactualSearchCandidateIsCurrentLaw → ⊥
counterfactualCandidateDoesNotBecomeCurrentLaw ()
