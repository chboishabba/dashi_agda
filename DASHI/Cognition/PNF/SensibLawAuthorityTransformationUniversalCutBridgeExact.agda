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
import DASHI.Cognition.PNF.SensibLawPabaiTransformationPromotionExact as PabaiTransform
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

------------------------------------------------------------------------
-- Legal availability is intentionally a separate parameter/witness. A typed
-- transformation plus a transformed proof does not prove that controlling law
-- authorises the transformation.
------------------------------------------------------------------------

record LegallyAvailableTransformation
  (transformation : Algebra.LegalTransformation)
  (AvailableUnderControllingAuthorities : Set) : Set where
  constructor legally-available-transformation
  field
    availabilityWitness : AvailableUnderControllingAuthorities

open LegallyAvailableTransformation public

data CutComputationStatus : Set where
  legacyCalibrationOnly
  typedGoalMaterialised
  finiteExecutableCandidateComputed
  proofRelevantCutComputed
  transformationCandidateReopensGoal
  typedTransformationReopensGoal
  transformationLegallyPromoted
  : CutComputationStatus

maboCutStatus : CutComputationStatus
maboCutStatus = proofRelevantCutComputed

cullenCutStatus : CutComputationStatus
cullenCutStatus = proofRelevantCutComputed

pabaiCutStatus : CutComputationStatus
pabaiCutStatus = finiteExecutableCandidateComputed

pabaiTransformationStatus : CutComputationStatus
pabaiTransformationStatus = typedTransformationReopensGoal

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

pabaiTypedTransformation : Algebra.LegalTransformation
pabaiTypedTransformation = PabaiTransform.pabaiTypedTransformation

pabaiTypedTransformationPromotion :
  Search.TransformationPromotion
    1 Negligence.dutyProposition Regression.pabaiReformulationCandidate
pabaiTypedTransformationPromotion = PabaiTransform.pabaiTransformationPromotion

pabaiLegalAvailabilityStillOpen :
  PabaiTransform.PabaiTransformationAvailableUnderControllingAuthorities → ⊥
pabaiLegalAvailabilityStillOpen = PabaiTransform.pabaiLegalAvailabilityStillOpen

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data LegacyMinimalCutResultIsComputedCut : Set where
data ReachableBooleanIsDerivationTree : Set where
data ExecutableCandidateIsProofRelevantCut : Set where
data TransformationClassLabelProvesLegalAvailability : Set where
data CounterfactualSearchCandidateIsCurrentLaw : Set where
data TypedTransformationProvesAvailability : Set where

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

typedTransformationStillDoesNotProveAvailability :
  TypedTransformationProvesAvailability → ⊥
typedTransformationStillDoesNotProveAvailability ()
