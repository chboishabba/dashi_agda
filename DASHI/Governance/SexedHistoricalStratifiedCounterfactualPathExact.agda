module DASHI.Governance.SexedHistoricalStratifiedCounterfactualPathExact where

------------------------------------------------------------------------
-- STRATIFIED COUNTERFACTUAL PATH / HISTORY-CONDITIONED CHOICE
--
-- The same present endpoint and the same current model fidelity need not erase
-- the order by which support repairs/counterformations were admitted.  This
-- owner makes admitted intervention paths first-class, gives them associative
-- concatenation, and instantiates the canonical history-conditioned-choice
-- theorem on two observationally collapsed path histories.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.HistoryConditionedChoiceExact as HistoryChoice
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Strata
import DASHI.Governance.SexedHistoricalStratifiedFidelityEscalationExact as Fidelity

------------------------------------------------------------------------
-- 1. Admitted historical moves and paths.
------------------------------------------------------------------------

data HistoricalMove : Set where
  localRepairMove
  networkCounterformationMove
  institutionalAccommodationMove
  : HistoricalMove

data AdmittedMove : HistoricalMove → Set where
  localRepairAdmitted : AdmittedMove localRepairMove
  networkCounterformationAdmitted : AdmittedMove networkCounterformationMove
  institutionalAccommodationAdmitted : AdmittedMove institutionalAccommodationMove

data AdmittedPath : Set where
  emptyPath : AdmittedPath
  stepPath : (m : HistoricalMove) → AdmittedMove m → AdmittedPath → AdmittedPath

_++p_ : AdmittedPath → AdmittedPath → AdmittedPath
emptyPath ++p q = q
stepPath m receipt tail ++p q = stepPath m receipt (tail ++p q)

pathAppendAssociative :
  (p q r : AdmittedPath) →
  (p ++p q) ++p r ≡ p ++p (q ++p r)
pathAppendAssociative emptyPath q r = refl
pathAppendAssociative (stepPath m receipt tail) q r =
  cong (stepPath m receipt) (pathAppendAssociative tail q r)

repairThenCounterformation : AdmittedPath
repairThenCounterformation =
  stepPath localRepairMove localRepairAdmitted
    (stepPath networkCounterformationMove networkCounterformationAdmitted
      emptyPath)

counterformationThenRepair : AdmittedPath
counterformationThenRepair =
  stepPath networkCounterformationMove networkCounterformationAdmitted
    (stepPath localRepairMove localRepairAdmitted
      emptyPath)

------------------------------------------------------------------------
-- 2. Coarse endpoint / stratum / fidelity observations collapse the paths.
------------------------------------------------------------------------

data PresentEndpoint : Set where
  onePersistentInstitutionalResidual : PresentEndpoint

pathEndpoint : AdmittedPath → PresentEndpoint
pathEndpoint _ = onePersistentInstitutionalResidual

pathStratum : AdmittedPath → Strata.VoxelStratum
pathStratum _ = Strata.centreStratum

pathFidelity : AdmittedPath → Fidelity.HistoricalModelFidelity
pathFidelity _ = Fidelity.edgeFidelity

record CoarsePathObservation : Set where
  constructor coarse-path-observation
  field
    endpoint : PresentEndpoint
    stratum : Strata.VoxelStratum
    fidelity : Fidelity.HistoricalModelFidelity

observePath : AdmittedPath → CoarsePathObservation
observePath p = coarse-path-observation (pathEndpoint p) (pathStratum p) (pathFidelity p)

canonicalPathsShareCoarseObservation :
  observePath repairThenCounterformation
  ≡ observePath counterformationThenRepair
canonicalPathsShareCoarseObservation = refl

------------------------------------------------------------------------
-- 3. Fine path pattern and next choice remain history-sensitive.
------------------------------------------------------------------------

data PathPattern : Set where
  repairPrecedesCounterformation
  counterformationPrecedesRepair
  otherPattern
  : PathPattern

patternOfPath : AdmittedPath → PathPattern
patternOfPath
  (stepPath localRepairMove _
    (stepPath networkCounterformationMove _ emptyPath)) =
    repairPrecedesCounterformation
patternOfPath
  (stepPath networkCounterformationMove _
    (stepPath localRepairMove _ emptyPath)) =
    counterformationPrecedesRepair
patternOfPath _ = otherPattern

data NextHistoricalChoice : Set where
  reopenInstitutionalCompatibilityFirst
  reopenDistributedCounterformationFirst
  continueGenericSearch
  : NextHistoricalChoice

chooseNext : AdmittedPath → NextHistoricalChoice
chooseNext
  (stepPath localRepairMove _
    (stepPath networkCounterformationMove _ emptyPath)) =
      reopenInstitutionalCompatibilityFirst
chooseNext
  (stepPath networkCounterformationMove _
    (stepPath localRepairMove _ emptyPath)) =
      reopenDistributedCounterformationFirst
chooseNext _ = continueGenericSearch

canonicalChoicesDiffer :
  chooseNext repairThenCounterformation
  ≡ chooseNext counterformationThenRepair → ⊥
canonicalChoicesDiffer ()

------------------------------------------------------------------------
-- 4. Instantiate canonical history-conditioned choice.
------------------------------------------------------------------------

counterfactualPathChoiceSurface : HistoryChoice.HistoryConditionedChoiceSurface
counterfactualPathChoiceSurface =
  record
    { History = AdmittedPath
    ; Observation = CoarsePathObservation
    ; Pattern = PathPattern
    ; Choice = NextHistoricalChoice
    ; observe = observePath
    ; patternOf = patternOfPath
    ; choose = chooseNext
    ; historyReading =
        "Two admitted stratified paths may share endpoint, current stratum and model fidelity while retaining different order patterns and next reopening choices."
    }

canonicalCounterfactualChoiceWitness :
  HistoryChoice.DistinctHistoriesSameObservationDifferentChoice
    counterfactualPathChoiceSurface
canonicalCounterfactualChoiceWitness =
  record
    { leftHistory = repairThenCounterformation
    ; rightHistory = counterformationThenRepair
    ; historiesDistinct = λ ()
    ; samePresentObservation = refl
    ; choicesDiffer = λ ()
    }

coarsePathCannotRecoverNextChoice :
  INF.FactorsThrough observePath chooseNext → ⊥
coarsePathCannotRecoverNextChoice =
  HistoryChoice.historySensitiveChoiceCannotDescendThroughPresentObservation
    canonicalCounterfactualChoiceWitness

------------------------------------------------------------------------
-- 5. Counterfactual branch relation: alternatives are typed continuations,
-- not claims that both were actually enacted.
------------------------------------------------------------------------

data CounterfactualAlternative : AdmittedPath → AdmittedPath → Set where
  canonicalOrderAlternative :
    CounterfactualAlternative
      repairThenCounterformation
      counterformationThenRepair

canonicalPathsAreCounterfactualAlternatives :
  CounterfactualAlternative repairThenCounterformation counterformationThenRepair
canonicalPathsAreCounterfactualAlternatives = canonicalOrderAlternative

------------------------------------------------------------------------
-- 6. No-promotion boundaries.
------------------------------------------------------------------------

data SameEndpointMeansSameHistory : Set where

data SameStratumMeansSamePath : Set where

data SameFidelityMeansSameChoice : Set where

data CounterfactualAlternativeWasActuallyEnacted : Set where

data PathAssociativityMeansHistoricalOrderIrrelevant : Set where

data CounterfactualBranchIsPrediction : Set where

sameEndpointDoesNotMeanSameHistory : SameEndpointMeansSameHistory → ⊥
sameEndpointDoesNotMeanSameHistory ()

sameStratumDoesNotMeanSamePath : SameStratumMeansSamePath → ⊥
sameStratumDoesNotMeanSamePath ()

sameFidelityDoesNotMeanSameChoice : SameFidelityMeansSameChoice → ⊥
sameFidelityDoesNotMeanSameChoice ()

counterfactualAlternativeDoesNotMeanActuallyEnacted :
  CounterfactualAlternativeWasActuallyEnacted → ⊥
counterfactualAlternativeDoesNotMeanActuallyEnacted ()

pathAssociativityDoesNotEraseHistoricalOrder :
  PathAssociativityMeansHistoricalOrderIrrelevant → ⊥
pathAssociativityDoesNotEraseHistoricalOrder ()

counterfactualBranchIsNotPrediction : CounterfactualBranchIsPrediction → ⊥
counterfactualBranchIsNotPrediction ()

record StratifiedCounterfactualPathBoundary : Set where
  constructor stratified-counterfactual-path-boundary
  field
    admittedPathsComposeAssociatively : Bool
    sameEndpointCanHideDifferentOrder : Bool
    sameStratumCanHideDifferentOrder : Bool
    sameFidelityCanHideDifferentChoice : Bool
    historySensitiveChoiceExplicit : Bool
    counterfactualAlternativeMeansActualEnactment : Bool
    pathAssociativityErasesOrder : Bool
    branchCreatesPredictionAuthority : Bool

canonicalStratifiedCounterfactualPathBoundary : StratifiedCounterfactualPathBoundary
canonicalStratifiedCounterfactualPathBoundary =
  stratified-counterfactual-path-boundary
    true true true true true false false false
