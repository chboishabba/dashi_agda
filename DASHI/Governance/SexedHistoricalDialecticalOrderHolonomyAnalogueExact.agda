module DASHI.Governance.SexedHistoricalDialecticalOrderHolonomyAnalogueExact where

------------------------------------------------------------------------
-- DIALECTICAL ORDER DEFECT / HOLONOMY ANALOGUE
--
-- Structural cross-pollination only.  This owner does NOT import draft PR #666
-- and does not claim gauge curvature, Wilson loops, or literal geometric
-- holonomy in historical dynamics.
--
-- It isolates the historical question suggested by the same formal pattern:
--
--   reinterpret then institutionalise
--   need not equal
--   institutionalise then reinterpret.
--
-- The two routes can even occupy the same coarse historical stratum while
-- differing in fine subject-formation and power residues.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.SexedHistoricalTransitionHyperfabricExact as Transition
import DASHI.Governance.SexedHistoricalCoConstitutionHyperfabricExact as Hyper
import DASHI.Governance.SexedHistoricalStatisticalExperimentHyperfabricExact as Stats

------------------------------------------------------------------------
-- Fine historical state and two path operators.
------------------------------------------------------------------------

data SymbolicGrammar : Set where
  inheritedGrammar
  reinterpretedGrammar
  institutionallyNormalisedGrammar
  contestedRearticulation
  : SymbolicGrammar

data InstitutionalStatus : Set where
  inheritedInstitution
  formallyCorrectedInstitution
  contestedInstitution
  : InstitutionalStatus

data HistoricalResidue : Set where
  inheritedResidue
  reinterpretationResidue
  institutionalResidue
  mixedResidue
  : HistoricalResidue

record FineHistoricalState : Set where
  constructor fine-historical-state
  field
    grammar : SymbolicGrammar
    institution : InstitutionalStatus
    residue : HistoricalResidue
    relation : Stats.ConstructionDirection
    power : Hyper.PowerLevel

open FineHistoricalState public

seed : FineHistoricalState
seed =
  fine-historical-state
    inheritedGrammar
    inheritedInstitution
    inheritedResidue
    Stats.masculineToFeminine
    Hyper.highPower

reinterpret : FineHistoricalState → FineHistoricalState
reinterpret s =
  fine-historical-state
    reinterpretedGrammar
    (institution s)
    reinterpretationResidue
    (relation s)
    (power s)

institutionalise : FineHistoricalState → FineHistoricalState
institutionalise s with grammar s
... | inheritedGrammar =
  fine-historical-state
    institutionallyNormalisedGrammar
    formallyCorrectedInstitution
    institutionalResidue
    (relation s)
    Hyper.mediumPower
... | reinterpretedGrammar =
  fine-historical-state
    contestedRearticulation
    formallyCorrectedInstitution
    mixedResidue
    (relation s)
    Hyper.mediumPower
... | institutionallyNormalisedGrammar =
  fine-historical-state
    institutionallyNormalisedGrammar
    formallyCorrectedInstitution
    institutionalResidue
    (relation s)
    Hyper.mediumPower
... | contestedRearticulation =
  fine-historical-state
    contestedRearticulation
    formallyCorrectedInstitution
    mixedResidue
    (relation s)
    Hyper.mediumPower

reinterpretAfterInstitutionalise : FineHistoricalState
reinterpretAfterInstitutionalise = reinterpret (institutionalise seed)

institutionaliseAfterReinterpret : FineHistoricalState
institutionaliseAfterReinterpret = institutionalise (reinterpret seed)

orderDefect :
  reinterpretAfterInstitutionalise ≡ institutionaliseAfterReinterpret → ⊥
orderDefect ()

------------------------------------------------------------------------
-- Coarse observer erases the order information.
------------------------------------------------------------------------

data CoarseHistoricalStratum : Set where
  formallyCorrectedContested
  inheritedCoarse
  : CoarseHistoricalStratum

coarseStratum : FineHistoricalState → CoarseHistoricalStratum
coarseStratum s with institution s
... | inheritedInstitution = inheritedCoarse
... | formallyCorrectedInstitution = formallyCorrectedContested
... | contestedInstitution = formallyCorrectedContested

sameCoarseStratumAfterBothOrders :
  coarseStratum reinterpretAfterInstitutionalise
  ≡ coarseStratum institutionaliseAfterReinterpret
sameCoarseStratumAfterBothOrders = refl

------------------------------------------------------------------------
-- The same coarse stratum cannot recover historical transport order.
------------------------------------------------------------------------

data PathOrder : Set where
  institutionThenReinterpret
  reinterpretThenInstitution
  : PathOrder

data OrderFineState : Set where
  institutionFirstState
  reinterpretationFirstState
  : OrderFineState

orderState : OrderFineState → FineHistoricalState
orderState institutionFirstState = reinterpretAfterInstitutionalise
orderState reinterpretationFirstState = institutionaliseAfterReinterpret

coarseOrderSurface : OrderFineState → CoarseHistoricalStratum
coarseOrderSurface s = coarseStratum (orderState s)

pathOrder : OrderFineState → PathOrder
pathOrder institutionFirstState = institutionThenReinterpret
pathOrder reinterpretationFirstState = reinterpretThenInstitution

coarseStratumCannotRecoverTransportOrder :
  INF.FactorsThrough coarseOrderSurface pathOrder → ⊥
coarseStratumCannotRecoverTransportOrder =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      institutionFirstState
      reinterpretationFirstState
      refl
      (λ ()))

------------------------------------------------------------------------
-- Statistical implication: route/order should be a first-class design factor.
------------------------------------------------------------------------

data OrderMeasurementRole : Set where
  routeRecorded
  routeCollapsed
  : OrderMeasurementRole

data HistoricalSequencePromotesStageTheory : Set where

data OrderDefectPromotesGaugeCurvature : Set where

data SameCoarseOutcomePromotesSameFormationHistory : Set where

data DialecticalOppositionPromotesNecessarySynthesis : Set where

historicalSequenceDoesNotPromoteStageTheory :
  HistoricalSequencePromotesStageTheory → ⊥
historicalSequenceDoesNotPromoteStageTheory ()

orderDefectDoesNotPromoteGaugeCurvature :
  OrderDefectPromotesGaugeCurvature → ⊥
orderDefectDoesNotPromoteGaugeCurvature ()

sameCoarseOutcomeDoesNotPromoteSameFormationHistory :
  SameCoarseOutcomePromotesSameFormationHistory → ⊥
sameCoarseOutcomeDoesNotPromoteSameFormationHistory ()

dialecticalOppositionDoesNotPromoteNecessarySynthesis :
  DialecticalOppositionPromotesNecessarySynthesis → ⊥
dialecticalOppositionDoesNotPromoteNecessarySynthesis ()

------------------------------------------------------------------------
-- Existing transition-residual boundary remains authoritative.
------------------------------------------------------------------------

formalCorrectionStillDoesNotCloseSymbolicResidual :
  Transition.SuffrageCorrectionImpliesWholePowerParity → ⊥
formalCorrectionStillDoesNotCloseSymbolicResidual =
  Transition.suffrageCorrectionDoesNotImplyWholePowerParity

record SexedHistoricalDialecticalOrderBoundary : Set where
  constructor sexed-historical-dialectical-order-boundary
  field
    historicalTransformsCommuteUniversally : Bool
    coarseStratumDeterminesTransportOrder : Bool
    sameCoarseOutcomeMeansSameHistory : Bool
    oppositionRequiresSynthesis : Bool
    orderDefectEqualsGaugeCurvature : Bool
    routeShouldBeMeasuredWhenSubstantivelyDefined : Bool

canonicalSexedHistoricalDialecticalOrderBoundary :
  SexedHistoricalDialecticalOrderBoundary
canonicalSexedHistoricalDialecticalOrderBoundary =
  sexed-historical-dialectical-order-boundary
    false false false false false true
