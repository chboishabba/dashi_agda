module DASHI.Core.InstitutionalNormProductionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- INSTITUTIONAL NORM PRODUCTION / NATURALISATION
--
-- This is a generic finite structural owner.  It does not identify any
-- historical institution, person, ideology, lobbying outcome or legal rule.
-- It isolates one reusable defect: a later baseline can erase production
-- history relevant to a downstream query, while a joined observer retaining
-- that history repairs the particular information loss.
------------------------------------------------------------------------

data BaselineWorld : Set where
  negotiatedHistoryWorld : BaselineWorld
  excludedHistoryWorld : BaselineWorld

data BaselineSurface : Set where
  sameInstitutionalBaseline : BaselineSurface

data ProductionHistory : Set where
  negotiatedProductionHistory : ProductionHistory
  excludedProductionHistory : ProductionHistory

data NormQuery : Set where
  baselineIdentityQuery : NormQuery
  productionHistoryQuery : NormQuery

data NormAnswer : Set where
  sameBaselineAnswer : NormAnswer
  negotiatedHistoryAnswer : NormAnswer
  excludedHistoryAnswer : NormAnswer

baselineSurface : BaselineWorld → BaselineSurface
baselineSurface world = sameInstitutionalBaseline

productionHistory : BaselineWorld → ProductionHistory
productionHistory negotiatedHistoryWorld = negotiatedProductionHistory
productionHistory excludedHistoryWorld = excludedProductionHistory

normAnswer : NormQuery → BaselineWorld → NormAnswer
normAnswer baselineIdentityQuery world = sameBaselineAnswer
normAnswer productionHistoryQuery negotiatedHistoryWorld = negotiatedHistoryAnswer
normAnswer productionHistoryQuery excludedHistoryWorld = excludedHistoryAnswer

normSemantics : Query.QuerySemantics BaselineWorld NormQuery NormAnswer
normSemantics = Query.querySemantics normAnswer

baselineIdentityAdequate :
  Query.AdequateFor baselineSurface normSemantics baselineIdentityQuery
baselineIdentityAdequate =
  Query.factorsForQuery
    (λ surface → sameBaselineAnswer)
    (λ world → refl)

ProductionHistoryQueryAdequacyDefect : Set₁
ProductionHistoryQueryAdequacyDefect =
  Query.QueryAdequacyDefect baselineSurface normSemantics productionHistoryQuery

productionHistoryQueryAdequacyDefect : ProductionHistoryQueryAdequacyDefect
productionHistoryQueryAdequacyDefect =
  Query.queryAdequacyDefect
    negotiatedHistoryWorld
    excludedHistoryWorld
    refl
    (λ ())

ProductionHistoryQueryAdequate : Set₁
ProductionHistoryQueryAdequate =
  Query.AdequateFor baselineSurface normSemantics productionHistoryQuery

productionHistoryNotAdequate : ProductionHistoryQueryAdequate → ⊥
productionHistoryNotAdequate =
  Query.queryAdequacyDefectBlocksFactorisation productionHistoryQueryAdequacyDefect

------------------------------------------------------------------------
-- Retained provenance/history is a strict observer refinement of the later
-- baseline on this finite witness.  Refinement is query-local information
-- repair, not a proof that the richer observer is complete.
------------------------------------------------------------------------

baselineWithHistory : BaselineWorld → (BaselineSurface × ProductionHistory)
baselineWithHistory = Observer.pairObserver baselineSurface productionHistory

BaselineWithHistoryStrictRefinement : Set
BaselineWithHistoryStrictRefinement =
  Observer.StrictRefinement baselineSurface baselineWithHistory

baselineWithHistoryStrictlyRefinesBaseline :
  BaselineWithHistoryStrictRefinement
baselineWithHistoryStrictlyRefinesBaseline =
  Observer.strictPairRefinement
    baselineSurface
    productionHistory
    negotiatedHistoryWorld
    excludedHistoryWorld
    refl
    (λ ())

------------------------------------------------------------------------
-- Non-promotion boundary.
--
-- `proximityAutomaticallyEstablishesInfluenceCausation = false` is
-- deliberately stronger than merely saying a particular observed edge has not
-- yet been paid: proximity/access is a distinct coordinate from a causal
-- influence conclusion.
------------------------------------------------------------------------

record InstitutionalNormProductionBoundary : Set where
  constructor institutionalNormProductionBoundary
  field
    legalValidityAutomaticallyPoliticalNeutrality : Bool
    legalValidityAutomaticallyMoralJustification : Bool
    formalEqualityAutomaticallyEqualNormProductionPower : Bool
    institutionalFamiliarityAutomaticallyEpistemicSuperiority : Bool
    statusSignalAutomaticallySubstantiveAdequacy : Bool
    lawfulLobbyingAutomaticallyNeutralPolicyOutcome : Bool
    consultationAutomaticallyBalancedParticipation : Bool
    proximityAutomaticallyEstablishesInfluenceCausation : Bool
    naturalisationCanEraseProductionHistory : Bool
    retainedHistoryCanRepairBaselineObserver : Bool

open InstitutionalNormProductionBoundary public

canonicalInstitutionalNormProductionBoundary : InstitutionalNormProductionBoundary
canonicalInstitutionalNormProductionBoundary =
  institutionalNormProductionBoundary
    false
    false
    false
    false
    false
    false
    false
    false
    true
    true
