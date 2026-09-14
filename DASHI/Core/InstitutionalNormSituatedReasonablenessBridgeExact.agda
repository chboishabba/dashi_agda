module DASHI.Core.InstitutionalNormSituatedReasonablenessBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Core.InstitutionalNormProductionExact as Norm
import DASHI.Core.ObserverSituatedReasonablenessExact as Situated

------------------------------------------------------------------------
-- INSTITUTIONAL NORM PRODUCTION × SITUATED REASONABLENESS
--
-- Thin bridge only.  It does not make lobbying, proximity, consultation or
-- social convention causally determinative of a legal reasonableness standard.
-- It isolates a narrower structural point: the currently declared standard can
-- be the same while the history by which that standard was produced differs.
-- Therefore production-history questions cannot be answered from the bare
-- present standard alone.
------------------------------------------------------------------------

parentNormProductionBoundary : Norm.InstitutionalNormProductionBoundary
parentNormProductionBoundary = Norm.canonicalInstitutionalNormProductionBoundary

parentSituatedReasonablenessBoundary : Situated.SituatedReasonablenessBoundary
parentSituatedReasonablenessBoundary = Situated.canonicalSituatedReasonablenessBoundary

data StandardHistoryWorld : Set where
  broadAccessProductionWorld : StandardHistoryWorld
  narrowAccessProductionWorld : StandardHistoryWorld

data ReasonablenessStandardSurface : Set where
  sameDeclaredReasonablenessStandard : ReasonablenessStandardSurface

data StandardProductionHistory : Set where
  broadAccessHistory : StandardProductionHistory
  narrowAccessHistory : StandardProductionHistory

data StandardHistoryQuery : Set where
  declaredStandardQuery : StandardHistoryQuery
  productionHistoryQuery : StandardHistoryQuery

data StandardHistoryAnswer : Set where
  sameDeclaredStandardAnswer : StandardHistoryAnswer
  broadAccessHistoryAnswer : StandardHistoryAnswer
  narrowAccessHistoryAnswer : StandardHistoryAnswer

reasonablenessStandardSurface : StandardHistoryWorld → ReasonablenessStandardSurface
reasonablenessStandardSurface world = sameDeclaredReasonablenessStandard

standardProductionHistory : StandardHistoryWorld → StandardProductionHistory
standardProductionHistory broadAccessProductionWorld = broadAccessHistory
standardProductionHistory narrowAccessProductionWorld = narrowAccessHistory

standardHistoryAnswer :
  StandardHistoryQuery → StandardHistoryWorld → StandardHistoryAnswer
standardHistoryAnswer declaredStandardQuery world = sameDeclaredStandardAnswer
standardHistoryAnswer productionHistoryQuery broadAccessProductionWorld =
  broadAccessHistoryAnswer
standardHistoryAnswer productionHistoryQuery narrowAccessProductionWorld =
  narrowAccessHistoryAnswer

standardHistorySemantics :
  Query.QuerySemantics
    StandardHistoryWorld
    StandardHistoryQuery
    StandardHistoryAnswer
standardHistorySemantics = Query.querySemantics standardHistoryAnswer

declaredStandardAdequate :
  Query.AdequateFor
    reasonablenessStandardSurface
    standardHistorySemantics
    declaredStandardQuery
declaredStandardAdequate =
  Query.factorsForQuery
    (λ surface → sameDeclaredStandardAnswer)
    (λ world → refl)

SameReasonablenessStandardDifferentProductionHistoryDefect : Set₁
SameReasonablenessStandardDifferentProductionHistoryDefect =
  Query.QueryAdequacyDefect
    reasonablenessStandardSurface
    standardHistorySemantics
    productionHistoryQuery

sameReasonablenessStandardDifferentProductionHistoryDefect :
  SameReasonablenessStandardDifferentProductionHistoryDefect
sameReasonablenessStandardDifferentProductionHistoryDefect =
  Query.queryAdequacyDefect
    broadAccessProductionWorld
    narrowAccessProductionWorld
    refl
    (λ ())

ProductionHistoryThroughDeclaredStandard : Set₁
ProductionHistoryThroughDeclaredStandard =
  Query.AdequateFor
    reasonablenessStandardSurface
    standardHistorySemantics
    productionHistoryQuery

productionHistoryDoesNotFactorThroughDeclaredStandard :
  ProductionHistoryThroughDeclaredStandard → ⊥
productionHistoryDoesNotFactorThroughDeclaredStandard =
  Query.queryAdequacyDefectBlocksFactorisation
    sameReasonablenessStandardDifferentProductionHistoryDefect

------------------------------------------------------------------------
-- Boundary: legal application and political/historical critique are different
-- consumer queries.  A court or administrator may be required to apply the
-- extant legal standard without thereby proving the standard's production
-- history neutral or normatively optimal.
------------------------------------------------------------------------

record InstitutionalNormReasonablenessBoundary : Set where
  constructor institutionalNormReasonablenessBoundary
  field
    parentNormProductionReused : Bool
    parentSituatedReasonablenessReused : Bool
    legallySpecifiedStandardAutomaticallyNeutralProductionHistory : Bool
    institutionalConventionAutomaticallyObjectiveTruth : Bool
    proximityAutomaticallyDeterminesReasonablenessNorm : Bool
    consultationAutomaticallyEqualInfluence : Bool
    presentStandardAutomaticallyRevealsProductionHistory : Bool
    historicalProductionCritiqueAutomaticallyInvalidatesCurrentRule : Bool
    currentRuleApplicationDoesNotRequireNeutralProductionHistory : Bool
    productionHistoryCanRemainDistinctCritiqueCoordinate : Bool

open InstitutionalNormReasonablenessBoundary public

canonicalInstitutionalNormReasonablenessBoundary :
  InstitutionalNormReasonablenessBoundary
canonicalInstitutionalNormReasonablenessBoundary =
  institutionalNormReasonablenessBoundary
    true
    true
    false
    false
    false
    false
    false
    false
    true
    true
