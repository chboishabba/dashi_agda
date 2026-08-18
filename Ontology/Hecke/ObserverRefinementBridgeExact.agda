module Ontology.Hecke.ObserverRefinementBridgeExact where

------------------------------------------------------------------------
-- HECKE OBSERVER REFINEMENT AS A GENERIC COLLISION/SPLITTER PROBLEM
--
-- The older Hecke lane already discovered refinement operationally:
-- collapse class -> stay refinement -> orbit summary -> triad histogram ->
-- sector correlation.  This module does not invent another Hecke invariant.
-- It instantiates the generic observer-refinement theorem on existing exact
-- data and retains the current saturated whole-summary collapse as a residual
-- fibre witness.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Core.ObserverRefinementExact as Observer
import DASHI.Physics.Closure.ShiftContractGeneratorTaxonomy as GT
import Ontology.Hecke.CertifiedRepresentativePersistence as CRP
import Ontology.Hecke.CurrentSaturatedForcedStableCollapse as Saturated
import Ontology.Hecke.CurrentSaturatedOrbitSummaryCollapse as SummaryCollapse
import Ontology.Hecke.DefectPersistenceRefinement as Refinement

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

------------------------------------------------------------------------
-- Exact strict refinement: collapse time alone collides on two stay states,
-- while the added Hecke persistence coordinate splits them.
------------------------------------------------------------------------

collapseTimeObserver :
  CRP.CertifiedRepresentativeClass →
  DASHI.Physics.Closure.ShiftContractCollapseTime.CollapseTime
collapseTimeObserver = CRP.certifiedRepresentativeCollapseTime

stayRefinementObserver :
  CRP.CertifiedRepresentativeClass → Refinement.StayRefinement
stayRefinementObserver = Refinement.stayRefinementAt

width1 width3 : CRP.CertifiedRepresentativeClass
width1 = CRP.stayRep GT.certifiedExplicitWidth1
width3 = CRP.stayRep GT.certifiedExplicitWidth3

sameCollapseTimeWidth1Width3 :
  collapseTimeObserver width1 ≡ collapseTimeObserver width3
sameCollapseTimeWidth1Width3 = refl

lowStay≢highStay : Refinement.lowStay ≢ Refinement.highStay
lowStay≢highStay ()

stayRefinementSplitsWidth1Width3 :
  stayRefinementObserver width1 ≢ stayRefinementObserver width3
stayRefinementSplitsWidth1Width3
  rewrite Refinement.explicitWidth1-lowStay
        | Refinement.explicitWidth3-highStay =
  lowStay≢highStay

collapsePlusStayStrictlyRefinesCollapseTime :
  Observer.StrictRefinement
    collapseTimeObserver
    (Observer.jointObserver collapseTimeObserver stayRefinementObserver)
collapsePlusStayStrictlyRefinesCollapseTime =
  Observer.jointStrictlyRefinesWhenAddedObserverSplitsCollision
    collapseTimeObserver
    stayRefinementObserver
    sameCollapseTimeWidth1Width3
    stayRefinementSplitsWidth1Width3

collapseTimeCannotSeparateCurrentCertifiedCarrier :
  Observer.Separating collapseTimeObserver → ⊥
collapseTimeCannotSeparateCurrentCertifiedCarrier =
  Observer.strictRefinementRulesOutCoarseSeparation
    collapsePlusStayStrictlyRefinesCollapseTime

------------------------------------------------------------------------
-- Exact residual collision: the FULL current DefectOrbitSummary still
-- collapses on the saturated branch.  This formally justifies searching for a
-- richer triad/correlation observer rather than rereading the same summary.
------------------------------------------------------------------------

saturatedOrbitSummaryObserver :
  Saturated.CurrentSaturatedGenerator →
  Ontology.Hecke.FactorVecDefectOrbitSummaries.DefectOrbitSummary
saturatedOrbitSummaryObserver = Saturated.saturatedOrbitSummaryP2At

saturatedWidth3 saturatedDense : Saturated.CurrentSaturatedGenerator
saturatedWidth3 = Saturated.saturatedExplicitWidth3
saturatedDense = Saturated.saturatedDenseComposed

sameSaturatedWholeSummary :
  saturatedOrbitSummaryObserver saturatedWidth3
    ≡ saturatedOrbitSummaryObserver saturatedDense
sameSaturatedWholeSummary =
  trans
    (SummaryCollapse.saturatedOrbitSummary≡canonical saturatedWidth3)
    (sym (SummaryCollapse.saturatedOrbitSummary≡canonical saturatedDense))

saturatedWidth3≢Dense : saturatedWidth3 ≢ saturatedDense
saturatedWidth3≢Dense ()

currentSaturatedWholeSummaryCollision :
  Observer.Collision saturatedOrbitSummaryObserver
currentSaturatedWholeSummaryCollision =
  Observer.collision
    saturatedWidth3
    saturatedDense
    sameSaturatedWholeSummary
    saturatedWidth3≢Dense

currentSaturatedWholeSummaryCannotSeparate :
  Observer.Separating saturatedOrbitSummaryObserver → ⊥
currentSaturatedWholeSummaryCannotSeparate =
  Observer.collisionRulesOutSeparation currentSaturatedWholeSummaryCollision
