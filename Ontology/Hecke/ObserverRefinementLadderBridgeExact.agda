module Ontology.Hecke.ObserverRefinementLadderBridgeExact where

------------------------------------------------------------------------
-- LEGACY HECKE SEPARATOR LADDER -> GENERIC OBSERVER REFINEMENT
--
-- The older Hecke representation lane predates the generic observer lattice.
-- It already contains exact collision/refinement data.  This module reuses
-- those theorems rather than creating another Hecke summary.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Physics.Closure.ShiftContractCollapseTime as SCT
import DASHI.Physics.Closure.ShiftContractGeneratorTaxonomy as GT
import Ontology.Hecke.CertifiedRepresentativePersistence as CRP
import Ontology.Hecke.CurrentSaturatedForcedStableCollapse as Saturated
import Ontology.Hecke.CurrentSaturatedOrbitSummaryCollapse as SummaryCollapse
import Ontology.Hecke.DefectPersistenceRefinement as Refinement
import Ontology.Hecke.FactorVecDefectOrbitSummaries as FOS

collapseTimeObserver :
  Observer.Observer CRP.CertifiedRepresentativeClass SCT.CollapseTime
collapseTimeObserver = CRP.certifiedRepresentativeCollapseTime

stayRefinementObserver :
  Observer.Observer CRP.CertifiedRepresentativeClass Refinement.StayRefinement
stayRefinementObserver = Refinement.stayRefinementAt

width1 width3 : CRP.CertifiedRepresentativeClass
width1 = CRP.stayRep GT.certifiedExplicitWidth1
width3 = CRP.stayRep GT.certifiedExplicitWidth3

sameCollapseTimeWidth1Width3 :
  collapseTimeObserver width1 ≡ collapseTimeObserver width3
sameCollapseTimeWidth1Width3 = refl

lowStayNotHighStay : Refinement.lowStay ≡ Refinement.highStay → ⊥
lowStayNotHighStay ()

stayRefinementSplitsWidth1Width3 :
  stayRefinementObserver width1 ≡ stayRefinementObserver width3 → ⊥
stayRefinementSplitsWidth1Width3
  rewrite Refinement.explicitWidth1-lowStay
        | Refinement.explicitWidth3-highStay =
  lowStayNotHighStay

collapsePlusStayStrictlyRefinesCollapseTime :
  Observer.StrictRefinement
    collapseTimeObserver
    (Observer.pairObserver collapseTimeObserver stayRefinementObserver)
collapsePlusStayStrictlyRefinesCollapseTime =
  Observer.strictPairRefinement
    collapseTimeObserver
    stayRefinementObserver
    width1
    width3
    sameCollapseTimeWidth1Width3
    stayRefinementSplitsWidth1Width3

collapseTimeCollision : Observer.ObserverCollision collapseTimeObserver
collapseTimeCollision =
  Observer.observerCollision
    width1
    width3
    sameCollapseTimeWidth1Width3
    width1NotWidth3
  where
    width1NotWidth3 : width1 ≡ width3 → ⊥
    width1NotWidth3 same =
      stayRefinementSplitsWidth1Width3 (cong stayRefinementObserver same)

collapseTimeCannotSeparateCertifiedRepresentatives :
  Observer.Separating collapseTimeObserver → ⊥
collapseTimeCannotSeparateCertifiedRepresentatives =
  Observer.collisionBlocksSeparation collapseTimeCollision

------------------------------------------------------------------------
-- Residual fibre after the current whole orbit summary.
------------------------------------------------------------------------

saturatedOrbitSummaryObserver :
  Observer.Observer Saturated.CurrentSaturatedGenerator FOS.DefectOrbitSummary
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

saturatedWidth3NotDense : saturatedWidth3 ≡ saturatedDense → ⊥
saturatedWidth3NotDense ()

currentSaturatedWholeSummaryCollision :
  Observer.ObserverCollision saturatedOrbitSummaryObserver
currentSaturatedWholeSummaryCollision =
  Observer.observerCollision
    saturatedWidth3
    saturatedDense
    sameSaturatedWholeSummary
    saturatedWidth3NotDense

currentSaturatedWholeSummaryCannotSeparate :
  Observer.Separating saturatedOrbitSummaryObserver → ⊥
currentSaturatedWholeSummaryCannotSeparate =
  Observer.collisionBlocksSeparation currentSaturatedWholeSummaryCollision

currentSaturatedResidualFibreAtWidth3 : Set
currentSaturatedResidualFibreAtWidth3 =
  Observer.ResidualObservationFibre
    (saturatedOrbitSummaryObserver ∷ [])
    saturatedWidth3

saturatedDenseLiesInWidth3ResidualFibre :
  currentSaturatedResidualFibreAtWidth3
saturatedDenseLiesInWidth3ResidualFibre =
  saturatedDense , (sameSaturatedWholeSummary , tt)

record HeckeObserverRefinementLadderBoundary : Set where
  constructor heckeObserverRefinementLadderBoundary
  field
    collapseTimeStrictlyRefinedByStayCoordinate : Bool
    collapseTimeStrictlyRefinedByStayCoordinateIsTrue :
      collapseTimeStrictlyRefinedByStayCoordinate ≡ true
    fullCurrentSaturatedSummaryStillCollides : Bool
    fullCurrentSaturatedSummaryStillCollidesIsTrue :
      fullCurrentSaturatedSummaryStillCollides ≡ true
    richerSeparatorStillRequiredAboveCurrentSummary : Bool
    richerSeparatorStillRequiredAboveCurrentSummaryIsTrue :
      richerSeparatorStillRequiredAboveCurrentSummary ≡ true

canonicalHeckeObserverRefinementLadderBoundary :
  HeckeObserverRefinementLadderBoundary
canonicalHeckeObserverRefinementLadderBoundary =
  heckeObserverRefinementLadderBoundary
    true refl
    true refl
    true refl
