module DASHI.Ontology.ProgenitorParentObserverRefinementTests where

open import DASHI.Core.Prelude using (Bool; true; false; _≡_; refl; ⊥)
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.FibrePreservingDynamicsExact as Dynamics
import DASHI.Core.SectionedProjectionProvenanceBridgeExact as Sectioned
import DASHI.Core.PredicatePullbackLatticeExact as Predicate
import DASHI.Cognition.PNF.ProofRelevantIdentityFibres as Identity

open import DASHI.Ontology.ProgenitorParentProjectionFibre using (projectParentSlot)
open import DASHI.Ontology.ProgenitorParentObserverDynamicsBridge
open import DASHI.Ontology.ProgenitorParentObservationAuthorityBridge
open import DASHI.Ontology.ProgenitorParentPredicateDescentBoundary
open import DASHI.Ontology.ProgenitorParentPNFPullbackLattice
open import Ontology.Hecke.CurrentSaturatedObserverRefinementBridgeExact

p8810NotSeparatingRegression : Observer.Separating parentSlotObserver → ⊥
p8810NotSeparatingRegression = p8810SlotNotSeparating

geneticNotSeparatingRegression : Observer.Separating geneticObserver → ⊥
geneticNotSeparatingRegression = geneticObserverNotSeparating

legalFinalizationHiddenRegression :
  Dynamics.HiddenTransition
    parentFibreRestrictionCore
    finalizeLegalParenthood
    preFinalizationCarrier
legalFinalizationHiddenRegression = legalFinalizationIsHiddenP8810Transition

geneticDoesNotDescendRegression :
  Predicate.FibreConstantPredicate projectParentSlot geneticP → ⊥
geneticDoesNotDescendRegression = geneticPredicateNotFibreConstant

genealogicalParentDoesNotDescendRegression :
  Predicate.FibreConstantPredicate projectParentSlot genealogicalParentP → ⊥
genealogicalParentDoesNotDescendRegression =
  genealogicalParentPredicateNotFibreConstant

separatingDisclosureObserverRegression :
  Observer.Separating variantDisclosureObserver
separatingDisclosureObserverRegression = variantDisclosureObserverSeparating

separationStillNoSurfaceWorldAuthorityRegression :
  Identity.WorldCanonicalPermission Identity.surfaceLocal → ⊥
separationStillNoSurfaceWorldAuthorityRegression =
  separatingObserverDoesNotGrantSurfaceWorldIdentity

saturatedHeckeCoarseObserverNotSeparatingRegression :
  Observer.Separating coarseSaturatedObserver → ⊥
saturatedHeckeCoarseObserverNotSeparatingRegression =
  coarseSaturatedObserverNotSeparating

observerMonotonicityBoundaryRegression :
  Observer.ObserverRefinementBoundary.addingObserversMonotonicallyShrinksResidualFibre
    Observer.canonicalObserverRefinementBoundary ≡ true
observerMonotonicityBoundaryRegression = refl

sectionNeedsResidualBoundaryRegression :
  Sectioned.SectionedProjectionBoundary.sectionAloneReconstructsEveryFineState
    Sectioned.canonicalSectionedProjectionBoundary ≡ false
sectionNeedsResidualBoundaryRegression = refl

predicatePullbackMeetBoundaryRegression :
  Predicate.PredicatePullbackLatticeBoundary.pullbackPreservesPredicateMeet
    Predicate.canonicalPredicatePullbackLatticeBoundary ≡ true
predicatePullbackMeetBoundaryRegression = refl
