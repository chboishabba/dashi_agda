module DASHI.Ontology.ProgenitorParentObserverDynamicsBridge where

------------------------------------------------------------------------
-- Parent/progenitor instantiation of the generic observer-refinement and
-- fibre-preserving dynamics cores.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.FibrePreservingDynamicsExact as Dynamics

open import DASHI.Ontology.ProgenitorParentHyperfabric
open import DASHI.Ontology.ProgenitorParentProjectionFibre
open import DASHI.Ontology.ProgenitorParentPNFPullbackLattice

------------------------------------------------------------------------
-- Observers.
------------------------------------------------------------------------

parentSlotObserver : Observer.Observer ParentCarrier WikidataParentSlot
parentSlotObserver = projectParentSlot

geneticObserver : Observer.Observer ParentCarrier Bool
geneticObserver carrier = geneticContributor (carrierRelation carrier)

genealogicalParentObserver : Observer.Observer ParentCarrier Bool
genealogicalParentObserver carrier = genealogicalParent (carrierRelation carrier)

legalParentObserver : Observer.Observer ParentCarrier Bool
legalParentObserver carrier = legalParent (carrierRelation carrier)

disclosureObserver : Observer.Observer ParentCarrier Bool
disclosureObserver carrier = identityDisclosable (carrierRelation carrier)

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

------------------------------------------------------------------------
-- P8810 is strictly refined by adding the genetic observer.
------------------------------------------------------------------------

p8810GeneticStrictRefinement :
  Observer.StrictRefinement
    parentSlotObserver
    (Observer.pairObserver parentSlotObserver geneticObserver)
p8810GeneticStrictRefinement =
  Observer.strictPairRefinement
    parentSlotObserver
    geneticObserver
    anonymousDonorCarrier
    adoptiveCarrier
    refl
    trueNotFalse

p8810SlotNotSeparating : Observer.Separating parentSlotObserver → ⊥
p8810SlotNotSeparating =
  Observer.collisionBlocksSeparation
    (Observer.observerCollision
      anonymousDonorCarrier
      adoptiveCarrier
      refl
      donorNotAdoptive)
  where
  donorNotAdoptive : anonymousDonorCarrier ≡ adoptiveCarrier → ⊥
  donorNotAdoptive equality =
    trueNotFalse
      (cong
        (λ carrier → progenitorRelation (carrierRelation carrier))
        equality)

------------------------------------------------------------------------
-- Genetic contribution itself is also a lossy observer: two genetic carriers
-- can disagree on genealogical parenthood.
------------------------------------------------------------------------

ordinaryGeneticParentCarrier : ParentCarrier
ordinaryGeneticParentCarrier = parentCarrier individualLevel singleMother

geneticObserverCollision : Observer.ObserverCollision geneticObserver
geneticObserverCollision =
  Observer.observerCollision
    anonymousDonorCarrier
    ordinaryGeneticParentCarrier
    refl
    donorNotOrdinaryParent
  where
  donorNotOrdinaryParent :
    anonymousDonorCarrier ≡ ordinaryGeneticParentCarrier → ⊥
  donorNotOrdinaryParent equality =
    falseNotTrue
      (cong
        (λ carrier → genealogicalParent (carrierRelation carrier))
        equality)

geneticObserverNotSeparating : Observer.Separating geneticObserver → ⊥
geneticObserverNotSeparating =
  Observer.collisionBlocksSeparation geneticObserverCollision

------------------------------------------------------------------------
-- Vertical dynamics over the existing parent FibreRestrictionCore.
--
-- Legal finalization changes a fine relation coordinate while the visible
-- P8810 slot remains unchanged.  This is the parent analogue of marked
-- arithmetic motion that disappears after quotienting.
------------------------------------------------------------------------

finalizedSingleMotherRelation : RelationVector
finalizedSingleMotherRelation =
  relationVector true true true false true true true true true true true true

preFinalizationSingleMotherRelation : RelationVector
preFinalizationSingleMotherRelation =
  relationVector true true true false true true true false true true true true

preFinalizationCarrier : ParentCarrier
preFinalizationCarrier =
  parentCarrier individualLevel preFinalizationSingleMotherRelation

postFinalizationCarrier : ParentCarrier
postFinalizationCarrier =
  parentCarrier individualLevel finalizedSingleMotherRelation

finalizeLegalParenthood : ParentCarrier → ParentCarrier
finalizeLegalParenthood carrier =
  parentCarrier (carrierLevel carrier) finalizedSingleMotherRelation

finalizePreservesParentSlot :
  Dynamics.SurfaceInvariant parentFibreRestrictionCore finalizeLegalParenthood
finalizePreservesParentSlot carrier = refl

finalizationEndomorphism : Dynamics.FibreEndomorphism parentFibreRestrictionCore
finalizationEndomorphism =
  Dynamics.fibreEndomorphism finalizeLegalParenthood finalizePreservesParentSlot

preToPostIsExact :
  finalizeLegalParenthood preFinalizationCarrier ≡ postFinalizationCarrier
preToPostIsExact = refl

finalizationActuallyChangesFineState :
  finalizeLegalParenthood preFinalizationCarrier ≡ preFinalizationCarrier → ⊥
finalizationActuallyChangesFineState equality =
  trueNotFalse
    (cong
      (λ carrier → legalParent (carrierRelation carrier))
      equality)

legalFinalizationIsHiddenP8810Transition :
  Dynamics.HiddenTransition
    parentFibreRestrictionCore
    finalizeLegalParenthood
    preFinalizationCarrier
legalFinalizationIsHiddenP8810Transition =
  Dynamics.hiddenTransition
    finalizationActuallyChangesFineState
    refl

legalFinalizationWitnessesP8810ProjectionLoss :
  ((a b : ParentCarrier) →
    projectParentSlot a ≡ projectParentSlot b → a ≡ b) →
  ⊥
legalFinalizationWitnessesP8810ProjectionLoss =
  Dynamics.hiddenTransitionWitnessesProjectionNoninjective
    legalFinalizationIsHiddenP8810Transition

------------------------------------------------------------------------
-- Disclosure is a fine coordinate independent of the public parent slot.
------------------------------------------------------------------------

anonymousDonorDisclosableRelation : RelationVector
anonymousDonorDisclosableRelation =
  relationVector true true true false false false false false false false true true

anonymousDonorDisclosableCarrier : ParentCarrier
anonymousDonorDisclosableCarrier =
  parentCarrier individualLevel anonymousDonorDisclosableRelation

sameP8810DifferentDisclosure :
  parentSlotObserver anonymousDonorCarrier
    ≡ parentSlotObserver anonymousDonorDisclosableCarrier
  × disclosureObserver anonymousDonorCarrier ≡ false
  × disclosureObserver anonymousDonorDisclosableCarrier ≡ true
sameP8810DifferentDisclosure = refl , (refl , refl)

record ParentObserverDynamicsBoundary : Set where
  constructor parentObserverDynamicsBoundary
  field
    wikidataSlotStrictlyRefinedByGenetics : Bool
    wikidataSlotStrictlyRefinedByGeneticsIsTrue :
      wikidataSlotStrictlyRefinedByGenetics ≡ true
    geneticObserverStillNotSeparating : Bool
    geneticObserverStillNotSeparatingIsTrue :
      geneticObserverStillNotSeparating ≡ true
    legalTransitionCanRemainInsideP8810Fibre : Bool
    legalTransitionCanRemainInsideP8810FibreIsTrue :
      legalTransitionCanRemainInsideP8810Fibre ≡ true
    disclosureCanVaryInsideP8810Fibre : Bool
    disclosureCanVaryInsideP8810FibreIsTrue :
      disclosureCanVaryInsideP8810Fibre ≡ true

canonicalParentObserverDynamicsBoundary : ParentObserverDynamicsBoundary
canonicalParentObserverDynamicsBoundary =
  parentObserverDynamicsBoundary true refl true refl true refl true refl
