module DASHI.Ontology.ProgenitorParentPredicatePullbackExact where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Ontology.ProgenitorParentHyperfabric
open import DASHI.Ontology.ProgenitorParentProjectionFibre
open import DASHI.Ontology.ProgenitorParentPNFPullbackLattice
open import DASHI.Ontology.ProgenitorParentPredicateBaseChange

------------------------------------------------------------------------
-- Exact predicate pullback.
--
-- A meet fibre is not only mapped to its two factors: it is exactly the data of
-- one slot-compatible hidden carrier together with both predicate witnesses.
------------------------------------------------------------------------

record PredicatePullbackPair
    (slot : WikidataParentSlot)
    (p q : ParentPredicate) : Set where
  constructor predicatePullbackPair
  field
    pullbackCarrier : ParentCarrier
    pullbackSlot : projectParentSlot pullbackCarrier ≡ slot
    leftPredicateWitness : p pullbackCarrier ≡ true
    rightPredicateWitness : q pullbackCarrier ≡ true
open PredicatePullbackPair public

meetFibreToPullbackPair :
  {slot : WikidataParentSlot} {p q : ParentPredicate} →
  ParentPredicateFibre slot (p ⊓p q) →
  PredicatePullbackPair slot p q
meetFibreToPullbackPair {p = p} {q = q} point =
  predicatePullbackPair
    (predicateCarrier point)
    (slotWitness point)
    (meetRefinesLeft p q (predicateCarrier point) (predicateWitness point))
    (meetRefinesRight p q (predicateCarrier point) (predicateWitness point))

pullbackPairToMeetFibre :
  {slot : WikidataParentSlot} {p q : ParentPredicate} →
  PredicatePullbackPair slot p q →
  ParentPredicateFibre slot (p ⊓p q)
pullbackPairToMeetFibre pair
  rewrite leftPredicateWitness pair | rightPredicateWitness pair =
  parentPredicateFibre (pullbackCarrier pair) (pullbackSlot pair) refl

meetPullbackCarrierRoundTrip :
  {slot : WikidataParentSlot} {p q : ParentPredicate} →
  (point : ParentPredicateFibre slot (p ⊓p q)) →
  predicateCarrier (pullbackPairToMeetFibre (meetFibreToPullbackPair point))
  ≡ predicateCarrier point
meetPullbackCarrierRoundTrip point = refl

pullbackMeetCarrierRoundTrip :
  {slot : WikidataParentSlot} {p q : ParentPredicate} →
  (pair : PredicatePullbackPair slot p q) →
  pullbackCarrier (meetFibreToPullbackPair (pullbackPairToMeetFibre pair))
  ≡ pullbackCarrier pair
pullbackMeetCarrierRoundTrip pair
  rewrite leftPredicateWitness pair | rightPredicateWitness pair = refl

------------------------------------------------------------------------
-- Concrete parent example: ordinary genetic+genealogical parenthood is the
-- intersection fibre, while donor and adoptive witnesses occupy only one side.
------------------------------------------------------------------------

geneticParentPullbackPair :
  PredicatePullbackPair parentP8810 geneticP genealogicalParentP
geneticParentPullbackPair = meetFibreToPullbackPair geneticAndParentP8810

geneticParentPullbackHasGeneticWitness :
  geneticP (pullbackCarrier geneticParentPullbackPair) ≡ true
geneticParentPullbackHasGeneticWitness = leftPredicateWitness geneticParentPullbackPair

geneticParentPullbackHasParentWitness :
  genealogicalParentP (pullbackCarrier geneticParentPullbackPair) ≡ true
geneticParentPullbackHasParentWitness = rightPredicateWitness geneticParentPullbackPair
