module DASHI.Ontology.ProgenitorParentPredicateBaseChange where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Ontology.ProgenitorParentHyperfabric
open import DASHI.Ontology.ProgenitorParentProjectionFibre
open import DASHI.Ontology.ProgenitorParentPNFPullbackLattice
open import DASHI.Ontology.LeanWikidataParentingPullbackBridge

------------------------------------------------------------------------
-- Predicate order and base change.
--
-- p ⊑ q means every carrier selected by p is also selected by q.  Pulling a
-- slot fibre back along a stronger predicate therefore maps canonically into the
-- fibre for the weaker predicate.  This is the concrete PNF/predicate analogue
-- of JMD's retract/pullback base-change theorem surface.
------------------------------------------------------------------------

PredicateRefines : ParentPredicate → ParentPredicate → Set
PredicateRefines p q =
  (carrier : ParentCarrier) → p carrier ≡ true → q carrier ≡ true

infix 4 _⊑p_
_⊑p_ : ParentPredicate → ParentPredicate → Set
_⊑p_ = PredicateRefines

predicateRefl : (p : ParentPredicate) → p ⊑p p
predicateRefl p carrier hp = hp

predicateTrans :
  {p q r : ParentPredicate} →
  p ⊑p q → q ⊑p r → p ⊑p r
predicateTrans pq qr carrier hp = qr carrier (pq carrier hp)

meetRefinesLeft : (p q : ParentPredicate) → (p ⊓p q) ⊑p p
meetRefinesLeft p q carrier h with p carrier | q carrier
... | true | true = refl
... | true | false = refl
... | false | true = refl
... | false | false = refl

meetRefinesRight : (p q : ParentPredicate) → (p ⊓p q) ⊑p q
meetRefinesRight p q carrier h with p carrier | q carrier
... | true | true = refl
... | true | false = refl
... | false | true = refl
... | false | false = refl

leftRefinesJoin : (p q : ParentPredicate) → p ⊑p (p ⊔p q)
leftRefinesJoin p q carrier h with p carrier | q carrier
... | true | true = refl
... | true | false = refl
... | false | true = refl
... | false | false = refl

rightRefinesJoin : (p q : ParentPredicate) → q ⊑p (p ⊔p q)
rightRefinesJoin p q carrier h with p carrier | q carrier
... | true | true = refl
... | true | false = refl
... | false | true = refl
... | false | false = refl

predicateBaseChange :
  {slot : WikidataParentSlot} {p q : ParentPredicate} →
  p ⊑p q →
  ParentPredicateFibre slot p →
  ParentPredicateFibre slot q
predicateBaseChange refinement point =
  parentPredicateFibre
    (predicateCarrier point)
    (slotWitness point)
    (refinement (predicateCarrier point) (predicateWitness point))

meetFibreToLeft :
  {slot : WikidataParentSlot} {p q : ParentPredicate} →
  ParentPredicateFibre slot (p ⊓p q) →
  ParentPredicateFibre slot p
meetFibreToLeft {p = p} {q = q} = predicateBaseChange (meetRefinesLeft p q)

meetFibreToRight :
  {slot : WikidataParentSlot} {p q : ParentPredicate} →
  ParentPredicateFibre slot (p ⊓p q) →
  ParentPredicateFibre slot q
meetFibreToRight {p = p} {q = q} = predicateBaseChange (meetRefinesRight p q)

leftFibreToJoin :
  {slot : WikidataParentSlot} {p q : ParentPredicate} →
  ParentPredicateFibre slot p →
  ParentPredicateFibre slot (p ⊔p q)
leftFibreToJoin {p = p} {q = q} = predicateBaseChange (leftRefinesJoin p q)

------------------------------------------------------------------------
-- Parent-specific base-change witnesses.
------------------------------------------------------------------------

recordedGeneticAndParentCarrier : ParentCarrier
recordedGeneticAndParentCarrier =
  parentCarrier individualLevel
    (relationVector true true true false false true true true true true true true)

geneticAndParentP8810 :
  ParentPredicateFibre parentP8810 geneticAndGenealogicalParentP
geneticAndParentP8810 =
  parentPredicateFibre recordedGeneticAndParentCarrier refl refl

geneticAndParentForgetsToGenetic :
  geneticP (predicateCarrier (meetFibreToLeft geneticAndParentP8810)) ≡ true
geneticAndParentForgetsToGenetic = refl

geneticAndParentForgetsToParent :
  genealogicalParentP (predicateCarrier (meetFibreToRight geneticAndParentP8810)) ≡ true
geneticAndParentForgetsToParent = refl

-- JMD supplies the general categorical result that retracts are stable under
-- base change.  The source contract is carried explicitly next to the concrete
-- predicate-base-change operation; it is not replaced by it.
record ParentBaseChangeBridge : Set where
  constructor parentBaseChangeBridge
  field
    jmdCategoricalBaseChange : LeanTheoremContract
    concretePredicateBaseChangeAvailable : ParentPredicateFibre parentP8810 geneticAndGenealogicalParentP
open ParentBaseChangeBridge public

canonicalParentBaseChangeBridge : ParentBaseChangeBridge
canonicalParentBaseChangeBridge =
  parentBaseChangeBridge jmdRetractsStableUnderBaseChange geneticAndParentP8810
