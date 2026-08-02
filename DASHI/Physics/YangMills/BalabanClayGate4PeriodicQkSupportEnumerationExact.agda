module DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkSupportEnumerationExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (Empty; Dec; yes; no; _∈_; here; there; FiniteEnumeration; elements;
    complete; productFinite; periodicTorus4Finite; cyclicIndexFinite;
    PositiveBond; four)

------------------------------------------------------------------------
-- Exact finite support enumeration on the repository's periodic bond carrier.
--
-- For the selected Bałaban derivative kernel the intended relation is
--
--   Support c b  iff  b belongs to B^k(c_-) union B^k(c_+).
--
-- This module does not guess that geometric predicate. Given any decidable
-- endpoint-block-union relation, it constructs the literal row-support and dual
-- column-incidence lists from the complete periodic bond enumerations and proves
-- both lists sound and complete. Their lengths are therefore exact finite
-- counts.
------------------------------------------------------------------------

emptyElim : ∀ {A : Set} → Empty → A
emptyElim ()

record Iff (left right : Set) : Set where
  constructor iff
  field
    forward : left → right
    backward : right → left

open Iff public

filterDec :
  ∀ {A : Set} (Predicate : A → Set) →
  ((value : A) → Dec (Predicate value)) →
  List A → List A
filterDec Predicate decide [] = []
filterDec Predicate decide (value ∷ values) with decide value
... | yes proof = value ∷ filterDec Predicate decide values
... | no refutation = filterDec Predicate decide values

filterDecSound :
  ∀ {A : Set} {Predicate : A → Set}
    (decide : (value : A) → Dec (Predicate value))
    {value : A} {values : List A} →
  value ∈ filterDec Predicate decide values →
  Predicate value
filterDecSound decide {values = []} ()
filterDecSound {Predicate = Predicate} decide
  {value = value} {values = candidate ∷ values}
  with decide candidate
... | yes candidateProof = λ where
      here → candidateProof
      (there membership) → filterDecSound {Predicate = Predicate} decide {values = values} membership
... | no candidateRefutation = λ membership →
      filterDecSound {Predicate = Predicate} decide {values = values} membership

filterDecComplete :
  ∀ {A : Set} {Predicate : A → Set}
    (decide : (value : A) → Dec (Predicate value))
    {value : A} {values : List A} →
  value ∈ values → Predicate value →
  value ∈ filterDec Predicate decide values
filterDecComplete decide {values = []} () proof
filterDecComplete {Predicate = Predicate} decide
  {value = value} {values = candidate ∷ values}
  membership proof with decide candidate | membership
... | yes candidateProof | here = here
... | yes candidateProof | there rest = there (filterDecComplete {Predicate = Predicate} decide {values = values} rest proof)
... | no candidateRefutation | here = emptyElim (candidateRefutation proof)
... | no candidateRefutation | there rest = filterDecComplete {Predicate = Predicate} decide {values = values} rest proof

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ values) = suc (listLength values)

positiveBondFinite : ∀ side → FiniteEnumeration (PositiveBond side)
positiveBondFinite side =
  productFinite (periodicTorus4Finite side) (cyclicIndexFinite four)

record FiniteKernelSupportRelation
    (CoarseBond FineBond : Set) : Set₁ where
  field
    coarseFinite : FiniteEnumeration CoarseBond
    fineFinite : FiniteEnumeration FineBond

    Support : CoarseBond → FineBond → Set
    supportDecidable : ∀ coarse fine → Dec (Support coarse fine)

open FiniteKernelSupportRelation public

rowSupport :
  ∀ {CoarseBond FineBond : Set} →
  FiniteKernelSupportRelation CoarseBond FineBond →
  CoarseBond → List FineBond
rowSupport dataSet coarse =
  filterDec
    (Support dataSet coarse)
    (supportDecidable dataSet coarse)
    (elements (fineFinite dataSet))

columnIncidence :
  ∀ {CoarseBond FineBond : Set} →
  FiniteKernelSupportRelation CoarseBond FineBond →
  FineBond → List CoarseBond
columnIncidence dataSet fine =
  filterDec
    (λ coarse → Support dataSet coarse fine)
    (λ coarse → supportDecidable dataSet coarse fine)
    (elements (coarseFinite dataSet))

rowSupportSound :
  ∀ {CoarseBond FineBond : Set}
    (dataSet : FiniteKernelSupportRelation CoarseBond FineBond)
    coarse fine →
  fine ∈ rowSupport dataSet coarse →
  Support dataSet coarse fine
rowSupportSound dataSet coarse fine membership =
  filterDecSound {Predicate = Support dataSet coarse}
    (supportDecidable dataSet coarse) {values = elements (fineFinite dataSet)}
    membership

rowSupportComplete :
  ∀ {CoarseBond FineBond : Set}
    (dataSet : FiniteKernelSupportRelation CoarseBond FineBond)
    coarse fine →
  Support dataSet coarse fine →
  fine ∈ rowSupport dataSet coarse
rowSupportComplete dataSet coarse fine support =
  filterDecComplete
    (supportDecidable dataSet coarse)
    (complete (fineFinite dataSet) fine)
    support

columnIncidenceSound :
  ∀ {CoarseBond FineBond : Set}
    (dataSet : FiniteKernelSupportRelation CoarseBond FineBond)
    fine coarse →
  coarse ∈ columnIncidence dataSet fine →
  Support dataSet coarse fine
columnIncidenceSound dataSet fine coarse membership =
  filterDecSound {Predicate = λ candidate → Support dataSet candidate fine}
    (λ candidate → supportDecidable dataSet candidate fine) {values = elements (coarseFinite dataSet)}
    membership

columnIncidenceComplete :
  ∀ {CoarseBond FineBond : Set}
    (dataSet : FiniteKernelSupportRelation CoarseBond FineBond)
    fine coarse →
  Support dataSet coarse fine →
  coarse ∈ columnIncidence dataSet fine
columnIncidenceComplete dataSet fine coarse support =
  filterDecComplete
    (λ candidate → supportDecidable dataSet candidate fine)
    (complete (coarseFinite dataSet) coarse)
    support

exactRowCount :
  ∀ {CoarseBond FineBond : Set} →
  FiniteKernelSupportRelation CoarseBond FineBond →
  CoarseBond → Nat
exactRowCount dataSet coarse = listLength (rowSupport dataSet coarse)

exactColumnCount :
  ∀ {CoarseBond FineBond : Set} →
  FiniteKernelSupportRelation CoarseBond FineBond →
  FineBond → Nat
exactColumnCount dataSet fine = listLength (columnIncidence dataSet fine)

record PeriodicQkSupportMeaning
    (fineSide coarseSide : Nat) : Set₁ where
  field
    supportRelation : FiniteKernelSupportRelation
      (PositiveBond coarseSide) (PositiveBond fineSide)

    EndpointBlockUnionSupport :
      PositiveBond coarseSide → PositiveBond fineSide → Set

    supportIsEndpointBlockUnion : ∀ coarse fine →
      Iff
        (Support supportRelation coarse fine)
        (EndpointBlockUnionSupport coarse fine)

open PeriodicQkSupportMeaning public

periodicSupportCarrier :
  ∀ {fineSide coarseSide}
    (meaning : PeriodicQkSupportMeaning fineSide coarseSide) →
  FiniteKernelSupportRelation
    (PositiveBond coarseSide) (PositiveBond fineSide)
periodicSupportCarrier = supportRelation

periodicSupportRelationFromEndpointPredicate :
  ∀ {fineSide coarseSide}
    (EndpointBlockUnionSupport :
      PositiveBond coarseSide → PositiveBond fineSide → Set) →
  (∀ coarse fine → Dec (EndpointBlockUnionSupport coarse fine)) →
  FiniteKernelSupportRelation
    (PositiveBond coarseSide) (PositiveBond fineSide)
periodicSupportRelationFromEndpointPredicate
    {fineSide = fineSide} {coarseSide = coarseSide}
    EndpointBlockUnionSupport decide = record
  { coarseFinite = positiveBondFinite coarseSide
  ; fineFinite = positiveBondFinite fineSide
  ; Support = EndpointBlockUnionSupport
  ; supportDecidable = decide
  }

periodicQkSupportMeaningFromEndpointPredicate :
  ∀ {fineSide coarseSide}
    (EndpointBlockUnionSupport :
      PositiveBond coarseSide → PositiveBond fineSide → Set)
    (decide : ∀ coarse fine →
      Dec (EndpointBlockUnionSupport coarse fine)) →
  PeriodicQkSupportMeaning fineSide coarseSide
periodicQkSupportMeaningFromEndpointPredicate
    EndpointBlockUnionSupport decide = record
  { supportRelation =
      periodicSupportRelationFromEndpointPredicate
        EndpointBlockUnionSupport decide
  ; EndpointBlockUnionSupport = EndpointBlockUnionSupport
  ; supportIsEndpointBlockUnion = λ coarse fine →
      iff (λ support → support) (λ support → support)
  }

periodicQkRowSupportEnumerationLevel : ProofLevel
periodicQkRowSupportEnumerationLevel = machineChecked

periodicQkColumnIncidenceEnumerationLevel : ProofLevel
periodicQkColumnIncidenceEnumerationLevel = machineChecked

periodicQkExactFiniteCountDefinitionLevel : ProofLevel
periodicQkExactFiniteCountDefinitionLevel = computed

periodicQkSupportFromEndpointPredicateLevel : ProofLevel
periodicQkSupportFromEndpointPredicateLevel = machineChecked

physicalQkEndpointBlockUnionPredicateInputsLevel : ProofLevel
physicalQkEndpointBlockUnionPredicateInputsLevel = conditional
