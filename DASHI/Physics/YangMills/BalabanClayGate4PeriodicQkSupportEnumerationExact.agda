module DASHI.Physics.YangMills.BalabanClayGate4PeriodicQkSupportEnumerationExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (Dec; yes; no; _∈_; here; there; FiniteEnumeration; elements;
    complete; productFinite; periodicTorus4Finite; cyclicIndexFinite;
    PositiveBond; four)

------------------------------------------------------------------------
-- Exact finite support enumeration on the repository's periodic bond carrier.
--
-- For the selected Bałaban derivative kernel the intended relation is
--
--   Support c b  iff  b belongs to B^k(c_-) union B^k(c_+).
--
-- This module does not guess that geometric predicate.  Given any decidable
-- support relation, it constructs the literal row-support and dual column-
-- incidence lists from the complete periodic bond enumerations and proves both
-- lists sound and complete.  Their lengths are therefore exact finite counts.
------------------------------------------------------------------------

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
      (there membership) → filterDecSound decide membership
... | no candidateRefutation = λ membership →
      filterDecSound decide membership

filterDecComplete :
  ∀ {A : Set} {Predicate : A → Set}
    (decide : (value : A) → Dec (Predicate value))
    {value : A} {values : List A} →
  value ∈ values → Predicate value →
  value ∈ filterDec Predicate decide values
filterDecComplete decide {values = []} () proof
filterDecComplete {Predicate = Predicate} decide
  {value = value} {values = candidate ∷ values}
  membership proof with decide candidate
... | yes candidateProof with membership
...   | here = here
...   | there rest = there (filterDecComplete decide rest proof)
... | no candidateRefutation with membership
...   | here = candidateRefutation proof
...   | there rest = filterDecComplete decide rest proof

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
rowSupportSound dataSet coarse fine =
  filterDecSound (supportDecidable dataSet coarse)

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
columnIncidenceSound dataSet fine coarse =
  filterDecSound (λ candidate → supportDecidable dataSet candidate fine)

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

periodicQkRowSupportEnumerationLevel : ProofLevel
periodicQkRowSupportEnumerationLevel = machineChecked

periodicQkColumnIncidenceEnumerationLevel : ProofLevel
periodicQkColumnIncidenceEnumerationLevel = machineChecked

periodicQkExactFiniteCountDefinitionLevel : ProofLevel
periodicQkExactFiniteCountDefinitionLevel = computed

physicalQkEndpointBlockUnionPredicateInputsLevel : ProofLevel
physicalQkEndpointBlockUnionPredicateInputsLevel = conditional

physicalQkUniformRowCountBoundInputsLevel : ProofLevel
physicalQkUniformRowCountBoundInputsLevel = conditional

physicalQkUniformColumnCountBoundInputsLevel : ProofLevel
physicalQkUniformColumnCountBoundInputsLevel = conditional
