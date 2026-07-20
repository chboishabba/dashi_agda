module Ontology.DNA.ChemistryPhaseTetrationBoundary where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import Ontology.DNA.ChemistrySheetHamiltonian using (Signed; neg; zer; pos)
open import Ontology.DNA.ChemistrySheetTowerBoundary using
  (CarrierGrowthLaw; fixedFourWayNesting; tetrationalComposition)

------------------------------------------------------------------------
-- Concrete involutive operator on the signed chemistry carrier.

flipSigned : Signed → Signed
flipSigned neg = pos
flipSigned zer = zer
flipSigned pos = neg

flipSigned-involutive : ∀ s → flipSigned (flipSigned s) ≡ s
flipSigned-involutive neg = refl
flipSigned-involutive zer = refl
flipSigned-involutive pos = refl

neutral-fixed : flipSigned zer ≡ zer
neutral-fixed = refl

data PhaseSector : Set where
  fixedNeutral pairedNegative pairedPositive : PhaseSector

phaseSector : Signed → PhaseSector
phaseSector neg = pairedNegative
phaseSector zer = fixedNeutral
phaseSector pos = pairedPositive

record ContextIndexedOperator : Set₁ where
  field
    Context : Set
    State : Set
    apply : Context → State → State
    invariant : Context → State → Set
    lowAction : Context → State → Set
    violation : Context → State → Set

record EigenclassPromotion (operator : ContextIndexedOperator) : Set₁ where
  open ContextIndexedOperator operator
  field
    Eigenvalue : Set
    eigenvalue : Context → State → Eigenvalue
    eigenLaw : Context → State → Set
    reverseComplementSector : Context → State → PhaseSector

------------------------------------------------------------------------
-- Tetration belongs to recursively nested transform/context capacity, not to
-- the finite physical DNA carrier merely because that carrier has four-way
-- nesting.

data TransformContext (A : Set) : Nat → Set where
  atom : A → TransformContext A zero
  nest : ∀ {n} → (TransformContext A n → TransformContext A n) →
    TransformContext A (suc n)

record TetrationalContextSemantics : Set₁ where
  field
    Atom : Set
    context : Nat → Set
    next : ∀ {n} → context n → context (suc n)
    nestedTransformMeaning : Set
    cardinalGrowthTheorem : Set

physicalDNAGrowthLaw : CarrierGrowthLaw
physicalDNAGrowthLaw = fixedFourWayNesting

physicalDNAIsNotPromotedToTetration : physicalDNAGrowthLaw ≡ fixedFourWayNesting
physicalDNAIsNotPromotedToTetration = refl

record TetrationPromotion : Set₁ where
  field
    semantics : TetrationalContextSemantics
    promotedGrowthLaw : CarrierGrowthLaw
    promotedGrowthLaw-is-tetrational :
      promotedGrowthLaw ≡ tetrationalComposition
