module DASHI.ComputerScience.GodelPrimitiveRecursiveRepresentabilityBridgeExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.GodelDiagonalProvabilityContractExact as Godel

------------------------------------------------------------------------
-- AUTHORITY-INDEXED PRIMITIVE RECURSIVENESS
--
-- Primitive-recursive status is not a user-constructible wrapper around an
-- arbitrary `Certificate : Set`.  A named authority owns the predicate on
-- functions, and every downstream theorem must use that SAME predicate.
------------------------------------------------------------------------

record PrimitiveRecursiveTheory : Set₂ where
  constructor primitiveRecursiveTheory
  field
    PrimitiveRecursiveUnary : (Nat → Nat) → Set

open PrimitiveRecursiveTheory public

record PrimitiveRecursiveExtensionalityAuthority
    (PRT : PrimitiveRecursiveTheory) : Set₁ where
  constructor primitiveRecursiveExtensionalityAuthority
  field
    transportAlongPointwiseEquality :
      (f g : Nat → Nat) →
      ((n : Nat) → f n ≡ g n) →
      PrimitiveRecursiveUnary PRT f →
      PrimitiveRecursiveUnary PRT g

open PrimitiveRecursiveExtensionalityAuthority public

record StrongUnaryGraphRepresentation
    (F : Godel.ArithmetisedFormalSystem)
    (f : Nat → Nat) : Set₁ where
  constructor strongUnaryGraphRepresentation
  field
    graphFormula : Godel.BinaryFormula F
    positiveInstance :
      (x : Nat) →
      Godel.Provable F
        (Godel.instantiate2 F graphFormula
          (Godel.numeral F x)
          (Godel.numeral F (f x)))
    negativeInstance :
      (x y : Nat) →
      (f x ≡ y → ⊥) →
      Godel.Provable F
        (Godel.Negation F
          (Godel.instantiate2 F graphFormula
            (Godel.numeral F x)
            (Godel.numeral F y)))

open StrongUnaryGraphRepresentation public

record PrimitiveRecursiveRepresentabilityAuthority
    (F : Godel.ArithmetisedFormalSystem)
    (PRT : PrimitiveRecursiveTheory) : Set₁ where
  constructor primitiveRecursiveRepresentabilityAuthority
  field
    representPrimitiveRecursiveUnary :
      (f : Nat → Nat) →
      PrimitiveRecursiveUnary PRT f →
      StrongUnaryGraphRepresentation F f

open PrimitiveRecursiveRepresentabilityAuthority public

------------------------------------------------------------------------
-- Object-language closure needed to compose A(y) with represented y=f(x).
------------------------------------------------------------------------

record RepresentedFunctionPrecomposition
    (F : Godel.ArithmetisedFormalSystem) : Set₁ where
  constructor representedFunctionPrecomposition
  field
    precompose :
      (predicate : Godel.Formula F) →
      (f : Nat → Nat) →
      StrongUnaryGraphRepresentation F f →
      Godel.Formula F

    precomposeLaw :
      (predicate : Godel.Formula F) →
      (f : Nat → Nat) →
      (representation : StrongUnaryGraphRepresentation F f) →
      (x : Nat) →
      Godel.Provable F
        (Godel.Biconditional F
          (Godel.instantiate F
            (precompose predicate f representation)
            (Godel.numeral F x))
          (Godel.instantiate F predicate
            (Godel.numeral F (f x))))

open RepresentedFunctionPrecomposition public

------------------------------------------------------------------------
-- Local producer: self-substitution code is primitive recursive under the
-- SAME PR authority consumed by representability.
------------------------------------------------------------------------

selfSubstitute :
  (F : Godel.ArithmetisedFormalSystem) →
  Godel.ArithmetisedSubstitution F →
  Nat → Nat
selfSubstitute F S x = Godel.substituteCode S x x

record SelfSubstitutionPrimitiveRecursive
    (F : Godel.ArithmetisedFormalSystem)
    (S : Godel.ArithmetisedSubstitution F)
    (PRT : PrimitiveRecursiveTheory) : Set₁ where
  constructor selfSubstitutionPrimitiveRecursive
  field
    primitiveRecursiveSelfSubstitution :
      PrimitiveRecursiveUnary PRT (selfSubstitute F S)

open SelfSubstitutionPrimitiveRecursive public

------------------------------------------------------------------------
-- Generic compiler to the existing diagonal ABI.
------------------------------------------------------------------------

compileDiagonalConstructionFromPrimitiveRecursiveRepresentation :
  (F : Godel.ArithmetisedFormalSystem) →
  (S : Godel.ArithmetisedSubstitution F) →
  (PRT : PrimitiveRecursiveTheory) →
  SelfSubstitutionPrimitiveRecursive F S PRT →
  PrimitiveRecursiveRepresentabilityAuthority F PRT →
  RepresentedFunctionPrecomposition F →
  Godel.DiagonalFormulaConstruction F S
compileDiagonalConstructionFromPrimitiveRecursiveRepresentation
  F S PRT selfPR authority closure =
  record
    { diagonalise = λ predicate →
        let f = selfSubstitute F S
            representation =
              representPrimitiveRecursiveUnary authority f
                (primitiveRecursiveSelfSubstitution selfPR)
        in precompose closure predicate f representation
    ; diagonaliseRepresentsSelfSubstitution = λ predicate →
        let f = selfSubstitute F S
            representation =
              representPrimitiveRecursiveUnary authority f
                (primitiveRecursiveSelfSubstitution selfPR)
            D = precompose closure predicate f representation
            x = Godel.codeFormula F D
        in precomposeLaw closure predicate f representation x
    }

compileDiagonalLemmaFromPrimitiveRecursiveRepresentation :
  (F : Godel.ArithmetisedFormalSystem) →
  (S : Godel.ArithmetisedSubstitution F) →
  (PRT : PrimitiveRecursiveTheory) →
  SelfSubstitutionPrimitiveRecursive F S PRT →
  PrimitiveRecursiveRepresentabilityAuthority F PRT →
  RepresentedFunctionPrecomposition F →
  Godel.DiagonalLemmaAuthority F
compileDiagonalLemmaFromPrimitiveRecursiveRepresentation
  F S PRT selfPR authority closure =
  Godel.diagonalLemmaFromConstruction F S
    (compileDiagonalConstructionFromPrimitiveRecursiveRepresentation
      F S PRT selfPR authority closure)

------------------------------------------------------------------------
-- Firewalls / exact frontier.
------------------------------------------------------------------------

data ArbitraryCertificateImpliesPrimitiveRecursive : Set where
data MetaLevelComputableImpliesObjectLanguageRepresentable : Set where
data PrimitiveRecursiveStatusAloneImpliesDiagonalLemma : Set where
data RepresentationAuthorityAloneSuppliesPrecomposition : Set where

data DifferentPrimitiveRecursiveAuthoritiesAreInterchangeable : Set where

arbitraryCertificateDoesNotCreatePRStatus :
  ArbitraryCertificateImpliesPrimitiveRecursive → ⊥
arbitraryCertificateDoesNotCreatePRStatus ()

metaComputabilityDoesNotSupplyRepresentability :
  MetaLevelComputableImpliesObjectLanguageRepresentable → ⊥
metaComputabilityDoesNotSupplyRepresentability ()

primitiveRecursiveStatusAloneDoesNotSupplyDiagonal :
  PrimitiveRecursiveStatusAloneImpliesDiagonalLemma → ⊥
primitiveRecursiveStatusAloneDoesNotSupplyDiagonal ()

representabilityDoesNotSilentlySupplyLogicalClosure :
  RepresentationAuthorityAloneSuppliesPrecomposition → ⊥
representabilityDoesNotSilentlySupplyLogicalClosure ()

prAuthoritiesDoNotSilentlyCoerce :
  DifferentPrimitiveRecursiveAuthoritiesAreInterchangeable → ⊥
prAuthoritiesDoNotSilentlyCoerce ()

record GodelPrimitiveRecursiveRepresentabilityBoundary : Set where
  constructor godelPrimitiveRecursiveRepresentabilityBoundary
  field
    authorityIndexedPrimitiveRecursivePredicateOwned : Bool
    primitiveRecursiveRepresentabilityContractOwned : Bool
    representedFunctionPrecompositionContractOwned : Bool
    selfSubstitutionPrimitiveRecursiveProducerOwned : Bool
    genericDiagonalCompilerFromTheseCoordinatesOwned : Bool
    arbitraryCertificateAcceptedAsPRStatus : Bool
    metaComputabilityPromotedToRepresentability : Bool
    diagonalLemmaCertifiedForConcreteArithmetic : Bool

canonicalGodelPrimitiveRecursiveRepresentabilityBoundary :
  GodelPrimitiveRecursiveRepresentabilityBoundary
canonicalGodelPrimitiveRecursiveRepresentabilityBoundary =
  godelPrimitiveRecursiveRepresentabilityBoundary
    true true true false true false false false
