module DASHI.ComputerScience.GodelPrimitiveRecursiveRepresentabilityBridgeExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.GodelDiagonalProvabilityContractExact as Godel

------------------------------------------------------------------------
-- PRIMITIVE-RECURSIVE REPRESENTABILITY -> DIAGONAL CONSTRUCTION
--
-- This module does NOT prove Gödel's representability theorem.  It isolates
-- the exact theorem authority and the local producer needed by the already
-- owned diagonal compiler.
------------------------------------------------------------------------

record PrimitiveRecursiveUnary (f : Nat → Nat) : Set₁ where
  constructor primitiveRecursiveUnary
  field
    Certificate : Set
    certificate : Certificate

open PrimitiveRecursiveUnary public

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
    (F : Godel.ArithmetisedFormalSystem) : Set₁ where
  constructor primitiveRecursiveRepresentabilityAuthority
  field
    representPrimitiveRecursiveUnary :
      (f : Nat → Nat) →
      PrimitiveRecursiveUnary f →
      StrongUnaryGraphRepresentation F f

open PrimitiveRecursiveRepresentabilityAuthority public

------------------------------------------------------------------------
-- Object-language closure needed to compose a unary predicate A(y) with a
-- represented function y = f(x).  In an ordinary arithmetic development this
-- is discharged by the usual existential/equality construction.  Keeping it
-- explicit prevents meta-level function composition from being promoted into
-- an object-language proof.
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
-- Local producer: self-substitution code is primitive recursive.
------------------------------------------------------------------------

selfSubstitute :
  (F : Godel.ArithmetisedFormalSystem) →
  Godel.ArithmetisedSubstitution F →
  Nat → Nat
selfSubstitute F S x = Godel.substituteCode S x x

record SelfSubstitutionPrimitiveRecursive
    (F : Godel.ArithmetisedFormalSystem)
    (S : Godel.ArithmetisedSubstitution F) : Set₁ where
  constructor selfSubstitutionPrimitiveRecursive
  field
    primitiveRecursiveSelfSubstitution :
      PrimitiveRecursiveUnary (selfSubstitute F S)

open SelfSubstitutionPrimitiveRecursive public

------------------------------------------------------------------------
-- Generic compiler to the existing diagonal ABI.
------------------------------------------------------------------------

compileDiagonalConstructionFromPrimitiveRecursiveRepresentation :
  (F : Godel.ArithmetisedFormalSystem) →
  (S : Godel.ArithmetisedSubstitution F) →
  SelfSubstitutionPrimitiveRecursive F S →
  PrimitiveRecursiveRepresentabilityAuthority F →
  RepresentedFunctionPrecomposition F →
  Godel.DiagonalFormulaConstruction F S
compileDiagonalConstructionFromPrimitiveRecursiveRepresentation
  F S selfPR authority closure =
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
  SelfSubstitutionPrimitiveRecursive F S →
  PrimitiveRecursiveRepresentabilityAuthority F →
  RepresentedFunctionPrecomposition F →
  Godel.DiagonalLemmaAuthority F
compileDiagonalLemmaFromPrimitiveRecursiveRepresentation F S selfPR authority closure =
  Godel.diagonalLemmaFromConstruction F S
    (compileDiagonalConstructionFromPrimitiveRecursiveRepresentation
      F S selfPR authority closure)

------------------------------------------------------------------------
-- Firewalls / exact frontier.
------------------------------------------------------------------------

data MetaLevelComputableImpliesObjectLanguageRepresentable : Set where
data PrimitiveRecursiveCertificateAloneImpliesDiagonalLemma : Set where
data RepresentationAuthorityAloneSuppliesPrecomposition : Set where

metaComputabilityDoesNotSupplyRepresentability :
  MetaLevelComputableImpliesObjectLanguageRepresentable → ⊥
metaComputabilityDoesNotSupplyRepresentability ()

primitiveRecursiveCertificateAloneDoesNotSupplyDiagonal :
  PrimitiveRecursiveCertificateAloneImpliesDiagonalLemma → ⊥
primitiveRecursiveCertificateAloneDoesNotSupplyDiagonal ()

representabilityDoesNotSilentlySupplyLogicalClosure :
  RepresentationAuthorityAloneSuppliesPrecomposition → ⊥
representabilityDoesNotSilentlySupplyLogicalClosure ()

record GodelPrimitiveRecursiveRepresentabilityBoundary : Set where
  constructor godelPrimitiveRecursiveRepresentabilityBoundary
  field
    primitiveRecursiveRepresentabilityContractOwned : Bool
    representedFunctionPrecompositionContractOwned : Bool
    selfSubstitutionPrimitiveRecursiveProducerOwned : Bool
    genericDiagonalCompilerFromTheseCoordinatesOwned : Bool
    metaComputabilityPromotedToRepresentability : Bool
    diagonalLemmaCertifiedForConcreteArithmetic : Bool

canonicalGodelPrimitiveRecursiveRepresentabilityBoundary :
  GodelPrimitiveRecursiveRepresentabilityBoundary
canonicalGodelPrimitiveRecursiveRepresentabilityBoundary =
  godelPrimitiveRecursiveRepresentabilityBoundary
    true true false true false false
