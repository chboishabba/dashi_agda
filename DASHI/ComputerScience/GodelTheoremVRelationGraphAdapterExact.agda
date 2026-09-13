module DASHI.ComputerScience.GodelTheoremVRelationGraphAdapterExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.GodelDiagonalProvabilityContractExact as Godel
import DASHI.ComputerScience.GodelPrimitiveRecursiveRepresentabilityBridgeExact as PR

------------------------------------------------------------------------
-- GÖDEL THEOREM V IN A RELATION-NATIVE SHAPE
--
-- The historical theorem is naturally stated for primitive-recursive
-- relations.  A unary function f is represented through its graph relation
-- Graph_f(x,y) := f(x)=y.  This adapter prevents the source theorem from being
-- silently strengthened into a function-specific representation theorem.
------------------------------------------------------------------------

record PrimitiveRecursiveBinaryRelationTheory : Set₁ where
  constructor primitiveRecursiveBinaryRelationTheory
  field
    PrimitiveRecursiveBinaryRelation :
      (Nat → Nat → Set) → Set

open PrimitiveRecursiveBinaryRelationTheory public

record NumeralwiseBinaryRelationRepresentation
    (F : Godel.ArithmetisedFormalSystem)
    (R : Nat → Nat → Set) : Set₁ where
  constructor numeralwiseBinaryRelationRepresentation
  field
    relationFormula : Godel.BinaryFormula F

    positiveInstance :
      (x y : Nat) →
      R x y →
      Godel.Provable F
        (Godel.instantiate2 F relationFormula
          (Godel.numeral F x)
          (Godel.numeral F y))

    negativeInstance :
      (x y : Nat) →
      (R x y → ⊥) →
      Godel.Provable F
        (Godel.Negation F
          (Godel.instantiate2 F relationFormula
            (Godel.numeral F x)
            (Godel.numeral F y)))

open NumeralwiseBinaryRelationRepresentation public

record GodelTheoremVAuthority
    (F : Godel.ArithmetisedFormalSystem)
    (RT : PrimitiveRecursiveBinaryRelationTheory) : Set₁ where
  constructor godelTheoremVAuthority
  field
    representPrimitiveRecursiveRelation :
      (R : Nat → Nat → Set) →
      PrimitiveRecursiveBinaryRelation RT R →
      NumeralwiseBinaryRelationRepresentation F R

open GodelTheoremVAuthority public

------------------------------------------------------------------------
-- Function graph closure under the SAME PR theories.
------------------------------------------------------------------------

Graph : (Nat → Nat) → Nat → Nat → Set
Graph f x y = f x ≡ y

record PrimitiveRecursiveFunctionGraphAuthority
    (FT : PR.PrimitiveRecursiveTheory)
    (RT : PrimitiveRecursiveBinaryRelationTheory) : Set₁ where
  constructor primitiveRecursiveFunctionGraphAuthority
  field
    graphIsPrimitiveRecursive :
      (f : Nat → Nat) →
      PR.PrimitiveRecursiveUnary FT f →
      PrimitiveRecursiveBinaryRelation RT (Graph f)

open PrimitiveRecursiveFunctionGraphAuthority public

------------------------------------------------------------------------
-- Exact adapter to the function-graph consumer used by the diagonal compiler.
------------------------------------------------------------------------

relationGraphCompilesStrongUnaryRepresentation :
  (F : Godel.ArithmetisedFormalSystem) →
  (FT : PR.PrimitiveRecursiveTheory) →
  (RT : PrimitiveRecursiveBinaryRelationTheory) →
  GodelTheoremVAuthority F RT →
  PrimitiveRecursiveFunctionGraphAuthority FT RT →
  PR.PrimitiveRecursiveRepresentabilityAuthority F FT
relationGraphCompilesStrongUnaryRepresentation F FT RT theoremV graphClosure =
  PR.primitiveRecursiveRepresentabilityAuthority
    (λ f fPR →
      let relationPR = graphIsPrimitiveRecursive graphClosure f fPR
          represented =
            representPrimitiveRecursiveRelation theoremV (Graph f) relationPR
      in PR.strongUnaryGraphRepresentation
          (relationFormula represented)
          (λ x → positiveInstance represented x (f x) refl)
          (λ x y notEqual →
            negativeInstance represented x y notEqual))

------------------------------------------------------------------------
-- Source-alignment gain: Theorem V now only has to align to relation
-- representability.  Function graph closure is a separate closure theorem.
------------------------------------------------------------------------

data RelationRepresentabilitySilentlyIncludesGraphClosure : Set where
data FunctionGraphClosureSilentlyChangesPRAuthority : Set where

theoremVDoesNotSilentlySupplyGraphClosure :
  RelationRepresentabilitySilentlyIncludesGraphClosure → ⊥
theoremVDoesNotSilentlySupplyGraphClosure ()

graphClosureDoesNotChangeAuthority :
  FunctionGraphClosureSilentlyChangesPRAuthority → ⊥
graphClosureDoesNotChangeAuthority ()

record GodelTheoremVRelationGraphBoundary : Set where
  constructor godelTheoremVRelationGraphBoundary
  field
    theoremVRelationNativeContractOwned : Bool
    functionGraphClosureSeparated : Bool
    relationToStrongFunctionGraphCompilerOwned : Bool
    theoremVSourceAlignedExactly : Bool
    functionGraphClosureCertified : Bool

canonicalGodelTheoremVRelationGraphBoundary :
  GodelTheoremVRelationGraphBoundary
canonicalGodelTheoremVRelationGraphBoundary =
  godelTheoremVRelationGraphBoundary true true true false false
