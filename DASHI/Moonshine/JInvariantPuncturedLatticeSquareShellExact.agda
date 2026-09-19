module DASHI.Moonshine.JInvariantPuncturedLatticeSquareShellExact where

------------------------------------------------------------------------
-- FINITE SQUARE-SHELL COVER FOR Z^2
--
-- For convergence we only need an O(r^2) cover of the max-norm shell, not the
-- sharper exact 8r boundary count.  The existing signed coordinate decoder
-- enumerates [-R,R] by Fin(2R+1).  Taking its finite product therefore gives
-- exactly (2R+1)^2 codes and a complete cover of every lattice point in the
-- square.
--
-- The radius-(R+1) shell is represented computationally as points in the
-- outer square but not the radius-R inner square.  Filtering can only reduce
-- cardinality, so this is sufficient for the k=4 Basel majorant.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Bool.Base using (T; _∧_; not)
open import Data.Bool.Properties using (T-∧)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using
  (List; []; _∷_; allFin; cartesianProductWith; filterᵇ; map)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Product using (Σ; _×_; _,_)
open import Function.Base using (_∘_)
open import Function.Bundles using (Equivalence)
open import Relation.Nullary.Decidable.Core using (T?)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Mathematics.NumberTheory.FiniteDependentPairCardinalityExact as Card
import DASHI.Mathematics.NumberTheory.FiniteProductCardinalityExact as ProductCard
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as Cutoff
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Lattice

SquareCode : Nat → Set
SquareCode radius =
  Fin (Cube.coordinateCodeBound radius)
  × Fin (Cube.coordinateCodeBound radius)

decodeSquareCode :
  (radius : Nat) →
  SquareCode radius →
  Lattice.LatticePoint
decodeSquareCode radius (i , j) =
  Lattice.lattice-point
    (Cube.decodeCoordinate radius i)
    (Cube.decodeCoordinate radius j)

squareCodes : (radius : Nat) → List (SquareCode radius)
squareCodes radius =
  cartesianProductWith _,_
    (allFin (Cube.coordinateCodeBound radius))
    (allFin (Cube.coordinateCodeBound radius))

pairConstructorInjective :
  {A B : Set} → {a b : A} → {x y : B} →
  (a , x) ≡ (b , y) → (a ≡ b) × (x ≡ y)
pairConstructorInjective refl = refl , refl

squareCodesUnique :
  (radius : Nat) →
  Unique (squareCodes radius)
squareCodesUnique radius =
  UniqueP.cartesianProductWith⁺ _,_ pairConstructorInjective
    (UniqueP.allFin⁺ (Cube.coordinateCodeBound radius))
    (UniqueP.allFin⁺ (Cube.coordinateCodeBound radius))

decodeSquareCodeInjective :
  (radius : Nat) →
  {left right : SquareCode radius} →
  decodeSquareCode radius left ≡ decodeSquareCode radius right →
  left ≡ right
decodeSquareCodeInjective radius {i , j} {i′ , j′} equality =
  cong₂ _,_
    (Cube.decodeCoordinateInjective radius
      (cong Lattice.horizontal equality))
    (Cube.decodeCoordinateInjective radius
      (cong Lattice.vertical equality))

squarePoints :
  (radius : Nat) →
  List Lattice.LatticePoint
squarePoints radius =
  map (decodeSquareCode radius) (squareCodes radius)

squarePointsUnique :
  (radius : Nat) →
  Unique (squarePoints radius)
squarePointsUnique radius =
  UniqueP.map⁺
    (decodeSquareCodeInjective radius)
    (squareCodesUnique radius)

squareCodeCount :
  Nat → Nat
squareCodeCount radius =
  Cube.coordinateCodeBound radius
  * Cube.coordinateCodeBound radius

squareCodesLength :
  (radius : Nat) →
  Reindex.listLength (squareCodes radius)
  ≡ squareCodeCount radius
squareCodesLength radius =
  trans
    (ProductCard.cartesianProductWithLength _,_
      (allFin (Cube.coordinateCodeBound radius))
      (allFin (Cube.coordinateCodeBound radius)))
    (cong₂ _*_
      (ProductCard.stdlibAllFinLength
        (Cube.coordinateCodeBound radius))
      (ProductCard.stdlibAllFinLength
        (Cube.coordinateCodeBound radius)))

squarePointsLength :
  (radius : Nat) →
  Reindex.listLength (squarePoints radius)
  ≡ squareCodeCount radius
squarePointsLength radius =
  trans
    (Card.mapLength
      (decodeSquareCode radius)
      (squareCodes radius))
    (squareCodesLength radius)

insideSquare? :
  Nat →
  Lattice.LatticePoint →
  Bool
insideSquare? radius point =
  Cutoff.coordinateInCutoff? radius (Lattice.horizontal point)
  ∧
  Cutoff.coordinateInCutoff? radius (Lattice.vertical point)

onSuccessorSquareShell? :
  Nat →
  Lattice.LatticePoint →
  Bool
onSuccessorSquareShell? inner point =
  insideSquare? (suc inner) point
  ∧ not (insideSquare? inner point)

successorSquareShell :
  Nat →
  List Lattice.LatticePoint
successorSquareShell inner =
  filterᵇ (onSuccessorSquareShell? inner)
    (squarePoints (suc inner))

successorSquareShellUnique :
  (inner : Nat) →
  Unique (successorSquareShell inner)
successorSquareShellUnique inner =
  UniqueP.filter⁺
    (T? ∘ onSuccessorSquareShell? inner)
    (squarePointsUnique (suc inner))

weakenRight :
  ∀ {left right : Nat} →
  left ≤ right →
  left ≤ suc right
weakenRight z≤n = z≤n
weakenRight (s≤s proof) =
  s≤s (weakenRight proof)

filterLengthAtMost :
  ∀ {A : Set}
    (predicate : A → Bool)
    (items : List A) →
  Reindex.listLength (filterᵇ predicate items)
  ≤ Reindex.listLength items
filterLengthAtMost predicate [] = z≤n
filterLengthAtMost predicate (item ∷ items)
  with predicate item
... | true =
  s≤s (filterLengthAtMost predicate items)
... | false =
  weakenRight (filterLengthAtMost predicate items)

successorSquareShellLengthBound :
  (inner : Nat) →
  Reindex.listLength (successorSquareShell inner)
  ≤ squareCodeCount (suc inner)
successorSquareShellLengthBound inner =
  substRight
    (squarePointsLength (suc inner))
    (filterLengthAtMost
      (onSuccessorSquareShell? inner)
      (squarePoints (suc inner)))
  where
  substRight :
    ∀ {left middle right : Nat} →
    middle ≡ right →
    left ≤ middle →
    left ≤ right
  substRight refl proof = proof

decodeSquareCodeInSquare :
  (radius : Nat) →
  (code : SquareCode radius) →
  T (insideSquare? radius (decodeSquareCode radius code))
decodeSquareCodeInSquare radius (i , j) =
  Equivalence.from T-∧
    (Cutoff.decodeCoordinateInCutoff radius i
    ,
    Cutoff.decodeCoordinateInCutoff radius j)

squareDecodeComplete :
  (radius : Nat) →
  (point : Lattice.LatticePoint) →
  T (insideSquare? radius point) →
  Σ (SquareCode radius)
    (λ code → decodeSquareCode radius code ≡ point)
squareDecodeComplete radius
    (Lattice.lattice-point horizontal vertical)
    inside
  with Equivalence.to T-∧ inside
... | horizontalInside , verticalInside
  with Cutoff.decodeCoordinateComplete
        radius horizontal horizontalInside
     | Cutoff.decodeCoordinateComplete
        radius vertical verticalInside
... | i , iLaw | j , jLaw =
  (i , j) ,
  Lattice.lattice-ext iLaw jLaw

record SquareShellConvergenceBoundary : Set where
  field
    uniqueFiniteSquareCodesExact : Bool
    squareCodeCardinalityExact : Bool
    squareDecoderComplete : Bool
    successorShellFiniteCoverExact : Bool
    successorShellCardinalityBoundBySquareExact : Bool
    exactEightRadiusBoundaryCountNeeded : Bool
    denominatorCoerciveRadiusBoundPaidHere : Bool
    bishopPuncturedAbsoluteSummabilityPaidHere : Bool

canonicalSquareShellConvergenceBoundary :
  SquareShellConvergenceBoundary
canonicalSquareShellConvergenceBoundary = record
  { uniqueFiniteSquareCodesExact = true
  ; squareCodeCardinalityExact = true
  ; squareDecoderComplete = true
  ; successorShellFiniteCoverExact = true
  ; successorShellCardinalityBoundBySquareExact = true
  ; exactEightRadiusBoundaryCountNeeded = false
  ; denominatorCoerciveRadiusBoundPaidHere = false
  ; bishopPuncturedAbsoluteSummabilityPaidHere = false
  }
