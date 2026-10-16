module DASHI.Moonshine.Monster3BSchrodingerAdditiveCharacterOrthogonalityExact where

------------------------------------------------------------------------
-- KERNEL-FACING ADDITIVE-CHARACTER ORTHOGONALITY CORE
--
-- The executable literal-character audit uses one algebraic cancellation:
--
--   sum_{y in F3^6} zeta^(b.y) = 729   if b = 0,
--                              = 0     if b != 0.
--
-- This owner proves the factorized finite-Fourier core from the repository's
-- exact Q(zeta_3) and F3 truth tables.  It does not yet identify this product
-- with a formal trace of the literal 729x729 monomial action; that final trace
-- bridge remains separate and is independently checked by the executable
-- all-coordinate audit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BCyclotomicLinearAlgebraExact as L
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.Monster3BFiniteSchrodingerFunctionModuleExact as V

------------------------------------------------------------------------
-- 1. One F3 coordinate.
------------------------------------------------------------------------

phaseWeightedSum : Trit → C3.Cyclotomic3
phaseWeightedSum coefficient =
  L.add
    (V.phase (H._*3_ coefficient neg))
    (L.add
      (V.phase (H._*3_ coefficient zer))
      (V.phase (H._*3_ coefficient pos)))

phaseWeightedSumNeg : phaseWeightedSum neg ≡ C3.zero
phaseWeightedSumNeg = C3.cyclotomic3Ext (solve []) (solve [])

phaseWeightedSumPos : phaseWeightedSum pos ≡ C3.zero
phaseWeightedSumPos = C3.cyclotomic3Ext (solve []) (solve [])

phaseWeightedSumZero : phaseWeightedSum zer ≡ L.three
phaseWeightedSumZero = C3.cyclotomic3Ext (solve []) (solve [])

data NonzeroTrit : Trit → Set where
  negNonzero : NonzeroTrit neg
  posNonzero : NonzeroTrit pos

phaseWeightedSumNonzero :
  (coefficient : Trit) → NonzeroTrit coefficient →
  phaseWeightedSum coefficient ≡ C3.zero
phaseWeightedSumNonzero neg negNonzero = phaseWeightedSumNeg
phaseWeightedSumNonzero pos posNonzero = phaseWeightedSumPos

------------------------------------------------------------------------
-- 2. Six-coordinate factorized character product.
------------------------------------------------------------------------

product6 :
  C3.Cyclotomic3 → C3.Cyclotomic3 → C3.Cyclotomic3 →
  C3.Cyclotomic3 → C3.Cyclotomic3 → C3.Cyclotomic3 →
  C3.Cyclotomic3
product6 z0 z1 z2 z3 z4 z5 =
  C3.multiply z0
    (C3.multiply z1
      (C3.multiply z2
        (C3.multiply z3
          (C3.multiply z4 z5))))

multiplyZeroRight : (z : C3.Cyclotomic3) →
  C3.multiply z C3.zero ≡ C3.zero
multiplyZeroRight z =
  trans (L.multiplyCommutative z C3.zero) (L.zeroActsLeft z)

product6Zero0 : (z1 z2 z3 z4 z5 : C3.Cyclotomic3) →
  product6 C3.zero z1 z2 z3 z4 z5 ≡ C3.zero
product6Zero0 z1 z2 z3 z4 z5 = L.zeroActsLeft _

product6Zero1 : (z0 z2 z3 z4 z5 : C3.Cyclotomic3) →
  product6 z0 C3.zero z2 z3 z4 z5 ≡ C3.zero
product6Zero1 z0 z2 z3 z4 z5 =
  trans
    (cong (C3.multiply z0) (L.zeroActsLeft _))
    (multiplyZeroRight z0)

product6Zero2 : (z0 z1 z3 z4 z5 : C3.Cyclotomic3) →
  product6 z0 z1 C3.zero z3 z4 z5 ≡ C3.zero
product6Zero2 z0 z1 z3 z4 z5 =
  trans
    (cong (C3.multiply z0)
      (trans
        (cong (C3.multiply z1) (L.zeroActsLeft _))
        (multiplyZeroRight z1)))
    (multiplyZeroRight z0)

product6Zero3 : (z0 z1 z2 z4 z5 : C3.Cyclotomic3) →
  product6 z0 z1 z2 C3.zero z4 z5 ≡ C3.zero
product6Zero3 z0 z1 z2 z4 z5 =
  trans
    (cong (C3.multiply z0)
      (trans
        (cong (C3.multiply z1)
          (trans
            (cong (C3.multiply z2) (L.zeroActsLeft _))
            (multiplyZeroRight z2)))
        (multiplyZeroRight z1)))
    (multiplyZeroRight z0)

product6Zero4 : (z0 z1 z2 z3 z5 : C3.Cyclotomic3) →
  product6 z0 z1 z2 z3 C3.zero z5 ≡ C3.zero
product6Zero4 z0 z1 z2 z3 z5 =
  trans
    (cong (C3.multiply z0)
      (trans
        (cong (C3.multiply z1)
          (trans
            (cong (C3.multiply z2)
              (trans
                (cong (C3.multiply z3) (L.zeroActsLeft z5))
                (multiplyZeroRight z3)))
            (multiplyZeroRight z2)))
        (multiplyZeroRight z1)))
    (multiplyZeroRight z0)

product6Zero5 : (z0 z1 z2 z3 z4 : C3.Cyclotomic3) →
  product6 z0 z1 z2 z3 z4 C3.zero ≡ C3.zero
product6Zero5 z0 z1 z2 z3 z4 =
  trans
    (cong (C3.multiply z0)
      (trans
        (cong (C3.multiply z1)
          (trans
            (cong (C3.multiply z2)
              (trans
                (cong (C3.multiply z3) (multiplyZeroRight z4))
                (multiplyZeroRight z3)))
            (multiplyZeroRight z2)))
        (multiplyZeroRight z1)))
    (multiplyZeroRight z0)

factorizedModulationCharacter : G.X6 → C3.Cyclotomic3
factorizedModulationCharacter (G.x6 b0 b1 b2 b3 b4 b5) =
  product6
    (phaseWeightedSum b0)
    (phaseWeightedSum b1)
    (phaseWeightedSum b2)
    (phaseWeightedSum b3)
    (phaseWeightedSum b4)
    (phaseWeightedSum b5)

data X6HasNonzeroCoordinate : G.X6 → Set where
  coordinate0 : ∀ {b0 b1 b2 b3 b4 b5} → NonzeroTrit b0 →
    X6HasNonzeroCoordinate (G.x6 b0 b1 b2 b3 b4 b5)
  coordinate1 : ∀ {b0 b1 b2 b3 b4 b5} → NonzeroTrit b1 →
    X6HasNonzeroCoordinate (G.x6 b0 b1 b2 b3 b4 b5)
  coordinate2 : ∀ {b0 b1 b2 b3 b4 b5} → NonzeroTrit b2 →
    X6HasNonzeroCoordinate (G.x6 b0 b1 b2 b3 b4 b5)
  coordinate3 : ∀ {b0 b1 b2 b3 b4 b5} → NonzeroTrit b3 →
    X6HasNonzeroCoordinate (G.x6 b0 b1 b2 b3 b4 b5)
  coordinate4 : ∀ {b0 b1 b2 b3 b4 b5} → NonzeroTrit b4 →
    X6HasNonzeroCoordinate (G.x6 b0 b1 b2 b3 b4 b5)
  coordinate5 : ∀ {b0 b1 b2 b3 b4 b5} → NonzeroTrit b5 →
    X6HasNonzeroCoordinate (G.x6 b0 b1 b2 b3 b4 b5)

factorizedNonzeroVector :
  (b : G.X6) → X6HasNonzeroCoordinate b →
  factorizedModulationCharacter b ≡ C3.zero
factorizedNonzeroVector
  (G.x6 b0 b1 b2 b3 b4 b5) (coordinate0 nonzero)
  rewrite phaseWeightedSumNonzero b0 nonzero =
    product6Zero0
      (phaseWeightedSum b1) (phaseWeightedSum b2)
      (phaseWeightedSum b3) (phaseWeightedSum b4)
      (phaseWeightedSum b5)
factorizedNonzeroVector
  (G.x6 b0 b1 b2 b3 b4 b5) (coordinate1 nonzero)
  rewrite phaseWeightedSumNonzero b1 nonzero =
    product6Zero1
      (phaseWeightedSum b0) (phaseWeightedSum b2)
      (phaseWeightedSum b3) (phaseWeightedSum b4)
      (phaseWeightedSum b5)
factorizedNonzeroVector
  (G.x6 b0 b1 b2 b3 b4 b5) (coordinate2 nonzero)
  rewrite phaseWeightedSumNonzero b2 nonzero =
    product6Zero2
      (phaseWeightedSum b0) (phaseWeightedSum b1)
      (phaseWeightedSum b3) (phaseWeightedSum b4)
      (phaseWeightedSum b5)
factorizedNonzeroVector
  (G.x6 b0 b1 b2 b3 b4 b5) (coordinate3 nonzero)
  rewrite phaseWeightedSumNonzero b3 nonzero =
    product6Zero3
      (phaseWeightedSum b0) (phaseWeightedSum b1)
      (phaseWeightedSum b2) (phaseWeightedSum b4)
      (phaseWeightedSum b5)
factorizedNonzeroVector
  (G.x6 b0 b1 b2 b3 b4 b5) (coordinate4 nonzero)
  rewrite phaseWeightedSumNonzero b4 nonzero =
    product6Zero4
      (phaseWeightedSum b0) (phaseWeightedSum b1)
      (phaseWeightedSum b2) (phaseWeightedSum b3)
      (phaseWeightedSum b5)
factorizedNonzeroVector
  (G.x6 b0 b1 b2 b3 b4 b5) (coordinate5 nonzero)
  rewrite phaseWeightedSumNonzero b5 nonzero =
    product6Zero5
      (phaseWeightedSum b0) (phaseWeightedSum b1)
      (phaseWeightedSum b2) (phaseWeightedSum b3)
      (phaseWeightedSum b4)

sevenHundredTwentyNine : C3.Cyclotomic3
sevenHundredTwentyNine = L.scale 729 C3.one

factorizedZeroVector :
  factorizedModulationCharacter (G.x6 zer zer zer zer zer zer)
  ≡ sevenHundredTwentyNine
factorizedZeroVector
  rewrite phaseWeightedSumZero
        | phaseWeightedSumZero
        | phaseWeightedSumZero
        | phaseWeightedSumZero
        | phaseWeightedSumZero
        | phaseWeightedSumZero =
  C3.cyclotomic3Ext (solve []) (solve [])

------------------------------------------------------------------------
-- 3. Authority boundary.
------------------------------------------------------------------------

record Boundary : Set where
  constructor boundary
  field
    oneCoordinateNontrivialCharacterCancellationPaid : Bool
    sixCoordinateFactorizedZeroVectorValuePaid : Bool
    factorizedAdditiveCharacterOrthogonalityPaid : Bool
    literalNestedBasisSumIdentifiedHere : Bool
    formalMatrixTraceIdentifiedHere : Bool
    actualMonsterCharacterIdentifiedHere : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary true true true false false false

end DASHI.Moonshine.Monster3BSchrodingerAdditiveCharacterOrthogonalityExact
