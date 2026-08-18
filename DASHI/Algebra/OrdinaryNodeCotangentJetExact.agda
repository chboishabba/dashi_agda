module DASHI.Algebra.OrdinaryNodeCotangentJetExact where

------------------------------------------------------------------------
-- MATHEMATICAL CONTEXT
--
-- Robin Hartshorne,
-- "Algebraic Geometry", GTM 52, Springer, 1977.
-- DOI: 10.1007/978-1-4757-3849-0.
--
-- At an ordinary node with completed local equation xy=0, the first-order
-- neighbourhood modulo m^2 has two independent tangent directions.  The
-- corresponding truncated algebra is
--
--   k[x,y] / (xy, x^2, y^2).
--
-- DASHI CONTRIBUTION
--
-- Construct the exact integer-coefficient first-order algebra as triples
--
--   c + a x + b y
--
-- with multiplication
--
--   (c,a,b)(d,e,f)
--     = (cd, ce+da, cf+db).
--
-- This makes the two tangent directions and their zero mixed product explicit.
-- It is deliberately only the cotangent/first-jet model; it does NOT replace
-- the completed local ring k[[x,y]]/(xy).
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_)
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
import Data.Integer.Tactic.RingSolver as ℤRing
open import Agda.Builtin.List using ([]; _∷_)

record NodeJet : Set where
  constructor nodeJet
  field
    constant : ℤ
    leftTangentCoefficient : ℤ
    rightTangentCoefficient : ℤ

open NodeJet public

zeroℤ : ℤ
zeroℤ = + 0

oneℤ : ℤ
oneℤ = + 1

zeroJet : NodeJet
zeroJet = nodeJet zeroℤ zeroℤ zeroℤ

unitJet : NodeJet
unitJet = nodeJet oneℤ zeroℤ zeroℤ

addJet : NodeJet → NodeJet → NodeJet
addJet (nodeJet c a b) (nodeJet d e f) =
  nodeJet (c +ℤ d) (a +ℤ e) (b +ℤ f)

scaleJet : ℤ → NodeJet → NodeJet
scaleJet k (nodeJet c a b) =
  nodeJet (k *ℤ c) (k *ℤ a) (k *ℤ b)

multiplyJet : NodeJet → NodeJet → NodeJet
multiplyJet (nodeJet c a b) (nodeJet d e f) =
  nodeJet
    (c *ℤ d)
    ((c *ℤ e) +ℤ (d *ℤ a))
    ((c *ℤ f) +ℤ (d *ℤ b))

leftTangent : ℤ → NodeJet
leftTangent a = nodeJet zeroℤ a zeroℤ

rightTangent : ℤ → NodeJet
rightTangent b = nodeJet zeroℤ zeroℤ b

------------------------------------------------------------------------
-- Exact branch/tangent algebra.
------------------------------------------------------------------------

leftTangentConstantZero :
  (a : ℤ) → constant (leftTangent a) ≡ zeroℤ
leftTangentConstantZero a = refl

rightTangentConstantZero :
  (b : ℤ) → constant (rightTangent b) ≡ zeroℤ
rightTangentConstantZero b = refl

leftTangentKeepsCoefficient :
  (a : ℤ) → leftTangentCoefficient (leftTangent a) ≡ a
leftTangentKeepsCoefficient a = refl

rightTangentKeepsCoefficient :
  (b : ℤ) → rightTangentCoefficient (rightTangent b) ≡ b
rightTangentKeepsCoefficient b = refl

mixedTangentProductConstantZero :
  (a b : ℤ) →
  constant (multiplyJet (leftTangent a) (rightTangent b)) ≡ zeroℤ
mixedTangentProductConstantZero a b =
  ℤRing.solve (a ∷ b ∷ [])

mixedTangentProductLeftZero :
  (a b : ℤ) →
  leftTangentCoefficient
    (multiplyJet (leftTangent a) (rightTangent b)) ≡ zeroℤ
mixedTangentProductLeftZero a b =
  ℤRing.solve (a ∷ b ∷ [])

mixedTangentProductRightZero :
  (a b : ℤ) →
  rightTangentCoefficient
    (multiplyJet (leftTangent a) (rightTangent b)) ≡ zeroℤ
mixedTangentProductRightZero a b =
  ℤRing.solve (a ∷ b ∷ [])

leftSquareFirstOrderZero :
  (a : ℤ) →
  leftTangentCoefficient
    (multiplyJet (leftTangent a) (leftTangent a)) ≡ zeroℤ
leftSquareFirstOrderZero a =
  ℤRing.solve (a ∷ [])

rightSquareFirstOrderZero :
  (b : ℤ) →
  rightTangentCoefficient
    (multiplyJet (rightTangent b) (rightTangent b)) ≡ zeroℤ
rightSquareFirstOrderZero b =
  ℤRing.solve (b ∷ [])

------------------------------------------------------------------------
-- Unit multiplication and commutativity checks on the explicit algebra.
------------------------------------------------------------------------

leftUnitConstant :
  (x : NodeJet) → constant (multiplyJet unitJet x) ≡ constant x
leftUnitConstant (nodeJet c a b) = ℤRing.solve (c ∷ a ∷ b ∷ [])

leftUnitLeft :
  (x : NodeJet) →
  leftTangentCoefficient (multiplyJet unitJet x)
  ≡ leftTangentCoefficient x
leftUnitLeft (nodeJet c a b) = ℤRing.solve (c ∷ a ∷ b ∷ [])

leftUnitRight :
  (x : NodeJet) →
  rightTangentCoefficient (multiplyJet unitJet x)
  ≡ rightTangentCoefficient x
leftUnitRight (nodeJet c a b) = ℤRing.solve (c ∷ a ∷ b ∷ [])

multiplyJetCommutativeConstant :
  (x y : NodeJet) →
  constant (multiplyJet x y) ≡ constant (multiplyJet y x)
multiplyJetCommutativeConstant (nodeJet c a b) (nodeJet d e f) =
  ℤRing.solve (c ∷ a ∷ b ∷ d ∷ e ∷ f ∷ [])

multiplyJetCommutativeLeft :
  (x y : NodeJet) →
  leftTangentCoefficient (multiplyJet x y)
  ≡ leftTangentCoefficient (multiplyJet y x)
multiplyJetCommutativeLeft (nodeJet c a b) (nodeJet d e f) =
  ℤRing.solve (c ∷ a ∷ b ∷ d ∷ e ∷ f ∷ [])

multiplyJetCommutativeRight :
  (x y : NodeJet) →
  rightTangentCoefficient (multiplyJet x y)
  ≡ rightTangentCoefficient (multiplyJet y x)
multiplyJetCommutativeRight (nodeJet c a b) (nodeJet d e f) =
  ℤRing.solve (c ∷ a ∷ b ∷ d ∷ e ∷ f ∷ [])

------------------------------------------------------------------------
-- Boundary: first-order node algebra != completed local ring.
------------------------------------------------------------------------

record OrdinaryNodeCotangentJetBoundary : Set where
  field
    twoIndependentTangentCoordinatesConstructed : Bool
    mixedTangentProductZeroDerived : Bool
    firstOrderSquaresZeroDerived : Bool
    completedLocalNodeRingConstructed : Bool
    actualModularCurveLocalRingIdentified : Bool

canonicalOrdinaryNodeCotangentJetBoundary : OrdinaryNodeCotangentJetBoundary
canonicalOrdinaryNodeCotangentJetBoundary = record
  { twoIndependentTangentCoordinatesConstructed = true
  ; mixedTangentProductZeroDerived = true
  ; firstOrderSquaresZeroDerived = true
  ; completedLocalNodeRingConstructed = false
  ; actualModularCurveLocalRingIdentified = false
  }
