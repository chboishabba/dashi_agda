module DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsCarrierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (+_)
open import Data.Rational using (_/_)

open import DASHI.Core.Q using
  ( ℚ ; _+ℚ_ ; _-ℚ_ ; _*ℚ_ ; zeroℚ ; oneℚ )
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Mathematics.Algebra.Ternary27FirstTitsAlbertExact as Ternary

------------------------------------------------------------------------
-- LITERAL RATIONAL FIRST-TITS CARRIER ON THE TERNARY-27 BASIS
------------------------------------------------------------------------

halfℚ : ℚ
halfℚ = + 1 / 2

record QMatrix3 : Set where
  constructor qmatrix3
  field
    m00 m01 m02 : ℚ
    m10 m11 m12 : ℚ
    m20 m21 m22 : ℚ
open QMatrix3 public

zeroM : QMatrix3
zeroM = qmatrix3 zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ zeroℚ

identityM : QMatrix3
identityM = qmatrix3 oneℚ zeroℚ zeroℚ zeroℚ oneℚ zeroℚ zeroℚ zeroℚ oneℚ

addM : QMatrix3 → QMatrix3 → QMatrix3
addM A B = qmatrix3
  (m00 A +ℚ m00 B) (m01 A +ℚ m01 B) (m02 A +ℚ m02 B)
  (m10 A +ℚ m10 B) (m11 A +ℚ m11 B) (m12 A +ℚ m12 B)
  (m20 A +ℚ m20 B) (m21 A +ℚ m21 B) (m22 A +ℚ m22 B)

subM : QMatrix3 → QMatrix3 → QMatrix3
subM A B = qmatrix3
  (m00 A -ℚ m00 B) (m01 A -ℚ m01 B) (m02 A -ℚ m02 B)
  (m10 A -ℚ m10 B) (m11 A -ℚ m11 B) (m12 A -ℚ m12 B)
  (m20 A -ℚ m20 B) (m21 A -ℚ m21 B) (m22 A -ℚ m22 B)

scaleM : ℚ → QMatrix3 → QMatrix3
scaleM q A = qmatrix3
  (q *ℚ m00 A) (q *ℚ m01 A) (q *ℚ m02 A)
  (q *ℚ m10 A) (q *ℚ m11 A) (q *ℚ m12 A)
  (q *ℚ m20 A) (q *ℚ m21 A) (q *ℚ m22 A)

mulM : QMatrix3 → QMatrix3 → QMatrix3
mulM A B = qmatrix3
  ((m00 A *ℚ m00 B) +ℚ (m01 A *ℚ m10 B) +ℚ (m02 A *ℚ m20 B))
  ((m00 A *ℚ m01 B) +ℚ (m01 A *ℚ m11 B) +ℚ (m02 A *ℚ m21 B))
  ((m00 A *ℚ m02 B) +ℚ (m01 A *ℚ m12 B) +ℚ (m02 A *ℚ m22 B))
  ((m10 A *ℚ m00 B) +ℚ (m11 A *ℚ m10 B) +ℚ (m12 A *ℚ m20 B))
  ((m10 A *ℚ m01 B) +ℚ (m11 A *ℚ m11 B) +ℚ (m12 A *ℚ m21 B))
  ((m10 A *ℚ m02 B) +ℚ (m11 A *ℚ m12 B) +ℚ (m12 A *ℚ m22 B))
  ((m20 A *ℚ m00 B) +ℚ (m21 A *ℚ m10 B) +ℚ (m22 A *ℚ m20 B))
  ((m20 A *ℚ m01 B) +ℚ (m21 A *ℚ m11 B) +ℚ (m22 A *ℚ m21 B))
  ((m20 A *ℚ m02 B) +ℚ (m21 A *ℚ m12 B) +ℚ (m22 A *ℚ m22 B))

traceM : QMatrix3 → ℚ
traceM A = m00 A +ℚ m11 A +ℚ m22 A

detM : QMatrix3 → ℚ
detM A =
  ((m00 A *ℚ m11 A) *ℚ m22 A)
  +ℚ ((m01 A *ℚ m12 A) *ℚ m20 A)
  +ℚ ((m02 A *ℚ m10 A) *ℚ m21 A)
  -ℚ ((m02 A *ℚ m11 A) *ℚ m20 A)
  -ℚ ((m01 A *ℚ m10 A) *ℚ m22 A)
  -ℚ ((m00 A *ℚ m12 A) *ℚ m21 A)

bulletM : QMatrix3 → QMatrix3 → QMatrix3
bulletM A B = scaleM halfℚ (addM (mulM A B) (mulM B A))

barM : QMatrix3 → QMatrix3
barM A = scaleM halfℚ (subM (scaleM (traceM A) identityM) A)

crossM : QMatrix3 → QMatrix3 → QMatrix3
crossM A B =
  addM
    (subM
      (subM
        (bulletM A B)
        (scaleM (halfℚ *ℚ traceM A) B))
      (scaleM (halfℚ *ℚ traceM B) A))
    (scaleM
      (halfℚ *ℚ ((traceM A *ℚ traceM B) -ℚ traceM (bulletM A B)))
      identityM)

record RationalFirstTits27 : Set where
  constructor rationalFirstTits27
  field
    block0 block1 block2 : QMatrix3
open RationalFirstTits27 public

zeroJ : RationalFirstTits27
zeroJ = rationalFirstTits27 zeroM zeroM zeroM

unitJ : RationalFirstTits27
unitJ = rationalFirstTits27 identityM zeroM zeroM

addJ : RationalFirstTits27 → RationalFirstTits27 → RationalFirstTits27
addJ X Y = rationalFirstTits27
  (addM (block0 X) (block0 Y))
  (addM (block1 X) (block1 Y))
  (addM (block2 X) (block2 Y))

scaleJ : ℚ → RationalFirstTits27 → RationalFirstTits27
scaleJ q X = rationalFirstTits27
  (scaleM q (block0 X))
  (scaleM q (block1 X))
  (scaleM q (block2 X))

firstTitsJordanProduct : RationalFirstTits27 → RationalFirstTits27 → RationalFirstTits27
firstTitsJordanProduct X Y = rationalFirstTits27
  (addM
    (bulletM (block0 X) (block0 Y))
    (addM
      (barM (mulM (block1 X) (block2 Y)))
      (barM (mulM (block1 Y) (block2 X)))))
  (addM
    (addM
      (mulM (barM (block0 X)) (block1 Y))
      (mulM (barM (block0 Y)) (block1 X)))
    (crossM (block2 X) (block2 Y)))
  (addM
    (addM
      (mulM (block2 Y) (barM (block0 X)))
      (mulM (block2 X) (barM (block0 Y))))
    (crossM (block1 X) (block1 Y)))

firstTitsCubic : RationalFirstTits27 → ℚ
firstTitsCubic X =
  detM (block0 X)
  +ℚ detM (block1 X)
  +ℚ detM (block2 X)
  -ℚ traceM (mulM (mulM (block0 X) (block1 X)) (block2 X))

deltaTrit : SSP.SSPTrit → SSP.SSPTrit → ℚ
deltaTrit SSP.sspNegOne SSP.sspNegOne = oneℚ
deltaTrit SSP.sspNegOne SSP.sspZero = zeroℚ
deltaTrit SSP.sspNegOne SSP.sspPosOne = zeroℚ
deltaTrit SSP.sspZero SSP.sspNegOne = zeroℚ
deltaTrit SSP.sspZero SSP.sspZero = oneℚ
deltaTrit SSP.sspZero SSP.sspPosOne = zeroℚ
deltaTrit SSP.sspPosOne SSP.sspNegOne = zeroℚ
deltaTrit SSP.sspPosOne SSP.sspZero = zeroℚ
deltaTrit SSP.sspPosOne SSP.sspPosOne = oneℚ

matrixUnit : SSP.SSPTrit → SSP.SSPTrit → QMatrix3
matrixUnit r c = qmatrix3
  (deltaTrit r SSP.sspNegOne *ℚ deltaTrit c SSP.sspNegOne)
  (deltaTrit r SSP.sspNegOne *ℚ deltaTrit c SSP.sspZero)
  (deltaTrit r SSP.sspNegOne *ℚ deltaTrit c SSP.sspPosOne)
  (deltaTrit r SSP.sspZero *ℚ deltaTrit c SSP.sspNegOne)
  (deltaTrit r SSP.sspZero *ℚ deltaTrit c SSP.sspZero)
  (deltaTrit r SSP.sspZero *ℚ deltaTrit c SSP.sspPosOne)
  (deltaTrit r SSP.sspPosOne *ℚ deltaTrit c SSP.sspNegOne)
  (deltaTrit r SSP.sspPosOne *ℚ deltaTrit c SSP.sspZero)
  (deltaTrit r SSP.sspPosOne *ℚ deltaTrit c SSP.sspPosOne)

basisVector : Ternary.TitsBasisSlot → RationalFirstTits27
basisVector (Ternary.titsBasisSlot Ternary.sector0 r c) =
  rationalFirstTits27 (matrixUnit r c) zeroM zeroM
basisVector (Ternary.titsBasisSlot Ternary.sector1 r c) =
  rationalFirstTits27 zeroM (matrixUnit r c) zeroM
basisVector (Ternary.titsBasisSlot Ternary.sector2 r c) =
  rationalFirstTits27 zeroM zeroM (matrixUnit r c)

record RationalFirstTitsCarrierBoundary : Set where
  constructor rational-first-tits-carrier-boundary
  field
    literalRationalCarrierDefined : Bool
    literalRationalMatrixOperationsDefined : Bool
    literalFirstTitsProductDefined : Bool
    literalFirstTitsCubicDefined : Bool
    ternaryBasisEmbeddingDefined : Bool
    characteristicThreeCarrierUsedForAlbertClassification : Bool
    bilinearityKernelProved : Bool
    commutativityKernelProved : Bool
    unitLawKernelProved : Bool
    jordanIdentityKernelProved : Bool
    cubicCompatibilityKernelProved : Bool
    classicalAlbertApplicationKernelProved : Bool
    boundary : String
open RationalFirstTitsCarrierBoundary public

canonicalBoundary : RationalFirstTitsCarrierBoundary
canonicalBoundary =
  rational-first-tits-carrier-boundary
    true true true true true false
    false false false false false false
    "The ternary 27 now indexes a literal characteristic-zero Agda carrier M3(Q)^3 with explicit first-Tits product and cubic. This removes the implementation ambiguity between the F3 toy carrier and the rational classical target. No algebra law is promoted from definition alone: bilinearity, commutativity, unit, Jordan identity, cubic compatibility and the classical Albert/F4/E6 application remain proof-relevant kernel obligations."
