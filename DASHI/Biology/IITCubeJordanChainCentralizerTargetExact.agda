module DASHI.Biology.IITCubeJordanChainCentralizerTargetExact where

------------------------------------------------------------------------
-- CONCRETE JORDAN CHAINS FOR N = B + I AND THE EXACT TARGET CENTRALIZER ALGEBRA
--
-- The independent finite audit found Jordan type (3,3,3) for B over F3 and
-- identified its 27-dimensional centralizer with M3(F3[t]/(t^3)) after a
-- change of basis.  This module kernel-writes the two pieces that do not need a
-- generic matrix-rank library:
--
--   * three explicit length-three N-chains on the actual Face9 carrier;
--   * the exact truncated-polynomial coefficient algebra with t^3 = 0.
--
-- It deliberately does NOT claim the nine chain vectors are a basis.  The
-- finite audit has an explicit inverse 9x9 matrix, but transporting that
-- invertibility into Agda remains the one proof-relevant same-object payment.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Foundations.Base369TriTruthField as F3
import DASHI.Biology.JFinePhaseQuotientFieldExact as Fine
import DASHI.Biology.IITCubeConcreteTorusImageExact as Cube

------------------------------------------------------------------------
-- 1. N = B + I on the concrete face.
------------------------------------------------------------------------

nilpotentN : Cube.Face9 → Cube.Face9
nilpotentN face = Cube.addFace (Cube.bop face) face

basisFace :
  Base.TriTruth → Base.TriTruth → Base.TriTruth →
  Base.TriTruth → Base.TriTruth → Base.TriTruth →
  Base.TriTruth → Base.TriTruth → Base.TriTruth → Cube.Face9
basisFace = Fine.phaseFineTable9

z o m : Base.TriTruth
z = Base.tri-low
o = Base.tri-mid
m = Base.tri-high

-- Top vectors v2 are the first-row coordinate basis e00,e01,e02.
chainA2 chainB2 chainC2 : Cube.Face9
chainA2 = basisFace o z z  z z z  z z z
chainB2 = basisFace z o z  z z z  z z z
chainC2 = basisFace z z o  z z z  z z z

-- Middle vectors v1 = N v2.
chainA1 chainB1 chainC1 : Cube.Face9
chainA1 = basisFace o z o  z z z  o z z
chainB1 = basisFace o o z  z z z  z o z
chainC1 = basisFace z o o  z z z  z z o

-- Bottom vectors v0 = N^2 v2, copied from the exact finite calculation and
-- checked definitionally against the concrete operator below.
chainA0 chainB0 chainC0 : Cube.Face9
chainA0 = basisFace o o m  o z z  m z m
chainB0 = basisFace m o o  z o z  m m z
chainC0 = basisFace o m o  z z o  z m m

chainA21 : nilpotentN chainA2 ≡ chainA1
chainA21 = refl
chainA10 : nilpotentN chainA1 ≡ chainA0
chainA10 = refl
chainA0Killed : nilpotentN chainA0 ≡ Cube.zeroFace
chainA0Killed = refl

chainB21 : nilpotentN chainB2 ≡ chainB1
chainB21 = refl
chainB10 : nilpotentN chainB1 ≡ chainB0
chainB10 = refl
chainB0Killed : nilpotentN chainB0 ≡ Cube.zeroFace
chainB0Killed = refl

chainC21 : nilpotentN chainC2 ≡ chainC1
chainC21 = refl
chainC10 : nilpotentN chainC1 ≡ chainC0
chainC10 = refl
chainC0Killed : nilpotentN chainC0 ≡ Cube.zeroFace
chainC0Killed = refl

record ConcreteJordanChain3 : Set where
  constructor concrete-jordan-chain3
  field
    top middle bottom : Cube.Face9
    topToMiddle : nilpotentN top ≡ middle
    middleToBottom : nilpotentN middle ≡ bottom
    bottomKilled : nilpotentN bottom ≡ Cube.zeroFace
open ConcreteJordanChain3 public

chainA chainB chainC : ConcreteJordanChain3
chainA = concrete-jordan-chain3 chainA2 chainA1 chainA0 chainA21 chainA10 chainA0Killed
chainB = concrete-jordan-chain3 chainB2 chainB1 chainB0 chainB21 chainB10 chainB0Killed
chainC = concrete-jordan-chain3 chainC2 chainC1 chainC0 chainC21 chainC10 chainC0Killed

------------------------------------------------------------------------
-- 2. Exact F3[t]/(t^3) target algebra.
------------------------------------------------------------------------

record TruncatedPoly3 : Set where
  constructor poly3
  field
    c0 c1 c2 : Base.TriTruth
open TruncatedPoly3 public

polyZero polyOne polyT polyT2 : TruncatedPoly3
polyZero = poly3 z z z
polyOne  = poly3 o z z
polyT    = poly3 z o z
polyT2   = poly3 z z o

polyAdd : TruncatedPoly3 → TruncatedPoly3 → TruncatedPoly3
polyAdd a b = poly3
  (F3.triAdd (c0 a) (c0 b))
  (F3.triAdd (c1 a) (c1 b))
  (F3.triAdd (c2 a) (c2 b))

polyMul : TruncatedPoly3 → TruncatedPoly3 → TruncatedPoly3
polyMul a b = poly3
  (F3.triMul (c0 a) (c0 b))
  (F3.triAdd
    (F3.triMul (c0 a) (c1 b))
    (F3.triMul (c1 a) (c0 b)))
  (F3.triAdd
    (F3.triAdd
      (F3.triMul (c0 a) (c2 b))
      (F3.triMul (c1 a) (c1 b)))
    (F3.triMul (c2 a) (c0 b)))

polyTT : polyMul polyT polyT ≡ polyT2
polyTT = refl

polyT2TZero : polyMul polyT2 polyT ≡ polyZero
polyT2TZero = refl

polyTT2Zero : polyMul polyT polyT2 ≡ polyZero
polyTT2Zero = refl

polyT3Zero : polyMul (polyMul polyT polyT) polyT ≡ polyZero
polyT3Zero = refl

------------------------------------------------------------------------
-- 3. 3x3 matrices over the truncated-polynomial algebra.
------------------------------------------------------------------------

record Matrix3Poly : Set where
  constructor matrix3poly
  field
    p00 p01 p02
      p10 p11 p12
      p20 p21 p22 : TruncatedPoly3
open Matrix3Poly public

matrixZero : Matrix3Poly
matrixZero = matrix3poly
  polyZero polyZero polyZero
  polyZero polyZero polyZero
  polyZero polyZero polyZero

polySum3 : TruncatedPoly3 → TruncatedPoly3 → TruncatedPoly3 → TruncatedPoly3
polySum3 a b c = polyAdd (polyAdd a b) c

matrixMul : Matrix3Poly → Matrix3Poly → Matrix3Poly
matrixMul a b = matrix3poly
  (polySum3 (polyMul (p00 a) (p00 b)) (polyMul (p01 a) (p10 b)) (polyMul (p02 a) (p20 b)))
  (polySum3 (polyMul (p00 a) (p01 b)) (polyMul (p01 a) (p11 b)) (polyMul (p02 a) (p21 b)))
  (polySum3 (polyMul (p00 a) (p02 b)) (polyMul (p01 a) (p12 b)) (polyMul (p02 a) (p22 b)))
  (polySum3 (polyMul (p10 a) (p00 b)) (polyMul (p11 a) (p10 b)) (polyMul (p12 a) (p20 b)))
  (polySum3 (polyMul (p10 a) (p01 b)) (polyMul (p11 a) (p11 b)) (polyMul (p12 a) (p21 b)))
  (polySum3 (polyMul (p10 a) (p02 b)) (polyMul (p11 a) (p12 b)) (polyMul (p12 a) (p22 b)))
  (polySum3 (polyMul (p20 a) (p00 b)) (polyMul (p21 a) (p10 b)) (polyMul (p22 a) (p20 b)))
  (polySum3 (polyMul (p20 a) (p01 b)) (polyMul (p21 a) (p11 b)) (polyMul (p22 a) (p21 b)))
  (polySum3 (polyMul (p20 a) (p02 b)) (polyMul (p21 a) (p12 b)) (polyMul (p22 a) (p22 b)))

------------------------------------------------------------------------
-- 4. Proof-relevant remaining bridge.  This is intentionally uninhabited here:
--    it asks for actual encode/decode maps showing the nine concrete chain
--    vectors form a basis, after which the standard block-polynomial action is
--    the concrete centralizer action.
------------------------------------------------------------------------

record ConcreteJordanBasisIntertwiner : Set₁ where
  field
    JordanCoordinates : Set
    encode : Cube.Face9 → JordanCoordinates
    decode : JordanCoordinates → Cube.Face9
    decodeEncode : (face : Cube.Face9) → decode (encode face) ≡ face
    encodeDecode : (coordinates : JordanCoordinates) → encode (decode coordinates) ≡ coordinates
    nilpotentActsAsThreeLengthThreeJordanBlocks : Set
    matrix3TruncatedPolynomialActionIntertwinesConcreteCentralizer : Set
open ConcreteJordanBasisIntertwiner public

record JordanCentralizerStatus : Set where
  constructor jordan-centralizer-status
  field
    threeConcreteLengthThreeChainsKernelWritten : Bool
    truncatedPolynomialT3ZeroKernelWritten : Bool
    threeByThreeTruncatedPolynomialAlgebraKernelWritten : Bool
    finiteAuditProvidesExplicitInverseBasisMatrix : Bool
    finiteAuditProvides27DimensionalCentralizer : Bool
    finiteAuditChecksFullBasisMultiplicationTable : Bool
    concreteJordanBasisIntertwinerKernelPaid : Bool
    concreteFullCentralizerAlgebraIsomorphismKernelPaid : Bool
open JordanCentralizerStatus public

canonicalJordanCentralizerStatus : JordanCentralizerStatus
canonicalJordanCentralizerStatus =
  jordan-centralizer-status true true true true true true false false
