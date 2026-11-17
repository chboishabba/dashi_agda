module DASHI.Physics.YangMills.BalabanPath13GeneratedLDLCoefficientProofExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _-_; -_; _≤_; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (sq; sqDiff; baseBelowBasePlusRemainder)
open import DASHI.Physics.YangMills.BalabanRationalLDLCertificate using
  (LDLTerm; ldlTerm; sumTermValues; sumTermValuesNonnegative)
open import DASHI.Physics.YangMills.BalabanPath13ScaledIntegerCoefficientDataExact public
import DASHI.Physics.YangMills.BalabanTriangularQuadraticCertificateExact as Quad

------------------------------------------------------------------------
-- Literal linear carrier attachments.
-- Only degree-1 equalities see all twelve Path13 coordinates.
------------------------------------------------------------------------

energyLinear0 : ∀ c → Quad.dot energy0Coefficients (coordinates c) ≡ y1 c - y0 c
energyLinear0 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear1 : ∀ c → Quad.dot energy1Coefficients (coordinates c) ≡ y2 c - y1 c
energyLinear1 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear2 : ∀ c → Quad.dot energy2Coefficients (coordinates c) ≡ y3 c - y2 c
energyLinear2 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear3 : ∀ c → Quad.dot energy3Coefficients (coordinates c) ≡ y4 c - y3 c
energyLinear3 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear4 : ∀ c → Quad.dot energy4Coefficients (coordinates c) ≡ y5 c - y4 c
energyLinear4 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear5 : ∀ c → Quad.dot energy5Coefficients (coordinates c) ≡ y6 c - y5 c
energyLinear5 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear6 : ∀ c → Quad.dot energy6Coefficients (coordinates c) ≡ y7 c - y6 c
energyLinear6 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear7 : ∀ c → Quad.dot energy7Coefficients (coordinates c) ≡ y8 c - y7 c
energyLinear7 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear8 : ∀ c → Quad.dot energy8Coefficients (coordinates c) ≡ y9 c - y8 c
energyLinear8 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear9 : ∀ c → Quad.dot energy9Coefficients (coordinates c) ≡ y10 c - y9 c
energyLinear9 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear10 : ∀ c → Quad.dot energy10Coefficients (coordinates c) ≡ y11 c - y10 c
energyLinear10 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
energyLinear11 : ∀ c → Quad.dot energy11Coefficients (coordinates c) ≡ lastCoordinate c - y11 c
energyLinear11 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀

normLinear0 : ∀ c → Quad.dot norm0Coefficients (coordinates c) ≡ y0 c
normLinear0 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear1 : ∀ c → Quad.dot norm1Coefficients (coordinates c) ≡ y1 c
normLinear1 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear2 : ∀ c → Quad.dot norm2Coefficients (coordinates c) ≡ y2 c
normLinear2 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear3 : ∀ c → Quad.dot norm3Coefficients (coordinates c) ≡ y3 c
normLinear3 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear4 : ∀ c → Quad.dot norm4Coefficients (coordinates c) ≡ y4 c
normLinear4 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear5 : ∀ c → Quad.dot norm5Coefficients (coordinates c) ≡ y5 c
normLinear5 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear6 : ∀ c → Quad.dot norm6Coefficients (coordinates c) ≡ y6 c
normLinear6 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear7 : ∀ c → Quad.dot norm7Coefficients (coordinates c) ≡ y7 c
normLinear7 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear8 : ∀ c → Quad.dot norm8Coefficients (coordinates c) ≡ y8 c
normLinear8 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear9 : ∀ c → Quad.dot norm9Coefficients (coordinates c) ≡ y9 c
normLinear9 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear10 : ∀ c → Quad.dot norm10Coefficients (coordinates c) ≡ y10 c
normLinear10 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear11 : ∀ c → Quad.dot norm11Coefficients (coordinates c) ≡ y11 c
normLinear11 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
normLinear12 : ∀ c → Quad.dot norm12Coefficients (coordinates c) ≡ lastCoordinate c
normLinear12 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀

dropTrailingZero12 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 →
  v0 + (v1 + (v2 + (v3 + (v4 + (v5 + (v6 + (v7 + (v8 + (v9 + (v10 + (v11 + 0ℚ)))))))))))
  ≡ v0 + (v1 + (v2 + (v3 + (v4 + (v5 + (v6 + (v7 + (v8 + (v9 + (v10 + v11))))))))))
dropTrailingZero12 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  rewrite ℚP.+-identityʳ v11 = refl

dropTrailingZero13 : ∀ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 →
  v0 + (v1 + (v2 + (v3 + (v4 + (v5 + (v6 + (v7 + (v8 + (v9 + (v10 + (v11 + (v12 + 0ℚ))))))))))))
  ≡ v0 + (v1 + (v2 + (v3 + (v4 + (v5 + (v6 + (v7 + (v8 + (v9 + (v10 + (v11 + v12)))))))))))
dropTrailingZero13 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  rewrite ℚP.+-identityʳ v12 = refl

energyValuesMatch : ∀ c → Quad.sumSquareValues energyFamilies (coordinates c) ≡ path13Energy c
energyValuesMatch c
  rewrite energyLinear0 c | energyLinear1 c | energyLinear2 c | energyLinear3 c
        | energyLinear4 c | energyLinear5 c | energyLinear6 c | energyLinear7 c
        | energyLinear8 c | energyLinear9 c | energyLinear10 c | energyLinear11 c
  = dropTrailingZero12
      (sqDiff (y1 c) (y0 c)) (sqDiff (y2 c) (y1 c))
      (sqDiff (y3 c) (y2 c)) (sqDiff (y4 c) (y3 c))
      (sqDiff (y5 c) (y4 c)) (sqDiff (y6 c) (y5 c))
      (sqDiff (y7 c) (y6 c)) (sqDiff (y8 c) (y7 c))
      (sqDiff (y9 c) (y8 c)) (sqDiff (y10 c) (y9 c))
      (sqDiff (y11 c) (y10 c)) (sqDiff (lastCoordinate c) (y11 c))

normValuesMatch : ∀ c → Quad.sumSquareValues normFamilies (coordinates c) ≡ path13NormSq c
normValuesMatch c
  rewrite normLinear0 c | normLinear1 c | normLinear2 c | normLinear3 c
        | normLinear4 c | normLinear5 c | normLinear6 c | normLinear7 c
        | normLinear8 c | normLinear9 c | normLinear10 c | normLinear11 c
        | normLinear12 c
  = dropTrailingZero13
      (sq (y0 c)) (sq (y1 c)) (sq (y2 c)) (sq (y3 c)) (sq (y4 c))
      (sq (y5 c)) (sq (y6 c)) (sq (y7 c)) (sq (y8 c)) (sq (y9 c))
      (sq (y10 c)) (sq (y11 c)) (sq (lastCoordinate c))

------------------------------------------------------------------------
-- Positive scaled remainder terms.
-- All pivots below are integer-valued rationals (denominator one).
------------------------------------------------------------------------

scaledTerms : List (LDLTerm Path13Coordinates)
scaledTerms =
  ldlTerm weight0
      (λ c → Quad.dot scaledForm0Coefficients (coordinates c))
      (nonnegativeFraction 2061771004467132024503554087757365850226084149255749046069268551725852249699567096500120 1)
  ∷ ldlTerm weight1
      (λ c → Quad.dot scaledForm1Coefficients (coordinates c))
      (nonnegativeFraction 1166820036483945684495503162284870317049283615877616890814526628028212931352329992360 1)
  ∷ ldlTerm weight2
      (λ c → Quad.dot scaledForm2Coefficients (coordinates c))
      (nonnegativeFraction 516184569070133148652637497627844160243515703911717683560085163851348491542354790 1)
  ∷ ldlTerm weight3
      (λ c → Quad.dot scaledForm3Coefficients (coordinates c))
      (nonnegativeFraction 333311577913220877263985596900974587050664212222084832136355989818036861520410 1)
  ∷ ldlTerm weight4
      (λ c → Quad.dot scaledForm4Coefficients (coordinates c))
      (nonnegativeFraction 304571911433633422309212676693195862576509470510122590650102573276567416520 1)
  ∷ ldlTerm weight5
      (λ c → Quad.dot scaledForm5Coefficients (coordinates c))
      (nonnegativeFraction 359283849351979050241613722186255465805006820960171635652182617406418840 1)
  ∷ ldlTerm weight6
      (λ c → Quad.dot scaledForm6Coefficients (coordinates c))
      (nonnegativeFraction 513541079670314261521825542054473656850485861884756032842578615922452 1)
  ∷ ldlTerm weight7
      (λ c → Quad.dot scaledForm7Coefficients (coordinates c))
      (nonnegativeFraction 21357539703932072702412498496181071098644299249140047543595620925740 1)
  ∷ ldlTerm weight8
      (λ c → Quad.dot scaledForm8Coefficients (coordinates c))
      (nonnegativeFraction 582011029774935626619634825519095089613274052507535637487672892088 1)
  ∷ ldlTerm weight9
      (λ c → Quad.dot scaledForm9Coefficients (coordinates c))
      (nonnegativeFraction 3396621855440594756988773113168811067316871714047695079112040 1)
  ∷ ldlTerm weight10
      (λ c → Quad.dot scaledForm10Coefficients (coordinates c))
      (nonnegativeFraction 7915733682361932346419013108004980848910522080156599162595 1)
  ∷ ldlTerm weight11
      (λ c → Quad.dot scaledForm11Coefficients (coordinates c))
      (nonnegativeFraction 23654724725960859118550599727273560507275252328952867480395816966937511364540065812424285 1)
  ∷ []

scaledRemainderValues : ∀ c →
  Quad.sumWeightedSquareValues scaledLDLFamilies (coordinates c)
  ≡ sumTermValues scaledTerms c
scaledRemainderValues c = refl

------------------------------------------------------------------------
-- Closed 78-coefficient payment, split into twelve triangular rows.
-- Every closed coefficient has denominator one.
------------------------------------------------------------------------

diagOf : Quad.TriQuadratic → ℚ
diagOf Quad.qnil = 0ℚ
diagOf (Quad.qcons diagonal row tail) = diagonal

rowOf : Quad.TriQuadratic → List ℚ
rowOf Quad.qnil = []
rowOf (Quad.qcons diagonal row tail) = row

tailOf : Quad.TriQuadratic → Quad.TriQuadratic
tailOf Quad.qnil = Quad.qnil
tailOf (Quad.qcons diagonal row tail) = tail

gapTail0 gapTail1 gapTail2 gapTail3 gapTail4 gapTail5 gapTail6 : Quad.TriQuadratic
gapTail7 gapTail8 gapTail9 gapTail10 gapTail11 gapTail12 : Quad.TriQuadratic
gapTail0 = scaledGapTri
gapTail1 = tailOf gapTail0
gapTail2 = tailOf gapTail1
gapTail3 = tailOf gapTail2
gapTail4 = tailOf gapTail3
gapTail5 = tailOf gapTail4
gapTail6 = tailOf gapTail5
gapTail7 = tailOf gapTail6
gapTail8 = tailOf gapTail7
gapTail9 = tailOf gapTail8
gapTail10 = tailOf gapTail9
gapTail11 = tailOf gapTail10
gapTail12 = tailOf gapTail11

ldlTail0 ldlTail1 ldlTail2 ldlTail3 ldlTail4 ldlTail5 ldlTail6 : Quad.TriQuadratic
ldlTail7 ldlTail8 ldlTail9 ldlTail10 ldlTail11 ldlTail12 : Quad.TriQuadratic
ldlTail0 = scaledLDLTri
ldlTail1 = tailOf ldlTail0
ldlTail2 = tailOf ldlTail1
ldlTail3 = tailOf ldlTail2
ldlTail4 = tailOf ldlTail3
ldlTail5 = tailOf ldlTail4
ldlTail6 = tailOf ldlTail5
ldlTail7 = tailOf ldlTail6
ldlTail8 = tailOf ldlTail7
ldlTail9 = tailOf ldlTail8
ldlTail10 = tailOf ldlTail9
ldlTail11 = tailOf ldlTail10
ldlTail12 = tailOf ldlTail11

row0Diag : diagOf gapTail0 ≡ diagOf ldlTail0
row0Diag = refl
row0Off : rowOf gapTail0 ≡ rowOf ldlTail0
row0Off = refl
row1Diag : diagOf gapTail1 ≡ diagOf ldlTail1
row1Diag = refl
row1Off : rowOf gapTail1 ≡ rowOf ldlTail1
row1Off = refl
row2Diag : diagOf gapTail2 ≡ diagOf ldlTail2
row2Diag = refl
row2Off : rowOf gapTail2 ≡ rowOf ldlTail2
row2Off = refl
row3Diag : diagOf gapTail3 ≡ diagOf ldlTail3
row3Diag = refl
row3Off : rowOf gapTail3 ≡ rowOf ldlTail3
row3Off = refl
row4Diag : diagOf gapTail4 ≡ diagOf ldlTail4
row4Diag = refl
row4Off : rowOf gapTail4 ≡ rowOf ldlTail4
row4Off = refl
row5Diag : diagOf gapTail5 ≡ diagOf ldlTail5
row5Diag = refl
row5Off : rowOf gapTail5 ≡ rowOf ldlTail5
row5Off = refl
row6Diag : diagOf gapTail6 ≡ diagOf ldlTail6
row6Diag = refl
row6Off : rowOf gapTail6 ≡ rowOf ldlTail6
row6Off = refl
row7Diag : diagOf gapTail7 ≡ diagOf ldlTail7
row7Diag = refl
row7Off : rowOf gapTail7 ≡ rowOf ldlTail7
row7Off = refl
row8Diag : diagOf gapTail8 ≡ diagOf ldlTail8
row8Diag = refl
row8Off : rowOf gapTail8 ≡ rowOf ldlTail8
row8Off = refl
row9Diag : diagOf gapTail9 ≡ diagOf ldlTail9
row9Diag = refl
row9Off : rowOf gapTail9 ≡ rowOf ldlTail9
row9Off = refl
row10Diag : diagOf gapTail10 ≡ diagOf ldlTail10
row10Diag = refl
row10Off : rowOf gapTail10 ≡ rowOf ldlTail10
row10Off = refl
row11Diag : diagOf gapTail11 ≡ diagOf ldlTail11
row11Diag = refl
row11Off : rowOf gapTail11 ≡ rowOf ldlTail11
row11Off = refl

gapTail12EqualsLDL : gapTail12 ≡ ldlTail12
gapTail12EqualsLDL = refl
gapTail11EqualsLDL : gapTail11 ≡ ldlTail11
gapTail11EqualsLDL = Quad.qconsCong row11Diag row11Off gapTail12EqualsLDL
gapTail10EqualsLDL : gapTail10 ≡ ldlTail10
gapTail10EqualsLDL = Quad.qconsCong row10Diag row10Off gapTail11EqualsLDL
gapTail9EqualsLDL : gapTail9 ≡ ldlTail9
gapTail9EqualsLDL = Quad.qconsCong row9Diag row9Off gapTail10EqualsLDL
gapTail8EqualsLDL : gapTail8 ≡ ldlTail8
gapTail8EqualsLDL = Quad.qconsCong row8Diag row8Off gapTail9EqualsLDL
gapTail7EqualsLDL : gapTail7 ≡ ldlTail7
gapTail7EqualsLDL = Quad.qconsCong row7Diag row7Off gapTail8EqualsLDL
gapTail6EqualsLDL : gapTail6 ≡ ldlTail6
gapTail6EqualsLDL = Quad.qconsCong row6Diag row6Off gapTail7EqualsLDL
gapTail5EqualsLDL : gapTail5 ≡ ldlTail5
gapTail5EqualsLDL = Quad.qconsCong row5Diag row5Off gapTail6EqualsLDL
gapTail4EqualsLDL : gapTail4 ≡ ldlTail4
gapTail4EqualsLDL = Quad.qconsCong row4Diag row4Off gapTail5EqualsLDL
gapTail3EqualsLDL : gapTail3 ≡ ldlTail3
gapTail3EqualsLDL = Quad.qconsCong row3Diag row3Off gapTail4EqualsLDL
gapTail2EqualsLDL : gapTail2 ≡ ldlTail2
gapTail2EqualsLDL = Quad.qconsCong row2Diag row2Off gapTail3EqualsLDL
gapTail1EqualsLDL : gapTail1 ≡ ldlTail1
gapTail1EqualsLDL = Quad.qconsCong row1Diag row1Off gapTail2EqualsLDL
gapTail0EqualsLDL : gapTail0 ≡ ldlTail0
gapTail0EqualsLDL = Quad.qconsCong row0Diag row0Off gapTail1EqualsLDL

scaledGapTriEqualsLDLTri : scaledGapTri ≡ scaledLDLTri
scaledGapTriEqualsLDLTri = gapTail0EqualsLDL

------------------------------------------------------------------------
-- Compiler output: closed coefficient payment -> scaled physical inequality.
------------------------------------------------------------------------

energyTriValue : ∀ c → Quad.evalTri energyTri (coordinates c) ≡ path13Energy c
energyTriValue c =
  trans (Quad.sumSquareCompiler energyFamilies (coordinates c)) (energyValuesMatch c)

normTriValue : ∀ c → Quad.evalTri normTri (coordinates c) ≡ path13NormSq c
normTriValue c =
  trans (Quad.sumSquareCompiler normFamilies (coordinates c)) (normValuesMatch c)

scaledLDLTriValue : ∀ c →
  Quad.evalTri scaledLDLTri (coordinates c) ≡ sumTermValues scaledTerms c
scaledLDLTriValue c =
  trans (Quad.sumWeightedSquareCompiler scaledLDLFamilies (coordinates c))
        (scaledRemainderValues c)

scaledGapArithmetic : ∀ m k energyValue normValue →
  m * energyValue + (- k) * normValue
  ≡ m * energyValue - k * normValue
scaledGapArithmetic = ℚRing.solve-∀

scaledGapTriValue : ∀ c →
  Quad.evalTri scaledGapTri (coordinates c)
  ≡ scaleM * path13Energy c - scaleK * path13NormSq c
scaledGapTriValue c =
  trans
    (Quad.evalAdd
      (Quad.scaleTri scaleM energyTri)
      (Quad.scaleTri (- scaleK) normTri)
      (coordinates c))
    (trans
      (cong₂ _+_
        (trans (Quad.evalScale scaleM energyTri (coordinates c))
               (cong (λ value → scaleM * value) (energyTriValue c)))
        (trans (Quad.evalScale (- scaleK) normTri (coordinates c))
               (cong (λ value → (- scaleK) * value) (normTriValue c))))
      (scaledGapArithmetic scaleM scaleK (path13Energy c) (path13NormSq c)))

path13ScaledGapToTerms : ∀ c →
  scaleM * path13Energy c - scaleK * path13NormSq c
  ≡ sumTermValues scaledTerms c
path13ScaledGapToTerms c =
  trans (sym (scaledGapTriValue c))
    (trans
      (cong (λ quadratic → Quad.evalTri quadratic (coordinates c))
            scaledGapTriEqualsLDLTri)
      (scaledLDLTriValue c))

scaledRecompose : ∀ m k energyValue normValue →
  m * energyValue
  ≡ k * normValue + (m * energyValue - k * normValue)
scaledRecompose = ℚRing.solve-∀

path13ScaledLDLDecomposition : ∀ c →
  scaleM * path13Energy c
  ≡ scaleK * path13NormSq c + sumTermValues scaledTerms c
path13ScaledLDLDecomposition c =
  trans
    (scaledRecompose scaleM scaleK (path13Energy c) (path13NormSq c))
    (cong
      (λ remainder → scaleK * path13NormSq c + remainder)
      (path13ScaledGapToTerms c))

path13ScaledBaseBelow : ∀ c →
  scaleK * path13NormSq c ≤ scaleM * path13Energy c
path13ScaledBaseBelow c =
  subst
    (λ right → scaleK * path13NormSq c ≤ right)
    (sym (path13ScaledLDLDecomposition c))
    (baseBelowBasePlusRemainder
      (scaleK * path13NormSq c)
      (sumTermValues scaledTerms c)
      (sumTermValuesNonnegative scaledTerms c))

------------------------------------------------------------------------
-- Cancel the positive common scale M.  The only 1/18 algebra is proved
-- generically before the huge integer scale is instantiated.
------------------------------------------------------------------------

eighteenTimesOneEighteenth : ∀ k value →
  (eighteenℚ * k) * (oneEighteenth * value) ≡ k * value
eighteenTimesOneEighteenth = ℚRing.solve-∀

scaledLeftIdentity : ∀ value →
  scaleM * (oneEighteenth * value) ≡ scaleK * value
scaledLeftIdentity value = eighteenTimesOneEighteenth scaleK value

path13ScaledTarget : ∀ c →
  scaleM * (oneEighteenth * path13NormSq c)
  ≤ scaleM * path13Energy c
path13ScaledTarget c =
  subst
    (λ left → left ≤ scaleM * path13Energy c)
    (sym (scaledLeftIdentity (path13NormSq c)))
    (path13ScaledBaseBelow c)

scaleKPositive : Positive scaleK
scaleKPositive = ℚP.normalize-pos 70100214151882488833120838983750438907686861074695467566355130758678976489785281281004080 1

eighteenPositive : Positive eighteenℚ
eighteenPositive = ℚP.normalize-pos 18 1

scaleMPositive : Positive scaleM
scaleMPositive =
  let
    instance
      kPositive : Positive scaleK
      kPositive = scaleKPositive

      eighteenPositiveInstance : Positive eighteenℚ
      eighteenPositiveInstance = eighteenPositive
  in
  ℚP.pos*pos⇒pos eighteenℚ scaleK

path13Poincare : ∀ c → oneEighteenth * path13NormSq c ≤ path13Energy c
path13Poincare c =
  let
    instance
      scaleMPositiveInstance : Positive scaleM
      scaleMPositiveInstance = scaleMPositive
  in
  ℚP.*-cancelˡ-≤-pos scaleM (path13ScaledTarget c)

path13CoefficientCertificateLevel : ProofLevel
path13CoefficientCertificateLevel = machineChecked
