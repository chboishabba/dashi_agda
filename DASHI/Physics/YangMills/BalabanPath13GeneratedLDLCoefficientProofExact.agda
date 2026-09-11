module DASHI.Physics.YangMills.BalabanPath13GeneratedLDLCoefficientProofExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _-_; -_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using (sq; sqDiff)
open import DASHI.Physics.YangMills.BalabanRationalLDLCertificate
open import DASHI.Physics.YangMills.BalabanPath13QuadraticCoefficientDataExact public
import DASHI.Physics.YangMills.BalabanTriangularQuadraticCertificateExact as Quad

------------------------------------------------------------------------
-- Literal linear carriers.
--
-- These are deliberately the only Path13 proofs below that mention the twelve
-- symbolic coordinates at once.  Every identity is linear; no dense square or
-- quadratic polynomial is sent to reflection.
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

formLinear0 : ∀ c → Quad.dot form0Coefficients (coordinates c) ≡ form0 c
formLinear0 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear1 : ∀ c → Quad.dot form1Coefficients (coordinates c) ≡ form1 c
formLinear1 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear2 : ∀ c → Quad.dot form2Coefficients (coordinates c) ≡ form2 c
formLinear2 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear3 : ∀ c → Quad.dot form3Coefficients (coordinates c) ≡ form3 c
formLinear3 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear4 : ∀ c → Quad.dot form4Coefficients (coordinates c) ≡ form4 c
formLinear4 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear5 : ∀ c → Quad.dot form5Coefficients (coordinates c) ≡ form5 c
formLinear5 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear6 : ∀ c → Quad.dot form6Coefficients (coordinates c) ≡ form6 c
formLinear6 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear7 : ∀ c → Quad.dot form7Coefficients (coordinates c) ≡ form7 c
formLinear7 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear8 : ∀ c → Quad.dot form8Coefficients (coordinates c) ≡ form8 c
formLinear8 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear9 : ∀ c → Quad.dot form9Coefficients (coordinates c) ≡ form9 c
formLinear9 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear10 : ∀ c → Quad.dot form10Coefficients (coordinates c) ≡ form10 c
formLinear10 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀
formLinear11 : ∀ c → Quad.dot form11Coefficients (coordinates c) ≡ form11 c
formLinear11 (path13Coordinates a b c d e f g h i j k l) = ℚRing.solve-∀

------------------------------------------------------------------------
-- Attach the structural quadratic compilers to the literal Path13 functions.
------------------------------------------------------------------------

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

ldlValuesMatch : ∀ c →
  Quad.sumWeightedSquareValues ldlFamilies (coordinates c)
  ≡ sumTermValues path13Terms c
ldlValuesMatch c
  rewrite formLinear0 c | formLinear1 c | formLinear2 c | formLinear3 c
        | formLinear4 c | formLinear5 c | formLinear6 c | formLinear7 c
        | formLinear8 c | formLinear9 c | formLinear10 c | formLinear11 c
  = refl

------------------------------------------------------------------------
-- Closed coefficient certificate.
--
-- The following twelve rows are the 78 independent coefficients of the
-- symmetric Path13 gap matrix, using the full x_i*x_j coefficient convention.
-- Both the physical gap compiler and the LDL compiler must reduce to this same
-- finite carrier.  Each `refl` below is therefore closed rational computation;
-- there are no symbolic Path13 variables in these checks.
------------------------------------------------------------------------

canonicalDiag0 canonicalDiag1 canonicalDiag2 canonicalDiag3 : ℚ
canonicalDiag4 canonicalDiag5 canonicalDiag6 canonicalDiag7 : ℚ
canonicalDiag8 canonicalDiag9 canonicalDiag10 canonicalDiag11 : ℚ
canonicalDiag0 = + 17 / 9
canonicalDiag1 = + 26 / 9
canonicalDiag2 = + 26 / 9
canonicalDiag3 = + 26 / 9
canonicalDiag4 = + 26 / 9
canonicalDiag5 = + 26 / 9
canonicalDiag6 = + 26 / 9
canonicalDiag7 = + 26 / 9
canonicalDiag8 = + 26 / 9
canonicalDiag9 = + 26 / 9
canonicalDiag10 = + 26 / 9
canonicalDiag11 = + 44 / 9

canonicalRow0 canonicalRow1 canonicalRow2 canonicalRow3 : List ℚ
canonicalRow4 canonicalRow5 canonicalRow6 canonicalRow7 : List ℚ
canonicalRow8 canonicalRow9 canonicalRow10 canonicalRow11 : List ℚ
canonicalRow0 = (- (+ 1 / 9)) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 35 / 9) ∷ []
canonicalRow1 = (- (+ 1 / 9)) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 35 / 9) ∷ []
canonicalRow2 = (- (+ 1 / 9)) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 35 / 9) ∷ []
canonicalRow3 = (- (+ 1 / 9)) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 35 / 9) ∷ []
canonicalRow4 = (- (+ 1 / 9)) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 35 / 9) ∷ []
canonicalRow5 = (- (+ 1 / 9)) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 35 / 9) ∷ []
canonicalRow6 = (- (+ 1 / 9)) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 35 / 9) ∷ []
canonicalRow7 = (- (+ 1 / 9)) ∷ (+ 17 / 9) ∷ (+ 17 / 9) ∷ (+ 35 / 9) ∷ []
canonicalRow8 = (- (+ 1 / 9)) ∷ (+ 17 / 9) ∷ (+ 35 / 9) ∷ []
canonicalRow9 = (- (+ 1 / 9)) ∷ (+ 35 / 9) ∷ []
canonicalRow10 = (+ 17 / 9) ∷ []
canonicalRow11 = []

canonicalTail12 canonicalTail11 canonicalTail10 canonicalTail9 : Quad.TriQuadratic
canonicalTail8 canonicalTail7 canonicalTail6 canonicalTail5 : Quad.TriQuadratic
canonicalTail4 canonicalTail3 canonicalTail2 canonicalTail1 canonicalTail0 : Quad.TriQuadratic
canonicalTail12 = Quad.qnil
canonicalTail11 = Quad.qcons canonicalDiag11 canonicalRow11 canonicalTail12
canonicalTail10 = Quad.qcons canonicalDiag10 canonicalRow10 canonicalTail11
canonicalTail9 = Quad.qcons canonicalDiag9 canonicalRow9 canonicalTail10
canonicalTail8 = Quad.qcons canonicalDiag8 canonicalRow8 canonicalTail9
canonicalTail7 = Quad.qcons canonicalDiag7 canonicalRow7 canonicalTail8
canonicalTail6 = Quad.qcons canonicalDiag6 canonicalRow6 canonicalTail7
canonicalTail5 = Quad.qcons canonicalDiag5 canonicalRow5 canonicalTail6
canonicalTail4 = Quad.qcons canonicalDiag4 canonicalRow4 canonicalTail5
canonicalTail3 = Quad.qcons canonicalDiag3 canonicalRow3 canonicalTail4
canonicalTail2 = Quad.qcons canonicalDiag2 canonicalRow2 canonicalTail3
canonicalTail1 = Quad.qcons canonicalDiag1 canonicalRow1 canonicalTail2
canonicalTail0 = Quad.qcons canonicalDiag0 canonicalRow0 canonicalTail1

canonicalTri : Quad.TriQuadratic
canonicalTri = canonicalTail0

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
gapTail0 = gapTri
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
ldlTail0 = ldlTri
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

gapDiag0 : diagOf gapTail0 ≡ canonicalDiag0
gapDiag0 = refl
gapRow0 : rowOf gapTail0 ≡ canonicalRow0
gapRow0 = refl
gapDiag1 : diagOf gapTail1 ≡ canonicalDiag1
gapDiag1 = refl
gapRow1 : rowOf gapTail1 ≡ canonicalRow1
gapRow1 = refl
gapDiag2 : diagOf gapTail2 ≡ canonicalDiag2
gapDiag2 = refl
gapRow2 : rowOf gapTail2 ≡ canonicalRow2
gapRow2 = refl
gapDiag3 : diagOf gapTail3 ≡ canonicalDiag3
gapDiag3 = refl
gapRow3 : rowOf gapTail3 ≡ canonicalRow3
gapRow3 = refl
gapDiag4 : diagOf gapTail4 ≡ canonicalDiag4
gapDiag4 = refl
gapRow4 : rowOf gapTail4 ≡ canonicalRow4
gapRow4 = refl
gapDiag5 : diagOf gapTail5 ≡ canonicalDiag5
gapDiag5 = refl
gapRow5 : rowOf gapTail5 ≡ canonicalRow5
gapRow5 = refl
gapDiag6 : diagOf gapTail6 ≡ canonicalDiag6
gapDiag6 = refl
gapRow6 : rowOf gapTail6 ≡ canonicalRow6
gapRow6 = refl
gapDiag7 : diagOf gapTail7 ≡ canonicalDiag7
gapDiag7 = refl
gapRow7 : rowOf gapTail7 ≡ canonicalRow7
gapRow7 = refl
gapDiag8 : diagOf gapTail8 ≡ canonicalDiag8
gapDiag8 = refl
gapRow8 : rowOf gapTail8 ≡ canonicalRow8
gapRow8 = refl
gapDiag9 : diagOf gapTail9 ≡ canonicalDiag9
gapDiag9 = refl
gapRow9 : rowOf gapTail9 ≡ canonicalRow9
gapRow9 = refl
gapDiag10 : diagOf gapTail10 ≡ canonicalDiag10
gapDiag10 = refl
gapRow10 : rowOf gapTail10 ≡ canonicalRow10
gapRow10 = refl
gapDiag11 : diagOf gapTail11 ≡ canonicalDiag11
gapDiag11 = refl
gapRow11 : rowOf gapTail11 ≡ canonicalRow11
gapRow11 = refl

ldlDiag0 : diagOf ldlTail0 ≡ canonicalDiag0
ldlDiag0 = refl
ldlRow0 : rowOf ldlTail0 ≡ canonicalRow0
ldlRow0 = refl
ldlDiag1 : diagOf ldlTail1 ≡ canonicalDiag1
ldlDiag1 = refl
ldlRow1 : rowOf ldlTail1 ≡ canonicalRow1
ldlRow1 = refl
ldlDiag2 : diagOf ldlTail2 ≡ canonicalDiag2
ldlDiag2 = refl
ldlRow2 : rowOf ldlTail2 ≡ canonicalRow2
ldlRow2 = refl
ldlDiag3 : diagOf ldlTail3 ≡ canonicalDiag3
ldlDiag3 = refl
ldlRow3 : rowOf ldlTail3 ≡ canonicalRow3
ldlRow3 = refl
ldlDiag4 : diagOf ldlTail4 ≡ canonicalDiag4
ldlDiag4 = refl
ldlRow4 : rowOf ldlTail4 ≡ canonicalRow4
ldlRow4 = refl
ldlDiag5 : diagOf ldlTail5 ≡ canonicalDiag5
ldlDiag5 = refl
ldlRow5 : rowOf ldlTail5 ≡ canonicalRow5
ldlRow5 = refl
ldlDiag6 : diagOf ldlTail6 ≡ canonicalDiag6
ldlDiag6 = refl
ldlRow6 : rowOf ldlTail6 ≡ canonicalRow6
ldlRow6 = refl
ldlDiag7 : diagOf ldlTail7 ≡ canonicalDiag7
ldlDiag7 = refl
ldlRow7 : rowOf ldlTail7 ≡ canonicalRow7
ldlRow7 = refl
ldlDiag8 : diagOf ldlTail8 ≡ canonicalDiag8
ldlDiag8 = refl
ldlRow8 : rowOf ldlTail8 ≡ canonicalRow8
ldlRow8 = refl
ldlDiag9 : diagOf ldlTail9 ≡ canonicalDiag9
ldlDiag9 = refl
ldlRow9 : rowOf ldlTail9 ≡ canonicalRow9
ldlRow9 = refl
ldlDiag10 : diagOf ldlTail10 ≡ canonicalDiag10
ldlDiag10 = refl
ldlRow10 : rowOf ldlTail10 ≡ canonicalRow10
ldlRow10 = refl
ldlDiag11 : diagOf ldlTail11 ≡ canonicalDiag11
ldlDiag11 = refl
ldlRow11 : rowOf ldlTail11 ≡ canonicalRow11
ldlRow11 = refl

------------------------------------------------------------------------
-- Reassemble the closed rows into whole quadratic objects.
------------------------------------------------------------------------

gapTail12Canonical : gapTail12 ≡ canonicalTail12
gapTail12Canonical = refl
gapTail11Canonical : gapTail11 ≡ canonicalTail11
gapTail11Canonical = Quad.qconsCong gapDiag11 gapRow11 gapTail12Canonical
gapTail10Canonical : gapTail10 ≡ canonicalTail10
gapTail10Canonical = Quad.qconsCong gapDiag10 gapRow10 gapTail11Canonical
gapTail9Canonical : gapTail9 ≡ canonicalTail9
gapTail9Canonical = Quad.qconsCong gapDiag9 gapRow9 gapTail10Canonical
gapTail8Canonical : gapTail8 ≡ canonicalTail8
gapTail8Canonical = Quad.qconsCong gapDiag8 gapRow8 gapTail9Canonical
gapTail7Canonical : gapTail7 ≡ canonicalTail7
gapTail7Canonical = Quad.qconsCong gapDiag7 gapRow7 gapTail8Canonical
gapTail6Canonical : gapTail6 ≡ canonicalTail6
gapTail6Canonical = Quad.qconsCong gapDiag6 gapRow6 gapTail7Canonical
gapTail5Canonical : gapTail5 ≡ canonicalTail5
gapTail5Canonical = Quad.qconsCong gapDiag5 gapRow5 gapTail6Canonical
gapTail4Canonical : gapTail4 ≡ canonicalTail4
gapTail4Canonical = Quad.qconsCong gapDiag4 gapRow4 gapTail5Canonical
gapTail3Canonical : gapTail3 ≡ canonicalTail3
gapTail3Canonical = Quad.qconsCong gapDiag3 gapRow3 gapTail4Canonical
gapTail2Canonical : gapTail2 ≡ canonicalTail2
gapTail2Canonical = Quad.qconsCong gapDiag2 gapRow2 gapTail3Canonical
gapTail1Canonical : gapTail1 ≡ canonicalTail1
gapTail1Canonical = Quad.qconsCong gapDiag1 gapRow1 gapTail2Canonical
gapTail0Canonical : gapTail0 ≡ canonicalTail0
gapTail0Canonical = Quad.qconsCong gapDiag0 gapRow0 gapTail1Canonical

ldlTail12Canonical : ldlTail12 ≡ canonicalTail12
ldlTail12Canonical = refl
ldlTail11Canonical : ldlTail11 ≡ canonicalTail11
ldlTail11Canonical = Quad.qconsCong ldlDiag11 ldlRow11 ldlTail12Canonical
ldlTail10Canonical : ldlTail10 ≡ canonicalTail10
ldlTail10Canonical = Quad.qconsCong ldlDiag10 ldlRow10 ldlTail11Canonical
ldlTail9Canonical : ldlTail9 ≡ canonicalTail9
ldlTail9Canonical = Quad.qconsCong ldlDiag9 ldlRow9 ldlTail10Canonical
ldlTail8Canonical : ldlTail8 ≡ canonicalTail8
ldlTail8Canonical = Quad.qconsCong ldlDiag8 ldlRow8 ldlTail9Canonical
ldlTail7Canonical : ldlTail7 ≡ canonicalTail7
ldlTail7Canonical = Quad.qconsCong ldlDiag7 ldlRow7 ldlTail8Canonical
ldlTail6Canonical : ldlTail6 ≡ canonicalTail6
ldlTail6Canonical = Quad.qconsCong ldlDiag6 ldlRow6 ldlTail7Canonical
ldlTail5Canonical : ldlTail5 ≡ canonicalTail5
ldlTail5Canonical = Quad.qconsCong ldlDiag5 ldlRow5 ldlTail6Canonical
ldlTail4Canonical : ldlTail4 ≡ canonicalTail4
ldlTail4Canonical = Quad.qconsCong ldlDiag4 ldlRow4 ldlTail5Canonical
ldlTail3Canonical : ldlTail3 ≡ canonicalTail3
ldlTail3Canonical = Quad.qconsCong ldlDiag3 ldlRow3 ldlTail4Canonical
ldlTail2Canonical : ldlTail2 ≡ canonicalTail2
ldlTail2Canonical = Quad.qconsCong ldlDiag2 ldlRow2 ldlTail3Canonical
ldlTail1Canonical : ldlTail1 ≡ canonicalTail1
ldlTail1Canonical = Quad.qconsCong ldlDiag1 ldlRow1 ldlTail2Canonical
ldlTail0Canonical : ldlTail0 ≡ canonicalTail0
ldlTail0Canonical = Quad.qconsCong ldlDiag0 ldlRow0 ldlTail1Canonical

gapTriEqualsLDLTri : gapTri ≡ ldlTri
gapTriEqualsLDLTri = trans gapTail0Canonical (sym ldlTail0Canonical)

------------------------------------------------------------------------
-- Compiler output: finite coefficient equality -> literal LDL decomposition.
------------------------------------------------------------------------

energyTriValue : ∀ c → Quad.evalTri energyTri (coordinates c) ≡ path13Energy c
energyTriValue c =
  trans (Quad.sumSquareCompiler energyFamilies (coordinates c)) (energyValuesMatch c)

normTriValue : ∀ c → Quad.evalTri normTri (coordinates c) ≡ path13NormSq c
normTriValue c =
  trans (Quad.sumSquareCompiler normFamilies (coordinates c)) (normValuesMatch c)

ldlTriValue : ∀ c → Quad.evalTri ldlTri (coordinates c) ≡ sumTermValues path13Terms c
ldlTriValue c =
  trans (Quad.sumWeightedSquareCompiler ldlFamilies (coordinates c)) (ldlValuesMatch c)

gapArithmetic : ∀ energyValue normValue →
  energyValue + (- oneEighteenth) * normValue
  ≡ energyValue - oneEighteenth * normValue
gapArithmetic = ℚRing.solve-∀

gapTriValue : ∀ c →
  Quad.evalTri gapTri (coordinates c)
  ≡ path13Energy c - oneEighteenth * path13NormSq c
gapTriValue c =
  trans
    (Quad.evalAdd energyTri (Quad.scaleTri (- oneEighteenth) normTri) (coordinates c))
    (trans
      (cong (λ right → Quad.evalTri energyTri (coordinates c) + right)
        (Quad.evalScale (- oneEighteenth) normTri (coordinates c)))
      (trans
        (cong (λ energyValue →
          energyValue + (- oneEighteenth) * Quad.evalTri normTri (coordinates c))
          (energyTriValue c))
        (trans
          (cong (λ normValue → path13Energy c + (- oneEighteenth) * normValue)
            (normTriValue c))
          (gapArithmetic (path13Energy c) (path13NormSq c)))))

path13GapToTerms : ∀ c →
  path13Energy c - oneEighteenth * path13NormSq c
  ≡ sumTermValues path13Terms c
path13GapToTerms c =
  trans (sym (gapTriValue c))
    (trans
      (cong (λ quadratic → Quad.evalTri quadratic (coordinates c)) gapTriEqualsLDLTri)
      (ldlTriValue c))

recomposeIdentity : ∀ energyValue normValue constant →
  energyValue ≡ constant * normValue + (energyValue - constant * normValue)
recomposeIdentity = ℚRing.solve-∀

path13LDLDecomposition : ∀ c →
  path13Energy c
  ≡ oneEighteenth * path13NormSq c + sumTermValues path13Terms c
path13LDLDecomposition c =
  trans
    (recomposeIdentity (path13Energy c) (path13NormSq c) oneEighteenth)
    (cong
      (λ remainder → oneEighteenth * path13NormSq c + remainder)
      (path13GapToTerms c))

path13LDLCertificate : RationalLDLCertificate Path13Coordinates
path13LDLCertificate = record
  { normSq = path13NormSq
  ; energy = path13Energy
  ; coercivityConstant = oneEighteenth
  ; terms = path13Terms
  ; decomposition = path13LDLDecomposition
  }

path13Poincare : ∀ c → oneEighteenth * path13NormSq c ≤ path13Energy c
path13Poincare = ldlCertificatePoincare path13LDLCertificate

path13CoefficientCertificateLevel : ProofLevel
path13CoefficientCertificateLevel = machineChecked
