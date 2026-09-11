module DASHI.Physics.YangMills.BalabanPath13QuadraticCoefficientDataExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _/_)
open import DASHI.Physics.YangMills.BalabanPath13GeneratedLDLDataExact public
import DASHI.Physics.YangMills.BalabanTriangularQuadraticCertificateExact as Quad

twoℚ : ℚ
twoℚ = 1ℚ + 1ℚ

coordinates : Path13Coordinates → List ℚ
coordinates c =
  y0 c ∷ y1 c ∷ y2 c ∷ y3 c ∷ y4 c ∷ y5 c ∷
  y6 c ∷ y7 c ∷ y8 c ∷ y9 c ∷ y10 c ∷ y11 c ∷ []

energy0Coefficients energy1Coefficients energy2Coefficients energy3Coefficients : List ℚ
energy4Coefficients energy5Coefficients energy6Coefficients energy7Coefficients : List ℚ
energy8Coefficients energy9Coefficients energy10Coefficients energy11Coefficients : List ℚ
energy0Coefficients = (- 1ℚ) ∷ 1ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
energy1Coefficients = 0ℚ ∷ (- 1ℚ) ∷ 1ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
energy2Coefficients = 0ℚ ∷ 0ℚ ∷ (- 1ℚ) ∷ 1ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
energy3Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ (- 1ℚ) ∷ 1ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
energy4Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ (- 1ℚ) ∷ 1ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
energy5Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ (- 1ℚ) ∷ 1ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
energy6Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ (- 1ℚ) ∷ 1ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
energy7Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ (- 1ℚ) ∷ 1ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
energy8Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ (- 1ℚ) ∷ 1ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
energy9Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ (- 1ℚ) ∷ 1ℚ ∷ 0ℚ ∷ []
energy10Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ (- 1ℚ) ∷ 1ℚ ∷ []
energy11Coefficients = (- 1ℚ) ∷ (- 1ℚ) ∷ (- 1ℚ) ∷ (- 1ℚ) ∷ (- 1ℚ) ∷ (- 1ℚ) ∷ (- 1ℚ) ∷ (- 1ℚ) ∷ (- 1ℚ) ∷ (- 1ℚ) ∷ (- 1ℚ) ∷ (- twoℚ) ∷ []

norm0Coefficients norm1Coefficients norm2Coefficients norm3Coefficients : List ℚ
norm4Coefficients norm5Coefficients norm6Coefficients norm7Coefficients : List ℚ
norm8Coefficients norm9Coefficients norm10Coefficients norm11Coefficients norm12Coefficients : List ℚ
norm0Coefficients = 1ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
norm1Coefficients = 0ℚ ∷ 1ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
norm2Coefficients = 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
norm3Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
norm4Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
norm5Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
norm6Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
norm7Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
norm8Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
norm9Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
norm10Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ 0ℚ ∷ []
norm11Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ []
norm12Coefficients = (- 1ℚ) ∷ (- 1ℚ) ∷ (- 1ℚ) ∷ (- 1ℚ) ∷ (- 1ℚ) ∷ (- 1ℚ) ∷ (- 1ℚ) ∷ (- 1ℚ) ∷ (- 1ℚ) ∷ (- 1ℚ) ∷ (- 1ℚ) ∷ (- 1ℚ) ∷ []

form0Coefficients form1Coefficients form2Coefficients form3Coefficients : List ℚ
form4Coefficients form5Coefficients form6Coefficients form7Coefficients : List ℚ
form8Coefficients form9Coefficients form10Coefficients form11Coefficients : List ℚ
form0Coefficients = 1ℚ ∷ (- (+ 1 / 34)) ∷ (+ 1 / 2) ∷ (+ 1 / 2) ∷ (+ 1 / 2) ∷ (+ 1 / 2) ∷ (+ 1 / 2) ∷ (+ 1 / 2) ∷ (+ 1 / 2) ∷ (+ 1 / 2) ∷ (+ 1 / 2) ∷ (+ 35 / 34) ∷ []
form1Coefficients = 0ℚ ∷ 1ℚ ∷ (- (+ 17 / 1767)) ∷ (+ 595 / 1767) ∷ (+ 595 / 1767) ∷ (+ 595 / 1767) ∷ (+ 595 / 1767) ∷ (+ 595 / 1767) ∷ (+ 595 / 1767) ∷ (+ 595 / 1767) ∷ (+ 595 / 1767) ∷ (+ 1225 / 1767) ∷ []
form2Coefficients = 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ (- (+ 16489 / 76856)) ∷ (+ 15317 / 76856) ∷ (+ 15317 / 76856) ∷ (+ 15317 / 76856) ∷ (+ 15317 / 76856) ∷ (+ 15317 / 76856) ∷ (+ 15317 / 76856) ∷ (+ 15317 / 76856) ∷ (+ 31535 / 76856) ∷ []
form3Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ (- (+ 1040093 / 2736473)) ∷ (+ 20195 / 160969) ∷ (+ 20195 / 160969) ∷ (+ 20195 / 160969) ∷ (+ 20195 / 160969) ∷ (+ 20195 / 160969) ∷ (+ 20195 / 160969) ∷ (+ 706825 / 2736473) ∷ []
form4Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ (- (+ 42203197 / 84108198)) ∷ (+ 7053317 / 84108198) ∷ (+ 7053317 / 84108198) ∷ (+ 7053317 / 84108198) ∷ (+ 7053317 / 84108198) ∷ (+ 7053317 / 84108198) ∷ (+ 14521535 / 84108198) ∷ []
form5Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ (- (+ 1378315529 / 2319761419)) ∷ (+ 135632035 / 2319761419) ∷ (+ 135632035 / 2319761419) ∷ (+ 135632035 / 2319761419) ∷ (+ 135632035 / 2319761419) ∷ (+ 279242425 / 2319761419) ∷ []
form6Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ (- (+ 7858771805 / 11768763332)) ∷ (+ 144814501 / 3461400980) ∷ (+ 144814501 / 3461400980) ∷ (+ 144814501 / 3461400980) ∷ (+ 1013701507 / 11768763332) ∷ []
form7Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ (- (+ 10704935275 / 14678568099)) ∷ (+ 8443969751 / 278892793881) ∷ (+ 8443969751 / 278892793881) ∷ (+ 17384643605 / 278892793881) ∷ []
form8Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ (- (+ 1285278684967 / 1641097686518)) ∷ (+ 35792443943 / 1641097686518) ∷ (+ 73690325765 / 1641097686518) ∷ []
form9Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ (- (+ 551132664563681 / 661887395501231)) ∷ (+ 20840943993625 / 661887395501231) ∷ []
form10Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ (- (+ 11638177724654623 / 13379628643375344)) ∷ []
form11Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 1ℚ ∷ []

energyFamilies : List (List ℚ)
energyFamilies =
  energy0Coefficients ∷ energy1Coefficients ∷ energy2Coefficients ∷
  energy3Coefficients ∷ energy4Coefficients ∷ energy5Coefficients ∷
  energy6Coefficients ∷ energy7Coefficients ∷ energy8Coefficients ∷
  energy9Coefficients ∷ energy10Coefficients ∷ energy11Coefficients ∷ []

normFamilies : List (List ℚ)
normFamilies =
  norm0Coefficients ∷ norm1Coefficients ∷ norm2Coefficients ∷
  norm3Coefficients ∷ norm4Coefficients ∷ norm5Coefficients ∷
  norm6Coefficients ∷ norm7Coefficients ∷ norm8Coefficients ∷
  norm9Coefficients ∷ norm10Coefficients ∷ norm11Coefficients ∷
  norm12Coefficients ∷ []

ldlFamilies : List (ℚ × List ℚ)
ldlFamilies =
  (pivot0 , form0Coefficients) ∷ (pivot1 , form1Coefficients) ∷
  (pivot2 , form2Coefficients) ∷ (pivot3 , form3Coefficients) ∷
  (pivot4 , form4Coefficients) ∷ (pivot5 , form5Coefficients) ∷
  (pivot6 , form6Coefficients) ∷ (pivot7 , form7Coefficients) ∷
  (pivot8 , form8Coefficients) ∷ (pivot9 , form9Coefficients) ∷
  (pivot10 , form10Coefficients) ∷ (pivot11 , form11Coefficients) ∷ []

energyTri normTri gapTri ldlTri : Quad.TriQuadratic
energyTri = Quad.sumSquareTri energyFamilies
normTri = Quad.sumSquareTri normFamilies
gapTri = Quad.addTri energyTri (Quad.scaleTri (- oneEighteenth) normTri)
ldlTri = Quad.sumWeightedSquareTri ldlFamilies
