module DASHI.Physics.YangMills.BalabanPath13ScaledIntegerCoefficientDataExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Product using (_×_; _,_)
open import Data.Rational using (ℚ; 0ℚ; _*_; -_; _/_)
open import DASHI.Physics.YangMills.BalabanPath13GeneratedLDLDataExact public
import DASHI.Physics.YangMills.BalabanTriangularQuadraticCertificateExact as Quad

------------------------------------------------------------------------
-- Common-denominator Path13 certificate data.
--
-- Every coefficient in the closed quadratic check has denominator one.
-- The huge rational LDL coefficients are cleared externally once; Agda only
-- combines integer-valued rationals here.  This prevents closed coefficient
-- evaluation from entering large-denominator gcd normalization.
------------------------------------------------------------------------

pos : Nat → ℚ
pos n = + n / 1

neg : Nat → ℚ
neg n = - pos n

eighteenℚ : ℚ
eighteenℚ = pos 18

scaleK : ℚ
scaleK = pos 70100214151882488833120838983750438907686861074695467566355130758678976489785281281004080

-- scaleM = 18 * scaleK; this is the common integer scaling M.
scaleM : ℚ
scaleM = eighteenℚ * scaleK

coordinates : Path13Coordinates → List ℚ
coordinates c =
  y0 c ∷ y1 c ∷ y2 c ∷ y3 c ∷ y4 c ∷ y5 c ∷
  y6 c ∷ y7 c ∷ y8 c ∷ y9 c ∷ y10 c ∷ y11 c ∷ []

energy0Coefficients : List ℚ
energy0Coefficients = neg 1 ∷ pos 1 ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
energy1Coefficients : List ℚ
energy1Coefficients = 0ℚ ∷ neg 1 ∷ pos 1 ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
energy2Coefficients : List ℚ
energy2Coefficients = 0ℚ ∷ 0ℚ ∷ neg 1 ∷ pos 1 ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
energy3Coefficients : List ℚ
energy3Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ neg 1 ∷ pos 1 ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
energy4Coefficients : List ℚ
energy4Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ neg 1 ∷ pos 1 ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
energy5Coefficients : List ℚ
energy5Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ neg 1 ∷ pos 1 ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
energy6Coefficients : List ℚ
energy6Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ neg 1 ∷ pos 1 ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
energy7Coefficients : List ℚ
energy7Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ neg 1 ∷ pos 1 ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
energy8Coefficients : List ℚ
energy8Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ neg 1 ∷ pos 1 ∷ 0ℚ ∷ 0ℚ ∷ []
energy9Coefficients : List ℚ
energy9Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ neg 1 ∷ pos 1 ∷ 0ℚ ∷ []
energy10Coefficients : List ℚ
energy10Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ neg 1 ∷ pos 1 ∷ []
energy11Coefficients : List ℚ
energy11Coefficients = neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 2 ∷ []

norm0Coefficients : List ℚ
norm0Coefficients = pos 1 ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
norm1Coefficients : List ℚ
norm1Coefficients = 0ℚ ∷ pos 1 ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
norm2Coefficients : List ℚ
norm2Coefficients = 0ℚ ∷ 0ℚ ∷ pos 1 ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
norm3Coefficients : List ℚ
norm3Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ pos 1 ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
norm4Coefficients : List ℚ
norm4Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ pos 1 ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
norm5Coefficients : List ℚ
norm5Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ pos 1 ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
norm6Coefficients : List ℚ
norm6Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ pos 1 ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
norm7Coefficients : List ℚ
norm7Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ pos 1 ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
norm8Coefficients : List ℚ
norm8Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ pos 1 ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ []
norm9Coefficients : List ℚ
norm9Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ pos 1 ∷ 0ℚ ∷ 0ℚ ∷ []
norm10Coefficients : List ℚ
norm10Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ pos 1 ∷ 0ℚ ∷ []
norm11Coefficients : List ℚ
norm11Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ pos 1 ∷ []
norm12Coefficients : List ℚ
norm12Coefficients = neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ []

scaledForm0Coefficients : List ℚ
scaledForm0Coefficients = pos 34 ∷ neg 1 ∷ pos 17 ∷ pos 17 ∷ pos 17 ∷ pos 17 ∷ pos 17 ∷ pos 17 ∷ pos 17 ∷ pos 17 ∷ pos 17 ∷ pos 35 ∷ []
scaledForm1Coefficients : List ℚ
scaledForm1Coefficients = 0ℚ ∷ pos 1767 ∷ neg 17 ∷ pos 595 ∷ pos 595 ∷ pos 595 ∷ pos 595 ∷ pos 595 ∷ pos 595 ∷ pos 595 ∷ pos 595 ∷ pos 1225 ∷ []
scaledForm2Coefficients : List ℚ
scaledForm2Coefficients = 0ℚ ∷ 0ℚ ∷ pos 76856 ∷ neg 16489 ∷ pos 15317 ∷ pos 15317 ∷ pos 15317 ∷ pos 15317 ∷ pos 15317 ∷ pos 15317 ∷ pos 15317 ∷ pos 31535 ∷ []
scaledForm3Coefficients : List ℚ
scaledForm3Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ pos 2736473 ∷ neg 1040093 ∷ pos 343315 ∷ pos 343315 ∷ pos 343315 ∷ pos 343315 ∷ pos 343315 ∷ pos 343315 ∷ pos 706825 ∷ []
scaledForm4Coefficients : List ℚ
scaledForm4Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ pos 84108198 ∷ neg 42203197 ∷ pos 7053317 ∷ pos 7053317 ∷ pos 7053317 ∷ pos 7053317 ∷ pos 7053317 ∷ pos 14521535 ∷ []
scaledForm5Coefficients : List ℚ
scaledForm5Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ pos 2319761419 ∷ neg 1378315529 ∷ pos 135632035 ∷ pos 135632035 ∷ pos 135632035 ∷ pos 135632035 ∷ pos 279242425 ∷ []
scaledForm6Coefficients : List ℚ
scaledForm6Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ pos 58843816660 ∷ neg 39293859025 ∷ pos 2461846517 ∷ pos 2461846517 ∷ pos 2461846517 ∷ pos 5068507535 ∷ []
scaledForm7Coefficients : List ℚ
scaledForm7Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ pos 278892793881 ∷ neg 203393770225 ∷ pos 8443969751 ∷ pos 8443969751 ∷ pos 17384643605 ∷ []
scaledForm8Coefficients : List ℚ
scaledForm8Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ pos 1641097686518 ∷ neg 1285278684967 ∷ pos 35792443943 ∷ pos 73690325765 ∷ []
scaledForm9Coefficients : List ℚ
scaledForm9Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ pos 661887395501231 ∷ neg 551132664563681 ∷ pos 20840943993625 ∷ []
scaledForm10Coefficients : List ℚ
scaledForm10Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ pos 13379628643375344 ∷ neg 11638177724654623 ∷ []
scaledForm11Coefficients : List ℚ
scaledForm11Coefficients = 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ 0ℚ ∷ pos 1 ∷ []

weight0 : ℚ
weight0 = pos 2061771004467132024503554087757365850226084149255749046069268551725852249699567096500120
weight1 : ℚ
weight1 = pos 1166820036483945684495503162284870317049283615877616890814526628028212931352329992360
weight2 : ℚ
weight2 = pos 516184569070133148652637497627844160243515703911717683560085163851348491542354790
weight3 : ℚ
weight3 = pos 333311577913220877263985596900974587050664212222084832136355989818036861520410
weight4 : ℚ
weight4 = pos 304571911433633422309212676693195862576509470510122590650102573276567416520
weight5 : ℚ
weight5 = pos 359283849351979050241613722186255465805006820960171635652182617406418840
weight6 : ℚ
weight6 = pos 513541079670314261521825542054473656850485861884756032842578615922452
weight7 : ℚ
weight7 = pos 21357539703932072702412498496181071098644299249140047543595620925740
weight8 : ℚ
weight8 = pos 582011029774935626619634825519095089613274052507535637487672892088
weight9 : ℚ
weight9 = pos 3396621855440594756988773113168811067316871714047695079112040
weight10 : ℚ
weight10 = pos 7915733682361932346419013108004980848910522080156599162595
weight11 : ℚ
weight11 = pos 23654724725960859118550599727273560507275252328952867480395816966937511364540065812424285

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

scaledLDLFamilies : List (ℚ × List ℚ)
scaledLDLFamilies =
  (weight0 , scaledForm0Coefficients)
  ∷   (weight1 , scaledForm1Coefficients)
  ∷   (weight2 , scaledForm2Coefficients)
  ∷   (weight3 , scaledForm3Coefficients)
  ∷   (weight4 , scaledForm4Coefficients)
  ∷   (weight5 , scaledForm5Coefficients)
  ∷   (weight6 , scaledForm6Coefficients)
  ∷   (weight7 , scaledForm7Coefficients)
  ∷   (weight8 , scaledForm8Coefficients)
  ∷   (weight9 , scaledForm9Coefficients)
  ∷   (weight10 , scaledForm10Coefficients)
  ∷   (weight11 , scaledForm11Coefficients)
  ∷ []

energyTri : Quad.TriQuadratic
energyTri = Quad.sumSquareTri energyFamilies

normTri : Quad.TriQuadratic
normTri = Quad.sumSquareTri normFamilies

scaledGapTri : Quad.TriQuadratic
scaledGapTri =
  Quad.addTri
    (Quad.scaleTri scaleM energyTri)
    (Quad.scaleTri (- scaleK) normTri)

scaledLDLTri : Quad.TriQuadratic
scaledLDLTri = Quad.sumWeightedSquareTri scaledLDLFamilies
