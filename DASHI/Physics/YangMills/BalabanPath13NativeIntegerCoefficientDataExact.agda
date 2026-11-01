module DASHI.Physics.YangMills.BalabanPath13NativeIntegerCoefficientDataExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer using (ℤ; +_; -_)
open import Data.Product using (_×_; _,_)

import DASHI.Physics.YangMills.BalabanIntegerTriangularQuadraticCertificateExact as QuadZ

pos : Nat → ℤ
pos n = + n

neg : Nat → ℤ
neg n = - (+ n)

zeroZ : ℤ
zeroZ = pos 0

scaleKZ : ℤ
scaleKZ = pos 70100214151882488833120838983750438907686861074695467566355130758678976489785281281004080

scaleMZ : ℤ
scaleMZ = pos 1261803854733884798996175101707507900338363499344518416194392353656221576816135063058073440

energy0CoefficientsZ : List ℤ
energy0CoefficientsZ = neg 1 ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []
energy1CoefficientsZ : List ℤ
energy1CoefficientsZ = zeroZ ∷ neg 1 ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []
energy2CoefficientsZ : List ℤ
energy2CoefficientsZ = zeroZ ∷ zeroZ ∷ neg 1 ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []
energy3CoefficientsZ : List ℤ
energy3CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ neg 1 ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []
energy4CoefficientsZ : List ℤ
energy4CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ neg 1 ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []
energy5CoefficientsZ : List ℤ
energy5CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ neg 1 ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []
energy6CoefficientsZ : List ℤ
energy6CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ neg 1 ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []
energy7CoefficientsZ : List ℤ
energy7CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ neg 1 ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []
energy8CoefficientsZ : List ℤ
energy8CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ neg 1 ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ []
energy9CoefficientsZ : List ℤ
energy9CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ neg 1 ∷ pos 1 ∷ zeroZ ∷ []
energy10CoefficientsZ : List ℤ
energy10CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ neg 1 ∷ pos 1 ∷ []
energy11CoefficientsZ : List ℤ
energy11CoefficientsZ = neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 2 ∷ []

norm0CoefficientsZ : List ℤ
norm0CoefficientsZ = pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []
norm1CoefficientsZ : List ℤ
norm1CoefficientsZ = zeroZ ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []
norm2CoefficientsZ : List ℤ
norm2CoefficientsZ = zeroZ ∷ zeroZ ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []
norm3CoefficientsZ : List ℤ
norm3CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []
norm4CoefficientsZ : List ℤ
norm4CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []
norm5CoefficientsZ : List ℤ
norm5CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []
norm6CoefficientsZ : List ℤ
norm6CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []
norm7CoefficientsZ : List ℤ
norm7CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []
norm8CoefficientsZ : List ℤ
norm8CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ []
norm9CoefficientsZ : List ℤ
norm9CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ pos 1 ∷ zeroZ ∷ zeroZ ∷ []
norm10CoefficientsZ : List ℤ
norm10CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ pos 1 ∷ zeroZ ∷ []
norm11CoefficientsZ : List ℤ
norm11CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ pos 1 ∷ []
norm12CoefficientsZ : List ℤ
norm12CoefficientsZ = neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ neg 1 ∷ []

scaledForm0CoefficientsZ : List ℤ
scaledForm0CoefficientsZ = pos 34 ∷ neg 1 ∷ pos 17 ∷ pos 17 ∷ pos 17 ∷ pos 17 ∷ pos 17 ∷ pos 17 ∷ pos 17 ∷ pos 17 ∷ pos 17 ∷ pos 35 ∷ []
scaledForm1CoefficientsZ : List ℤ
scaledForm1CoefficientsZ = zeroZ ∷ pos 1767 ∷ neg 17 ∷ pos 595 ∷ pos 595 ∷ pos 595 ∷ pos 595 ∷ pos 595 ∷ pos 595 ∷ pos 595 ∷ pos 595 ∷ pos 1225 ∷ []
scaledForm2CoefficientsZ : List ℤ
scaledForm2CoefficientsZ = zeroZ ∷ zeroZ ∷ pos 76856 ∷ neg 16489 ∷ pos 15317 ∷ pos 15317 ∷ pos 15317 ∷ pos 15317 ∷ pos 15317 ∷ pos 15317 ∷ pos 15317 ∷ pos 31535 ∷ []
scaledForm3CoefficientsZ : List ℤ
scaledForm3CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ pos 2736473 ∷ neg 1040093 ∷ pos 343315 ∷ pos 343315 ∷ pos 343315 ∷ pos 343315 ∷ pos 343315 ∷ pos 343315 ∷ pos 706825 ∷ []
scaledForm4CoefficientsZ : List ℤ
scaledForm4CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ pos 84108198 ∷ neg 42203197 ∷ pos 7053317 ∷ pos 7053317 ∷ pos 7053317 ∷ pos 7053317 ∷ pos 7053317 ∷ pos 14521535 ∷ []
scaledForm5CoefficientsZ : List ℤ
scaledForm5CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ pos 2319761419 ∷ neg 1378315529 ∷ pos 135632035 ∷ pos 135632035 ∷ pos 135632035 ∷ pos 135632035 ∷ pos 279242425 ∷ []
scaledForm6CoefficientsZ : List ℤ
scaledForm6CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ pos 58843816660 ∷ neg 39293859025 ∷ pos 2461846517 ∷ pos 2461846517 ∷ pos 2461846517 ∷ pos 5068507535 ∷ []
scaledForm7CoefficientsZ : List ℤ
scaledForm7CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ pos 278892793881 ∷ neg 203393770225 ∷ pos 8443969751 ∷ pos 8443969751 ∷ pos 17384643605 ∷ []
scaledForm8CoefficientsZ : List ℤ
scaledForm8CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ pos 1641097686518 ∷ neg 1285278684967 ∷ pos 35792443943 ∷ pos 73690325765 ∷ []
scaledForm9CoefficientsZ : List ℤ
scaledForm9CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ pos 661887395501231 ∷ neg 551132664563681 ∷ pos 20840943993625 ∷ []
scaledForm10CoefficientsZ : List ℤ
scaledForm10CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ pos 13379628643375344 ∷ neg 11638177724654623 ∷ []
scaledForm11CoefficientsZ : List ℤ
scaledForm11CoefficientsZ = zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ zeroZ ∷ pos 1 ∷ []

weight0Z : ℤ
weight0Z = pos 2061771004467132024503554087757365850226084149255749046069268551725852249699567096500120
weight1Z : ℤ
weight1Z = pos 1166820036483945684495503162284870317049283615877616890814526628028212931352329992360
weight2Z : ℤ
weight2Z = pos 516184569070133148652637497627844160243515703911717683560085163851348491542354790
weight3Z : ℤ
weight3Z = pos 333311577913220877263985596900974587050664212222084832136355989818036861520410
weight4Z : ℤ
weight4Z = pos 304571911433633422309212676693195862576509470510122590650102573276567416520
weight5Z : ℤ
weight5Z = pos 359283849351979050241613722186255465805006820960171635652182617406418840
weight6Z : ℤ
weight6Z = pos 513541079670314261521825542054473656850485861884756032842578615922452
weight7Z : ℤ
weight7Z = pos 21357539703932072702412498496181071098644299249140047543595620925740
weight8Z : ℤ
weight8Z = pos 582011029774935626619634825519095089613274052507535637487672892088
weight9Z : ℤ
weight9Z = pos 3396621855440594756988773113168811067316871714047695079112040
weight10Z : ℤ
weight10Z = pos 7915733682361932346419013108004980848910522080156599162595
weight11Z : ℤ
weight11Z = pos 23654724725960859118550599727273560507275252328952867480395816966937511364540065812424285

energyFamiliesZ : List (List ℤ)
energyFamiliesZ =
  energy0CoefficientsZ ∷ energy1CoefficientsZ ∷ energy2CoefficientsZ ∷
  energy3CoefficientsZ ∷ energy4CoefficientsZ ∷ energy5CoefficientsZ ∷
  energy6CoefficientsZ ∷ energy7CoefficientsZ ∷ energy8CoefficientsZ ∷
  energy9CoefficientsZ ∷ energy10CoefficientsZ ∷ energy11CoefficientsZ ∷ []

normFamiliesZ : List (List ℤ)
normFamiliesZ =
  norm0CoefficientsZ ∷ norm1CoefficientsZ ∷ norm2CoefficientsZ ∷
  norm3CoefficientsZ ∷ norm4CoefficientsZ ∷ norm5CoefficientsZ ∷
  norm6CoefficientsZ ∷ norm7CoefficientsZ ∷ norm8CoefficientsZ ∷
  norm9CoefficientsZ ∷ norm10CoefficientsZ ∷ norm11CoefficientsZ ∷
  norm12CoefficientsZ ∷ []

scaledLDLFamiliesZ : List (ℤ × List ℤ)
scaledLDLFamiliesZ =
  (weight0Z , scaledForm0CoefficientsZ)
  ∷ (weight1Z , scaledForm1CoefficientsZ)
  ∷ (weight2Z , scaledForm2CoefficientsZ)
  ∷ (weight3Z , scaledForm3CoefficientsZ)
  ∷ (weight4Z , scaledForm4CoefficientsZ)
  ∷ (weight5Z , scaledForm5CoefficientsZ)
  ∷ (weight6Z , scaledForm6CoefficientsZ)
  ∷ (weight7Z , scaledForm7CoefficientsZ)
  ∷ (weight8Z , scaledForm8CoefficientsZ)
  ∷ (weight9Z , scaledForm9CoefficientsZ)
  ∷ (weight10Z , scaledForm10CoefficientsZ)
  ∷ (weight11Z , scaledForm11CoefficientsZ)
  ∷ []

energyTriZ : QuadZ.TriQuadraticZ
energyTriZ = QuadZ.sumSquareTriZ energyFamiliesZ

normTriZ : QuadZ.TriQuadraticZ
normTriZ = QuadZ.sumSquareTriZ normFamiliesZ

scaledGapTriZ : QuadZ.TriQuadraticZ
scaledGapTriZ =
  QuadZ.addTriZ
    (QuadZ.scaleTriZ scaleMZ energyTriZ)
    (QuadZ.scaleTriZ (neg 70100214151882488833120838983750438907686861074695467566355130758678976489785281281004080) normTriZ)

scaledLDLTriZ : QuadZ.TriQuadraticZ
scaledLDLTriZ = QuadZ.sumWeightedSquareTriZ scaledLDLFamiliesZ
