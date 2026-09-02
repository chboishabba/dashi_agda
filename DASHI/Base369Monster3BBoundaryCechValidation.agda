module DASHI.Base369Monster3BBoundaryCechValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.Base369Ternary27BoundaryNerveExact as Nerve
import DASHI.Moonshine.Base369Ternary27FaceHypercubeCechGluingBidiExact as Cech
import DASHI.Moonshine.Base369Monster3BZetaFaceHypercubeGluingCompilerExact as Compiler
import DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound14Exact as Round14

edgeCountIsTwelve : Nerve.edgeCount ≡ 12
edgeCountIsTwelve = refl

cornerCountIsEight : Nerve.cornerCount ≡ 8
cornerCountIsEight = refl

modelGluingDoesNotPromoteMonsterByItself :
  Cech.FaceHypercubeCechBoundary.modelGluingImpliesActualMonsterGluing
    Cech.canonicalFaceHypercubeCechBoundary ≡ false
modelGluingDoesNotPromoteMonsterByItself = refl

faceGluingPaymentPrunedAfterZeta :
  Round14.Round14Status.separateFaceGluingPaymentAfterZetaRecognition
    Round14.canonicalRound14Status ≡ false
faceGluingPaymentPrunedAfterZeta = refl

fullNormalizerGluingStillLive :
  Round14.Round14Status.fullMonsterNormalizerFaceGluingOwned
    Round14.canonicalRound14Status ≡ false
fullNormalizerGluingStillLive = refl

zetaCompilerDoesNotConstructRecognition :
  Compiler.ZetaFaceGluingCompilerBoundary.actualZetaRecognitionConstructedHere
    Compiler.canonicalZetaFaceGluingCompilerBoundary ≡ false
zetaCompilerDoesNotConstructRecognition = refl
