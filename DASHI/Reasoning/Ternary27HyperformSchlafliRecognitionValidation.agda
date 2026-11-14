module DASHI.Reasoning.Ternary27HyperformSchlafliRecognitionValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Reasoning.Ternary27HyperformSchlafliRecognitionExact as S

chartCount : S.schlafliChartCount ≡ 27
chartCount = S.schlafliChartCountIs27

originRoundTrip :
  S.schlafliLabelToPoint (S.pointToSchlafliLabel Geometry.origin) ≡ Geometry.origin
originRoundTrip = S.pointAfterLabel Geometry.origin

usesExistingCarrier :
  S.usesExistingTernary27Point S.canonicalTernary27HyperformSchlafliBoundary ≡ true
usesExistingCarrier = refl

usesExistingFaces :
  S.usesExistingSixOrientedFaces S.canonicalTernary27HyperformSchlafliBoundary ≡ true
usesExistingFaces = refl

chartPaid :
  S.exactSixPlusFifteenPlusSixChartPaid S.canonicalTernary27HyperformSchlafliBoundary ≡ true
chartPaid = refl

bijectionPaid :
  S.chartTwoSidedBijectionPaidInAgda S.canonicalTernary27HyperformSchlafliBoundary ≡ true
bijectionPaid = refl

leanRelationProducerRecorded :
  S.leanSchlafliSRGProducerSourceWritten S.canonicalTernary27HyperformSchlafliBoundary ≡ true
leanRelationProducerRecorded = refl

translationInvarianceNotRequired :
  S.additiveTranslationInvarianceRequired S.canonicalTernary27HyperformSchlafliBoundary ≡ false
translationInvarianceNotRequired = refl

rawE6ActionNotInvented :
  S.independentRawTernaryE6ActionPaid S.canonicalTernary27HyperformSchlafliBoundary ≡ false
rawE6ActionNotInvented = refl

albertProductNotInvented :
  S.albertJordanProductPaid S.canonicalTernary27HyperformSchlafliBoundary ≡ false
albertProductNotInvented = refl

agdaSRGNotInvented :
  S.agdaSRGEnumerationKernelPaidHere S.canonicalTernary27HyperformSchlafliBoundary ≡ false
agdaSRGNotInvented = refl
