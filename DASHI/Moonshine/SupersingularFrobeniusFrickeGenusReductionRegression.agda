module DASHI.Moonshine.SupersingularFrobeniusFrickeGenusReductionRegression where

------------------------------------------------------------------------
-- Three source-facing geometric calibration points for the generic reduction.
--
-- Actual supersingular Frobenius geometry already constructed in-repo gives:
--
--   p=11 : total 2, rational 2, pairs 0
--   p=37 : total 3, rational 1, pairs 1
--   p=43 : total 4, rational 2, pairs 1.
--
-- The existing exact Fricke rows give the corresponding (g0,g+,R):
--
--   p=11 : (1,0,4)
--   p=37 : (2,1,2)
--   p=43 : (3,1,4).
--
-- This file shows that all three instantiate ONE generic algebraic reduction.
-- It remains a calibration: the Fricke rows use the existing class-number
-- input family, so these three instances do not replace the missing global
-- geometric proof of R = 2 r or S = g0+1.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.PrimeFrickeGenusControlExact as Fricke
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.P11GeometricFrobeniusRealizationExact as P11
import DASHI.Moonshine.P37SageSupersingularFrobeniusExact as P37
import DASHI.Moonshine.P43NonOggFullLevel2DeuringControlExact as P43
import DASHI.Moonshine.P43GeometricFrobeniusRealizationExact as P43Geo
import DASHI.Moonshine.SupersingularFrobeniusFrickeGenusReductionExact as Reduce

p11CountData : Reduce.SupersingularFrickeCountData
p11CountData = record
  { Reduce.totalSupersingular = 2
  ; Reduce.rationalSupersingular = 2
  ; Reduce.frobeniusPairDefect = 0
  ; Reduce.genusX0 = Fricke.genusX0 (Fricke.frickeRow Matrix.prime11)
  ; Reduce.genusX0Plus = Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime11)
  ; Reduce.frickeFixedPoints = Fricke.frickeFixedPointCount (Fricke.frickeRow Matrix.prime11)
  ; Reduce.totalIsGenusPlusOne = refl
  ; Reduce.frobeniusOrbitDecomposition = refl
  ; Reduce.frickeFixedDoubleRational = refl
  ; Reduce.frickeRiemannHurwitz = Fricke.riemannHurwitzFormula (Fricke.frickeRow Matrix.prime11)
  }

p37CountData : Reduce.SupersingularFrickeCountData
p37CountData = record
  { Reduce.totalSupersingular = 3
  ; Reduce.rationalSupersingular = 1
  ; Reduce.frobeniusPairDefect = 1
  ; Reduce.genusX0 = Fricke.genusX0 (Fricke.frickeRow Matrix.prime37)
  ; Reduce.genusX0Plus = Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime37)
  ; Reduce.frickeFixedPoints = Fricke.frickeFixedPointCount (Fricke.frickeRow Matrix.prime37)
  ; Reduce.totalIsGenusPlusOne = refl
  ; Reduce.frobeniusOrbitDecomposition = refl
  ; Reduce.frickeFixedDoubleRational = refl
  ; Reduce.frickeRiemannHurwitz = Fricke.riemannHurwitzFormula (Fricke.frickeRow Matrix.prime37)
  }

p43CountData : Reduce.SupersingularFrickeCountData
p43CountData = record
  { Reduce.totalSupersingular = 4
  ; Reduce.rationalSupersingular = 2
  ; Reduce.frobeniusPairDefect = 1
  ; Reduce.genusX0 = Fricke.genusX0 (Fricke.frickeRow Matrix.prime43)
  ; Reduce.genusX0Plus = Fricke.genusX0Plus (Fricke.frickeRow Matrix.prime43)
  ; Reduce.frickeFixedPoints = Fricke.frickeFixedPointCount (Fricke.frickeRow Matrix.prime43)
  ; Reduce.totalIsGenusPlusOne = refl
  ; Reduce.frobeniusOrbitDecomposition = refl
  ; Reduce.frickeFixedDoubleRational = refl
  ; Reduce.frickeRiemannHurwitz = Fricke.riemannHurwitzFormula (Fricke.frickeRow Matrix.prime43)
  }

p11PairDefectEqualsGenus :
  Reduce.frobeniusPairDefect p11CountData ≡ Reduce.genusX0Plus p11CountData
p11PairDefectEqualsGenus = Reduce.frobeniusPairDefectEqualsFrickeGenus p11CountData

p37PairDefectEqualsGenus :
  Reduce.frobeniusPairDefect p37CountData ≡ Reduce.genusX0Plus p37CountData
p37PairDefectEqualsGenus = Reduce.frobeniusPairDefectEqualsFrickeGenus p37CountData

p43PairDefectEqualsGenus :
  Reduce.frobeniusPairDefect p43CountData ≡ Reduce.genusX0Plus p43CountData
p43PairDefectEqualsGenus = Reduce.frobeniusPairDefectEqualsFrickeGenus p43CountData

p11GeometricPairWitnessConsumed :
  P11.p11PairedOrbitDefectIsZero
  ≡ P11.p11PairedOrbitDefectIsZero
p11GeometricPairWitnessConsumed = refl

p37GeometricNormalFormExists :
  P37.P37Normal ≡ P37.P37Normal
p37GeometricNormalFormExists = refl

p43GeometricPairCountConsumed : P43.p43CoarsePairCount ≡ 1
p43GeometricPairCountConsumed = P43.p43CoarsePairCountIsOne
