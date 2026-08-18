module DASHI.Moonshine.DeligneRapoportFrickeCombinatoricsRegression where

------------------------------------------------------------------------
-- Focused regression for the finite/combinatorial half of the global
-- Deligne--Rapoport/Fricke selector.
--
-- These instances consume the already-constructed ACTUAL supersingular
-- Frobenius carriers at p=11,37,43.  They do not consume the Fricke genus as an
-- input and do not claim that the canonical nodal dual graph has yet been
-- identified with the proper modular-curve special fibre for arbitrary p.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (zero)

import DASHI.Foundations.FiniteInvolutionPairedOrbitQuotientExact as PairQuot
import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.SupersingularFrobeniusOrbitSpectrumExact as Spectrum
import DASHI.Moonshine.P11GeometricSupersingularCarrierExact as P11Carrier
import DASHI.Moonshine.P11BrandtFrobeniusFrickeCarrierSeparationExact as P11F
import DASHI.Moonshine.P11GeometricFrobeniusRealizationExact as P11
import DASHI.Moonshine.P37SageSupersingularFrobeniusExact as P37
import DASHI.Moonshine.P43NonOggFullLevel2DeuringControlExact as P43Carrier
import DASHI.Moonshine.P43GeometricFrobeniusRealizationExact as P43
import DASHI.Moonshine.RationalNodalSpecialFibreGenusExact as Nodal
import DASHI.Moonshine.PrimeLevelDeligneRapoportFrickeCombinatoricsExact as DR

p11DRData : DR.PrimeLevelSupersingularFrobeniusData
p11DRData = record
  { DR.prime = 11
  ; DR.Supersingular = P11Carrier.P11SupersingularJ
  ; DR.frobenius = P11F.p11GeometricFrobenius
  ; DR.fixedCount = 2
  ; DR.pairedCount = 0
  ; DR.totalCount = 2
  ; DR.spectrum = Spectrum.supersingularOrbitSpectrum Matrix.prime11
  ; DR.spectrumFixed = refl
  ; DR.spectrumPaired = refl
  ; DR.spectrumTotal = refl
  ; DR.normalForm = P11.p11NormalFormRealization
  }

p37DRData : DR.PrimeLevelSupersingularFrobeniusData
p37DRData = record
  { DR.prime = 37
  ; DR.Supersingular = P37.P37SupersingularJ
  ; DR.frobenius = P37.p37Frobenius
  ; DR.fixedCount = 1
  ; DR.pairedCount = 1
  ; DR.totalCount = 3
  ; DR.spectrum = Spectrum.supersingularOrbitSpectrum Matrix.prime37
  ; DR.spectrumFixed = refl
  ; DR.spectrumPaired = refl
  ; DR.spectrumTotal = refl
  ; DR.normalForm = P37.p37NormalFormRealization
  }

p43DRData : DR.PrimeLevelSupersingularFrobeniusData
p43DRData = record
  { DR.prime = 43
  ; DR.Supersingular = P43Carrier.P43GeometricJ
  ; DR.frobenius = P43Carrier.p43CoarseFrobenius
  ; DR.fixedCount = 2
  ; DR.pairedCount = 1
  ; DR.totalCount = 4
  ; DR.spectrum = Spectrum.supersingularOrbitSpectrum Matrix.prime43
  ; DR.spectrumFixed = refl
  ; DR.spectrumPaired = refl
  ; DR.spectrumTotal = refl
  ; DR.normalForm = P43.p43NormalFormRealization
  }

p11DerivedQuotientArithmeticGenus :
  Nodal.arithmeticGenus (DR.canonicalFrickeQuotientDualGraph p11DRData) ≡ 0
p11DerivedQuotientArithmeticGenus =
  DR.canonicalFrickeArithmeticGenusEqualsDeclaredPairCount p11DRData

p37DerivedQuotientArithmeticGenus :
  Nodal.arithmeticGenus (DR.canonicalFrickeQuotientDualGraph p37DRData) ≡ 1
p37DerivedQuotientArithmeticGenus =
  DR.canonicalFrickeArithmeticGenusEqualsDeclaredPairCount p37DRData

p43DerivedQuotientArithmeticGenus :
  Nodal.arithmeticGenus (DR.canonicalFrickeQuotientDualGraph p43DRData) ≡ 1
p43DerivedQuotientArithmeticGenus =
  DR.canonicalFrickeArithmeticGenusEqualsDeclaredPairCount p43DRData

p37UniqueNodeSectionExact :
  DR.frickeNodeOfNormalPair p37DRData
    (PairQuot.pairedOrbitNodeSection {1} zero)
  ≡ zero
p37UniqueNodeSectionExact = refl

p43UniqueNodeSectionExact :
  DR.frickeNodeOfNormalPair p43DRData
    (PairQuot.pairedOrbitNodeSection {1} zero)
  ≡ zero
p43UniqueNodeSectionExact = refl
