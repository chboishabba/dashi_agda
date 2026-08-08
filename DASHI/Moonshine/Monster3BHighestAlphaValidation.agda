module DASHI.Moonshine.Monster3BHighestAlphaValidation where

------------------------------------------------------------------------
-- Cumulative kernel root for the Monster 3B highest-alpha lane.
------------------------------------------------------------------------

import DASHI.Moonshine.Monster3BNormalizerBridge as Normalizer
import DASHI.Moonshine.Monster3BCyclicFourierDyadicBridgeExact as Fourier
import DASHI.Moonshine.Monster3BHeisenbergMultiplicityExact as Heisenberg
import DASHI.Moonshine.Monster3BElementaryAbelianInvariantExact as Elementary
import DASHI.Moonshine.Monster3BPhaseTransportExact as Transport
import DASHI.Moonshine.MonsterThreeLocalE8LeechBridgeExact as ThreeLocal
import DASHI.Moonshine.LeechWeightTwo196608BridgeExact as Leech
import DASHI.Moonshine.MonsterYangMills196608CrossLaneExact as CrossLane

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_)

normalizerAndFourierAgreeOnNontrivialMultiplicity :
  Normalizer.nontrivialPhaseDegree ≡ Fourier.zeta Fourier.monsterW3B
normalizerAndFourierAgreeOnNontrivialMultiplicity = refl

normalizerAndHeisenbergAgreeOnNontrivialMultiplicity :
  Normalizer.nontrivialPhaseDegree ≡ Heisenberg.heisenbergMultiplicitySector
normalizerAndHeisenbergAgreeOnNontrivialMultiplicity = refl

threeLocalChartsAgreeWithNormalizerDegree :
  ThreeLocal.tenTimesThreePowerEight ≡ Normalizer.nontrivialPhaseDegree
threeLocalChartsAgreeWithNormalizerDegree = refl

leechSubtotalAgreesWithDyadicBulk :
  Leech.leechCoordinateSubtotal ≡ Fourier.dyadicSymmetricBulk
leechSubtotalAgreesWithDyadicBulk = refl

actualWilsonDenominatorAgreesWithLeechSubtotal :
  CrossLane.commonDenominator ≡ Leech.leechCoordinateSubtotal
actualWilsonDenominatorAgreesWithLeechSubtotal = refl

leechCompletionAgreesWithMoonshineWeightTwo :
  Leech.leechWeightTwoDimension
  ≡ Fourier.phaseDimension Fourier.moonshineWeightTwo3B
leechCompletionAgreesWithMoonshineWeightTwo = refl

monsterGeometricCompletionAgreesAcrossCharts :
  Leech.coordinateSubtotalAfterConformalQuotient
  + Leech.offDiagonalQuadraticCount
  ≡ Fourier.phaseDimension Fourier.monsterW3B
monsterGeometricCompletionAgreesAcrossCharts = refl

monsterNumericalCompletionAgreesAcrossCharts :
  Leech.leechCoordinateSubtotal + Leech.numericalResidualBeyond196608
  ≡ Fourier.phaseDimension Fourier.monsterW3B
monsterNumericalCompletionAgreesAcrossCharts = refl

phaseTransportPreservesNontrivialDegree :
  Transport.phaseDimension
    (Transport.transportPhase
      Transport.invertsGenerator
      Transport.zetaPhase)
  ≡ Fourier.zetaSquared Fourier.monsterW3B
phaseTransportPreservesNontrivialDegree = refl

fixedLagrangianRestrictionReconstructsSchrodingerDegree :
  Elementary.regularCharacterMultiplicity
  * Elementary.translationPlaneOrder
  ≡ Elementary.schrodingerDimension
fixedLagrangianRestrictionReconstructsSchrodingerDegree = refl

fullSymplecticPlaneStrataReconstructGrassmannian :
  Elementary.fullIsotropicTwoPlaneCount
  + Elementary.fullNonIsotropicTwoPlaneCount
  ≡ Elementary.fullTwoPlaneCount
fullSymplecticPlaneStrataReconstructGrassmannian = refl

plusMinusExtraspecialDegreesAgree :
  Heisenberg.nonlinearCharacterDegree Heisenberg.plusType
  ≡ Heisenberg.nonlinearCharacterDegree Heisenberg.minusType
plusMinusExtraspecialDegreesAgree = refl
