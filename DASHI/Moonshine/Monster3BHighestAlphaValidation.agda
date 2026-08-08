module DASHI.Moonshine.Monster3BHighestAlphaValidation where

------------------------------------------------------------------------
-- Cumulative kernel root for the Monster 3B highest-alpha lane.
--
-- This imports the exact arithmetic, phase transport, Heisenberg multiplicity,
-- Leech weight-two, E8/3-local, and external-computation boundary modules.
-- A generated GAP certificate is compiled separately when available.
------------------------------------------------------------------------

import DASHI.Moonshine.Monster3BNormalizerBridge as Normalizer
import DASHI.Moonshine.Monster3BCyclicFourierDyadicBridgeExact as Fourier
import DASHI.Moonshine.Monster3BHeisenbergMultiplicityExact as Heisenberg
import DASHI.Moonshine.Monster3BPhaseTransportExact as Transport
import DASHI.Moonshine.MonsterThreeLocalE8LeechBridgeExact as ThreeLocal
import DASHI.Moonshine.LeechWeightTwo196608BridgeExact as Leech

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

------------------------------------------------------------------------
-- Cross-module exact endpoints.
------------------------------------------------------------------------

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

leechCompletionAgreesWithMoonshineWeightTwo :
  Leech.leechWeightTwoDimension ≡ Fourier.phaseDimension Fourier.moonshineWeightTwo3B
leechCompletionAgreesWithMoonshineWeightTwo = refl

monsterResidualCompletionAgreesAcrossCharts :
  Leech.leechCoordinateSubtotal + Leech.offDiagonalAfterConformalAdjustment
  ≡ Fourier.phaseDimension Fourier.monsterW3B
monsterResidualCompletionAgreesAcrossCharts = refl

phaseTransportPreservesNontrivialDegree :
  Transport.phaseDimension
    (Transport.transportPhase
      Transport.invertsGenerator
      Transport.zetaPhase)
  ≡ Fourier.zetaSquared Fourier.monsterW3B
phaseTransportPreservesNontrivialDegree = refl

highestAlphaArithmeticEndpoint : Nat
highestAlphaArithmeticEndpoint =
  Heisenberg.threePowerSix * Heisenberg.multiplicityDegree
  + Fourier.dyadicResidualDimension

highestAlphaArithmeticEndpointIs65885 :
  highestAlphaArithmeticEndpoint ≡ 65885
highestAlphaArithmeticEndpointIs65885 = refl
