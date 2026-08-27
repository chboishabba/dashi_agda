module DASHI.Moonshine.Monster3BHighestAlphaValidation where

------------------------------------------------------------------------
-- Cumulative kernel root for the Monster 3B highest-alpha lane.
------------------------------------------------------------------------

import DASHI.Algebra.TriadicDepthOneCharacters as C3Exact
import DASHI.Moonshine.Monster3BNormalizerBridge as Normalizer
import DASHI.Moonshine.Monster3BCyclicFourierDyadicBridgeExact as Fourier
import DASHI.Moonshine.Monster3BHeisenbergMultiplicityExact as Heisenberg
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as Generators
import DASHI.Moonshine.Monster3BFiniteHeisenbergPermutationExact as Permutations
import DASHI.Moonshine.Monster3BElementaryAbelianInvariantExact as Elementary
import DASHI.Moonshine.Monster3BPhaseTransportExact as Transport
import DASHI.Moonshine.MonsterThreeLocalE8LeechBridgeExact as ThreeLocal
import DASHI.Moonshine.LeechWeightTwo196608BridgeExact as Leech
import DASHI.Moonshine.MonsterYangMills196608CrossLaneExact as CrossLane
import DASHI.Moonshine.Monster3BCentredProbeCoreSelectorExact as Centred
import DASHI.Moonshine.Monster3BMaximalRegularCoreExact as Maximal
import DASHI.Moonshine.Monster3BConformalLinePlacementExact as Conformal
import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Projector
import DASHI.Moonshine.Monster3BFiniteWeightProjectorExact as WeightProjector
import DASHI.Moonshine.Monster3BMultiplicityCharacterProjectorExact as Character
import DASHI.Moonshine.C3FourierConjugationExact as C3Fourier
import DASHI.Moonshine.C3CyclotomicRealDescentExact as C3Real
import DASHI.Moonshine.SSP15AffineC3TranslationExact as SSP42
import DASHI.Moonshine.MonsterReducedNonaryBoundaryExact as ReducedNonary

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_; _*_)
open import Data.Fin.Base using (Fin)

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

standardHeisenbergGeneratorPairCountIsThirtySix :
  Generators.standardGeneratorPairCount ≡ 36
standardHeisenbergGeneratorPairCountIsThirtySix = refl

sampleGeneratorWeylLaw :
  (state : Generators.X6) →
  Generators.modulationExponent Generators.axis2
    (Generators.translate Generators.axis2 state)
  ≡ Generators._+3_
      (Generators.kronecker Generators.axis2 Generators.axis2)
      (Generators.modulationExponent Generators.axis2 state)
sampleGeneratorWeylLaw =
  Generators.generatorWeylExponent Generators.axis2 Generators.axis2

sampleTranslationPermutationLaw :
  (state : Generators.X6) →
  Generators.translateInverse Generators.axis4
    (Generators.translate Generators.axis4 state)
  ≡ state
sampleTranslationPermutationLaw =
  Permutations.translateInverseAfterTranslate Generators.axis4

maximalCoreCertificateIsCanonical :
  Maximal.core Maximal.canonicalMaximalCoreDecomposition
  ≡ Centred.maximalRegularCore
maximalCoreCertificateIsCanonical = Maximal.canonicalCoreIsMaximal

conformalLineIsInvariantOnly :
  Conformal.addMultiplicity
    Conformal.conformalLineMultiplicity Fourier.monsterW3B
  ≡ Fourier.moonshineWeightTwo3B
conformalLineIsInvariantOnly =
  Conformal.moonshineWeightTwoSplitsConformalPlusMonster

projectorIndexModelHasCorrectDimension :
  Projector.zetaModelDimension ≡ 65610
projectorIndexModelHasCorrectDimension =
  Projector.zetaModelDimensionIs65610

sampleWeightProjectorIdempotent :
  (position : Generators.X6) →
  (coordinate : Fin 90) →
  WeightProjector.weightProjectorCoefficient position
      (WeightProjector.basisAt position coordinate)
    * WeightProjector.weightProjectorCoefficient position
      (WeightProjector.basisAt position coordinate)
  ≡ WeightProjector.weightProjectorCoefficient position
      (WeightProjector.basisAt position coordinate)
sampleWeightProjectorIdempotent position coordinate =
  WeightProjector.weightProjectorCoefficientIdempotent
    position (WeightProjector.basisAt position coordinate)

projectorCharacterDimensionMatchesNormalizer :
  Character.zetaSectorDegree ≡ Normalizer.nontrivialPhaseDegree
projectorCharacterDimensionMatchesNormalizer = refl

multiplicityCharacterTargetDegreeSplits :
  Heisenberg.naturalSuzukiDegree
  + Heisenberg.symmetricSquareDualDegree
  ≡ Character.multiplicityDegree
multiplicityCharacterTargetDegreeSplits =
  Character.multiplicityTwelvePlusSeventyEight

------------------------------------------------------------------------
-- New C3 / SSP15 / reduced-nonary frontier.

zetaSquareIsInverseInHighestAlphaRoot :
  C3Fourier.zetaSquared ≡ C3Fourier.inversePhase C3Fourier.zeta
zetaSquareIsInverseInHighestAlphaRoot =
  C3Fourier.zetaSquaredIsInverseZeta

conjugateFourierRowsAreExplicit :
  C3Fourier.conjugateRow C3Fourier.chi1 ≡ C3Fourier.chi2
conjugateFourierRowsAreExplicit = C3Fourier.chi1ConjugateIsChi2

ssp42VerticalTranslationIsInverseC3Phase :
  (mode : SSP42.MobileComplementMode3) →
  SSP42.advance12 (SSP42.advance42 mode) ≡ mode
ssp42VerticalTranslationIsInverseC3Phase = SSP42.advance12After42

ssp42GridReachesMonsterFactorTriple : 47 * 59 * 71 ≡ 196883
ssp42GridReachesMonsterFactorTriple =
  SSP42.largestThreeOggProductIsMonsterDimension

cyclotomicTraceIsConjugationInvariant :
  (phase : C3Exact.C3Phase) →
  C3Real.cyclotomicTrace (C3Fourier.inversePhase phase)
  ≡ C3Real.cyclotomicTrace phase
cyclotomicTraceIsConjugationInvariant = C3Real.traceIsConjugationInvariant

localisedReducedBoundaryStillGivesFiftyThree :
  ReducedNonary.reducedSixByNine ≡ 53
localisedReducedBoundaryStillGivesFiftyThree =
  ReducedNonary.reducedSixByNineIsFiftyThree
