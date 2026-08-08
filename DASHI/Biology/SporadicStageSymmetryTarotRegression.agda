module DASHI.Biology.SporadicStageSymmetryTarotRegression where

open import DASHI.Core.Prelude

import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Foundations.StageSymmetryCarrierTowerExact as Sym
import DASHI.Foundations.DialecticSheetFrameSelectorExact as Selector
import DASHI.Foundations.SecondRevolutionJankoTarotExact as Revolution
import DASHI.Biology.SporadicTarotDependencyExact as Sporadic
import DASHI.Biology.TarotCarrierExact as Tarot
import DASHI.Biology.JMDSporadicTarotOrdinalTotalisationExact as Total
import DASHI.Moonshine.EulerMonsterMeaningSeparationExact as Euler

stageFiveConstituentRegression :
  BT.TwoTriadComposite.totalAmplitude BT.stage5Composite ≡ 5
stageFiveConstituentRegression = refl

stageFiveResidualRetainedRegression :
  BT.RetainedTriadicFallback.residualErased BT.stage5To3RetainsTwo ≡ false
stageFiveResidualRetainedRegression = refl

stageFiveSymmetryRegression :
  BT.SymmetryAwareStageState.stabiliser BT.stage3SymmetryState
    ≡ BT.fullStabiliserS3
  × BT.SymmetryAwareStageState.stabiliser BT.stage2SymmetryState
    ≡ BT.pairStabiliserS2
stageFiveSymmetryRegression = refl , refl

counterpositionRegression :
  BT.thirdCoordinateCounterposition ≡ BT.strictInverse BT.allPositive → ⊥
counterpositionRegression = BT.counterpositionNeedNotBeInverse

sixDualReadingRegression :
  Sym.hexadicCardinality ≡ 6
  × 6 + 3 ≡ Sym.nonaryCardinality
sixDualReadingRegression = refl , refl

oggCountRegression : BT.countList BT.allOggPrimes ≡ 15
oggCountRegression = BT.oggPrimeCountIsFifteen

seventyOneComplementRegression : 10 + 71 ≡ 81
seventyOneComplementRegression = BT.eightyOneSplitsTenAndSeventyOne

moonshineResidueRegression :
  2430 * 81 + 54 ≡ 196884
  × 2430 * 81 + 53 ≡ 196883
moonshineResidueRegression =
  BT.moonshineCoefficientDepthTwoEquation ,
  BT.monsterConstituentDepthTwoEquation

selectorReturnsWitnessRegression :
  Selector.Optional
    (Selector.FrameWitness Selector.exampleSemantics
      Selector.firstCondition Selector.secondCondition
      Selector.joinedSynthesis)
selectorReturnsWitnessRegression = Selector.selectInhabitableFrame

jankoAddressRegression :
  Revolution.DualRevolutionAddress.global Revolution.address14 ≡ 14
  × 10 + 4 ≡ 14
  × 9 + 5 ≡ 14
jankoAddressRegression = refl , refl , refl

fi22TotalisedRegression :
  Total.familyCompressionAssignment Sporadic.Fi22 ≡ Tarot.strength
fi22TotalisedRegression = Total.fi22FillsActualStrengthSlot

explicitCollisionRegression :
  Total.familyCompressionAssignment Sporadic.Fi23
  ≡ Total.familyCompressionAssignment Sporadic.BabyMonster
explicitCollisionRegression = Total.fi23BabyMonsterCollision

totalisationBoundaryRegression : Total.TotalisationAuthorityBoundary
totalisationBoundaryRegression = Total.canonicalTotalisationAuthorityBoundary

eulerMeaningBoundaryRegression : Euler.EulerMonsterAuthorityBoundary
eulerMeaningBoundaryRegression = Euler.canonicalEulerMonsterAuthorityBoundary
