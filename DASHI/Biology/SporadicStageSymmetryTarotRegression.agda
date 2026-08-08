module DASHI.Biology.SporadicStageSymmetryTarotRegression where

open import DASHI.Core.Prelude

import DASHI.Foundations.BalancedTernaryStageSymmetryExact as BT
import DASHI.Foundations.BalancedTernaryAmplitudeClosureExact as Amp
import DASHI.Foundations.BalancedTernaryUltrametricExact as Ultra
import DASHI.Foundations.StageSymmetryCarrierTowerExact as Sym
import DASHI.Foundations.DialecticSheetFrameSelectorExact as Selector
import DASHI.Foundations.FrameWitnessFibreMDLExact as FrameMDL
import DASHI.Foundations.DialecticCubieTetralemmaExact as Cubie
import DASHI.Foundations.SecondRevolutionJankoTarotExact as Revolution
import DASHI.Biology.ReducedFiftyThreeOrbitCandidateExact as Candidate
import DASHI.Biology.StageSymmetrySSP15BridgeExact as SSP
import DASHI.Biology.StageSymmetrySSP15SpectrumExact as Spectrum
import DASHI.Biology.ImageHexagramSSP15MDLExact as Integrated
import DASHI.Biology.SporadicSignedFiftyThreeTarotProjectionExact as Signed
import DASHI.Biology.SporadicTarotDependencyExact as Sporadic
import DASHI.Biology.TarotCarrierExact as Tarot
import DASHI.Biology.JMDSporadicTarotOrdinalTotalisationExact as Total
import DASHI.Moonshine.DepthTwoNonaryResidueFibreExact as DepthTwo
import DASHI.Moonshine.EulerMonsterMeaningSeparationExact as Euler
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane

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

signedAmplitudeRegression :
  Amp.triadAmplitude BT.allPositive ≡ Amp.ampPos3
  × Amp.triadAmplitude BT.allNegative ≡ Amp.ampNeg3
  × Amp.triadAmplitude BT.balancedZeroPattern ≡ Amp.ampZero
signedAmplitudeRegression = refl , refl , refl

joinedAmplitudeRegression :
  Amp.joinAmplitude BT.allPositive BT.twoPositiveOneOpen ≡ Amp.joinedPos5
  × Amp.joinAmplitude BT.allPositive BT.allPositive ≡ Amp.joinedPos6
joinedAmplitudeRegression = refl , refl

stageFiveFullBranchRegression :
  Amp.StageFiveBranch.visibleTarget Amp.positiveStageFiveCompletion ≡ 6
  × Amp.StageFiveBranch.visibleTarget Amp.negativeStageFiveResolution ≡ 4
  × Amp.StageFiveBranch.visibleTarget Amp.stageFiveFallbackWithResidual ≡ 3
stageFiveFullBranchRegression = refl , refl , refl

stageFiveResidueProfileRegression :
  Amp.ResidueDeficit369.remainder3 Amp.fiveResidueDeficitProfile ≡ 2
  × Amp.ResidueDeficit369.deficit6 Amp.fiveResidueDeficitProfile ≡ 1
  × Amp.ResidueDeficit369.deficit9 Amp.fiveResidueDeficitProfile ≡ 4
stageFiveResidueProfileRegression = refl , refl , refl

counterpositionRegression :
  BT.thirdCoordinateCounterposition ≡ BT.strictInverse BT.allPositive → ⊥
counterpositionRegression = BT.counterpositionNeedNotBeInverse

sixDualReadingRegression :
  Sym.hexadicCardinality ≡ 6
  × 6 + 3 ≡ Sym.nonaryCardinality
sixDualReadingRegression = refl , refl

ultrametricPrefixRegression :
  Ultra.PrefixAgreement 2 Ultra.fiveDigits Ultra.sixDigits
ultrametricPrefixRegression = Ultra.fiveSixAgreeThroughDepthTwo

tetralemmaRetainsCarrierRegression :
  Cubie.retainedCarrier Cubie.stageThreePatternWithCounterSquare
  ≡ BT.allPositive
tetralemmaRetainsCarrierRegression = Cubie.stageThreeCarrierRetained

cubiePositionCountRegression : Cubie.cubiePositionCardinality ≡ 27
cubiePositionCountRegression = Cubie.cubiePositionCardinalityIsTwentySeven

decisionPoliciesReallyDifferRegression :
  Cubie.positiveOnlyDecision BT.neg ≡ Cubie.nonzeroDecision BT.neg → ⊥
decisionPoliciesReallyDifferRegression = Cubie.decisionPoliciesDifferOnNegative

witnessFibreRetainsAlternativesRegression :
  FrameMDL.listCount FrameMDL.allAdmissibleWitnesses ≡ 2
witnessFibreRetainsAlternativesRegression =
  FrameMDL.admissibleWitnessCountIsTwo

mdlSelectorRegression :
  FrameMDL.ActionMDL.MDLSelection.selected
    FrameMDL.canonicalFrameMDLSelection tt
  ≡ FrameMDL.compactFrame
mdlSelectorRegression = FrameMDL.selectedFrameIsCompact

oggCountRegression : SSP.countList SSP.allOggPrimeLanes ≡ 15
oggCountRegression = SSP.oggPrimeLaneCountIsFifteen

seventyOneExistingLaneRegression :
  10 + SSP.oggPrimeLaneValue Lane.p71 ≡ 81
seventyOneExistingLaneRegression = SSP.eightyOneTenSeventyOneBridge

richSpectrumRetainsResidualRegression :
  Spectrum.residualCode (Spectrum.stageFiveRichSignature Lane.p3) ≡ 2
richSpectrumRetainsResidualRegression =
  Spectrum.stageFiveP3RetainsResidualTwo

sameLocalDifferentSpectrumRegression :
  Spectrum.status (Spectrum.localOnlyStageThreeSignature Lane.p71)
  ≡ Spectrum.status (Spectrum.crossScaleStageThreeSignature Lane.p71)
  → ⊥
sameLocalDifferentSpectrumRegression = Spectrum.signaturesDifferAtP71

integratedPipelineRegression :
  Integrated.listCount Integrated.canonicalPipeline ≡ 7
integratedPipelineRegression = Integrated.pipelineHasSevenTypedStages

moonshineResidueRegression :
  2430 * 81 + 54 ≡ 196884
  × 2430 * 81 + 53 ≡ 196883
moonshineResidueRegression =
  BT.moonshineCoefficientDepthTwoEquation ,
  BT.monsterConstituentDepthTwoEquation

moonshineTernaryExpansionRegression :
  3 ^ 11 + 3 ^ 9 + 2 * (3 ^ 3) ≡ 196884
moonshineTernaryExpansionRegression =
  DepthTwo.moonshineCoefficientTernaryExpansion

depthTwoCommutingSquareRegression :
  DepthTwo.fullResidue DepthTwo.canonicalDepthTwoCommutingSquare ≡ 54
  × DepthTwo.reducedResidue DepthTwo.canonicalDepthTwoCommutingSquare ≡ 53
  × DepthTwo.terminalProductCount ≡ 54
depthTwoCommutingSquareRegression = refl , refl , refl

signedSporadicDimensionRegression : Signed.sporadicSignedDimension ≡ 53
signedSporadicDimensionRegression = Signed.sporadicSignedDimensionIsFiftyThree

signedSporadic54Regression : Signed.sporadicSigned54Dimension ≡ 54
signedSporadic54Regression = Signed.sporadicSigned54DimensionIsFiftyFour

signedPolaritySharesCardRegression :
  Signed.canonicalArcanaProjection
    (Signed.sporadicSignedState Sporadic.J2 Candidate.positiveFibre)
  ≡
  Signed.canonicalArcanaProjection
    (Signed.sporadicSignedState Sporadic.J2 Candidate.negativeFibre)
signedPolaritySharesCardRegression = Signed.polaritiesShareArcana Sporadic.J2

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

signedCarrierBoundaryRegression : Signed.SporadicSignedFiftyThreeBoundary
signedCarrierBoundaryRegression = Signed.canonicalSporadicSignedFiftyThreeBoundary

amplitudeBoundaryRegression : Amp.AmplitudeProjectionBoundary
amplitudeBoundaryRegression = Amp.canonicalAmplitudeProjectionBoundary

witnessFibreBoundaryRegression : FrameMDL.WitnessFibreMDLBoundary
witnessFibreBoundaryRegression = FrameMDL.canonicalWitnessFibreMDLBoundary

sspReuseBoundaryRegression : SSP.StageSymmetrySSP15Boundary
sspReuseBoundaryRegression = SSP.canonicalStageSymmetrySSP15Boundary

richSpectrumBoundaryRegression : Spectrum.OggSpectrumAuthorityBoundary
richSpectrumBoundaryRegression = Spectrum.canonicalOggSpectrumAuthorityBoundary

integratedSelectorBoundaryRegression : Integrated.IntegratedSelectorBoundary
integratedSelectorBoundaryRegression = Integrated.canonicalIntegratedSelectorBoundary

depthTwoBoundaryRegression : DepthTwo.DepthTwoNonaryAuthorityBoundary
depthTwoBoundaryRegression = DepthTwo.canonicalDepthTwoNonaryAuthorityBoundary

eulerMeaningBoundaryRegression : Euler.EulerMonsterAuthorityBoundary
eulerMeaningBoundaryRegression = Euler.canonicalEulerMonsterAuthorityBoundary
