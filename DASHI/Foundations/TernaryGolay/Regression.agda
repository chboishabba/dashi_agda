module DASHI.Foundations.TernaryGolay.Regression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (_*_)
open import Data.Rational using (_+_; 0ℚ)

open import Base369 using
  ( tri-mid ; non-7 )
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.Base369NonaryTruthRing as Z9
import DASHI.Foundations.Base369TriTruthField as F3
import DASHI.Foundations.TernaryGolay.BinaryTernaryMacWilliamsUnification as MacWilliams
import DASHI.Foundations.TernaryGolay.ChannelC3OrbitDecomposition as Channels
import DASHI.Foundations.TernaryGolay.CodeBoundary as Code
import DASHI.Foundations.TernaryGolay.CoxeterToddRoutesBoundary as K12
import DASHI.Foundations.TernaryGolay.ExplicitCode729 as Explicit
import DASHI.Foundations.TernaryGolay.MathieuExceptionalBridgeBoundary as Mathieu
import DASHI.Foundations.TernaryGolay.NonaryTernaryReduction as Reduction
import DASHI.Foundations.TernaryGolay.RetractedZ9CoxeterToddBoundary as Retraction
import DASHI.Foundations.TernaryGolay.SmallWittHexadCount as SmallWitt
import DASHI.Foundations.TernaryGolay.SourceAtlas as Sources
import DASHI.Foundations.TernaryGolay.TernaryGolayWeightEnumerator as Enumerator
import DASHI.Foundations.TernaryGolay.TGICWalshS3Decomposition as Walsh
import DASHI.Foundations.UBP.ExternalRepositoryProvenance as Provenance
import DASHI.Foundations.UBP.LeechValidMoveSet as Moves
import DASHI.Foundations.UBP.MOGGolayCharacterisationBoundary as MOG
import DASHI.Foundations.UBP.NRCIModelParameterBoundary as NRCI
import DASHI.Foundations.UBP.YIntervalCertificate as Interval

sourceCountRegression : Sources.canonicalTernaryGolaySourceCount ≡ 12
sourceCountRegression = Sources.canonicalTernaryGolaySourceCountIsTwelve

externalSourceCountRegression :
  Provenance.canonicalUBPExternalSourceCount ≡ 4
externalSourceCountRegression =
  Provenance.canonicalUBPExternalSourceCountIsFour

threePowerSixRegression : Code.pow 3 6 ≡ 729
threePowerSixRegression = Code.threePowerSix

explicitMessageCountRegression :
  Explicit.listCount Explicit.allMessages ≡ 729
explicitMessageCountRegression = Explicit.allMessagesCountIs729

explicitGeneratorGramRegression :
  Explicit.gramZeroCheck Explicit.generatorRows ≡ true
explicitGeneratorGramRegression = Explicit.generatorGramIsZero

explicitMinimumWeightRegression :
  Explicit.countWeight 5 Explicit.allCodewords ≡ 0
explicitMinimumWeightRegression = Explicit.weight5Count

explicitWeightSixRegression :
  Explicit.countWeight 6 Explicit.allCodewords ≡ 264
explicitWeightSixRegression = Explicit.weight6Count

explicitWeightNineRegression :
  Explicit.countWeight 9 Explicit.allCodewords ≡ 440
explicitWeightNineRegression = Explicit.weight9Count

explicitWeightTwelveRegression :
  Explicit.countWeight 12 Explicit.allCodewords ≡ 24
explicitWeightTwelveRegression = Explicit.weight12Count

weightEnumeratorSumRegression :
  Enumerator.coefficient0 Enumerator.ternaryGolayWeightEnumerator
  + Enumerator.coefficient6 Enumerator.ternaryGolayWeightEnumerator
  + Enumerator.coefficient9 Enumerator.ternaryGolayWeightEnumerator
  + Enumerator.coefficient12 Enumerator.ternaryGolayWeightEnumerator
  ≡ 729
weightEnumeratorSumRegression = Enumerator.enumeratorCoefficientSum

hexadCountRegression :
  Explicit.listCount SmallWitt.hexadSupports ≡ 132
hexadCountRegression = SmallWitt.hexadSupportCountIs132

pentadCountRegression :
  Explicit.listCount SmallWitt.pentads ≡ 792
pentadCountRegression = SmallWitt.pentadCountIs792

smallWittRegression :
  SmallWitt.everyPentadHasUniqueHexadCheck ≡ true
smallWittRegression = SmallWitt.everyPentadHasUniqueHexad

binaryOctadArithmeticRegression :
  64 * MacWilliams.octadCount
    MacWilliams.canonicalBinaryGolayOctadCoefficientReceipt
  ≡ 48576
binaryOctadArithmeticRegression =
  MacWilliams.reducedCoefficientEquation
    MacWilliams.canonicalBinaryGolayOctadCoefficientReceipt

channelCountRegression : Channels.listCount Channels.allChannels ≡ 9
channelCountRegression = Channels.channelCountIsNine

faceCountRegression : Channels.listCount Channels.allDirectedFaces ≡ 6
faceCountRegression = Channels.faceCountIsSix

diagonalCountRegression : Channels.listCount Channels.allDiagonalChannels ≡ 3
diagonalCountRegression = Channels.diagonalCountIsThree

c3OrientationRegression :
  Channels.c3OrbitOf
    (Channels.swapLowMidChannel Channels.low-mid)
  ≡ Channels.antiCyclicOrbit
c3OrientationRegression = Channels.swapExchangesCyclicOrientation

fullS3OrbitRegression :
  Channels.s3OrbitOf
    (Channels.swapLowMidChannel Channels.low-mid)
  ≡ Channels.offDiagonalS3Orbit
fullS3OrbitRegression = Channels.swapReturnsToSingleS3Orbit

nonaryReductionSample : Reduction.reduce9to3 non-7 ≡ tri-mid
nonaryReductionSample = refl

nonaryReductionAddLawAvailable :
  Reduction.reduce9to3 (Z9.nonaryAdd non-7 non-7)
  ≡
  F3.triAdd
    (Reduction.reduce9to3 non-7)
    (Reduction.reduce9to3 non-7)
nonaryReductionAddLawAvailable = Reduction.reducePreservesAdd non-7 non-7

retractedK12ClaimClosed :
  Retraction.constructionProducesK12 Retraction.canonicalCorrectedZ9LiftFacts
  ≡ false
retractedK12ClaimClosed =
  Retraction.constructionProducesK12IsFalse
    Retraction.canonicalCorrectedZ9LiftFacts

correctK12RoutesRecognised :
  K12.validRouteKinds K12.canonicalCoxeterToddRouteStatus
    K12.leechOrderThreeFixedRoute
  ≡ true
correctK12RoutesRecognised =
  K12.fixedRouteRecognised K12.canonicalCoxeterToddRouteStatus

trioOrbitArithmeticRegression :
  Mathieu.trioStabilizerOrder * Mathieu.trioCount ≡ Mathieu.m24Order
trioOrbitArithmeticRegression = Mathieu.trioOrbitArithmetic

walshPairwiseYCoefficientsCancel :
  Walsh.yCoefficient Walsh.xyPairwiseBias
  + Walsh.yCoefficient Walsh.xzPairwiseBias
  + Walsh.yCoefficient Walsh.yzPairwiseBias
  ≡ 0ℚ
walshPairwiseYCoefficientsCancel =
  Walsh.pairwiseBiasYCoefficientsSumToZero

mogShadowAloneClosed :
  MOG.shadowAloneDefinesGolay MOG.canonicalMOGCharacterisationStatus
  ≡ false
mogShadowAloneClosed =
  MOG.shadowAloneDefinesGolayIsFalse
    MOG.canonicalMOGCharacterisationStatus

nrciPhysicalEmergenceClosed :
  NRCI.independentlyEmergentThresholdEstablished
    NRCI.canonicalNRCIParameterStatus
  ≡ false
nrciPhysicalEmergenceClosed =
  NRCI.independentlyEmergentThresholdEstablishedIsFalse
    NRCI.canonicalNRCIParameterStatus

focusedReceipts : List GenericReceipt.GenericReceipt
focusedReceipts =
  Provenance.externalRepositoryProvenanceGenericReceipt
  ∷ Sources.sourceAtlasReceipt
  ∷ Code.ternaryGolayBoundaryReceipt
  ∷ Explicit.explicitTernaryGolayGenericReceipt
  ∷ Enumerator.weightEnumeratorGenericReceipt
  ∷ SmallWitt.smallWittGenericReceipt
  ∷ MacWilliams.macWilliamsUnificationGenericReceipt
  ∷ Retraction.retractedLiftGenericReceipt
  ∷ K12.coxeterToddRoutesGenericReceipt
  ∷ Mathieu.mathieuExceptionalBridgeReceipt
  ∷ Walsh.tgicWalshGenericReceipt
  ∷ MOG.mogCharacterisationReceipt
  ∷ NRCI.nrciParameterReceipt
  ∷ Interval.yIntervalGenericReceipt
  ∷ Moves.leechValidMoveGenericReceipt
  ∷ []

allFocusedReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting focusedReceipts
allFocusedReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting focusedReceipts
