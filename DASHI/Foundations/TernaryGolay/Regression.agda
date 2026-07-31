module DASHI.Foundations.TernaryGolay.Regression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (0ℚ)

open import Base369 using
  ( tri-mid ; non-7 )
import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.TernaryGolay.ChannelC3OrbitDecomposition as Channels
import DASHI.Foundations.TernaryGolay.CodeBoundary as Code
import DASHI.Foundations.TernaryGolay.CoxeterToddRoutesBoundary as K12
import DASHI.Foundations.TernaryGolay.MathieuExceptionalBridgeBoundary as Mathieu
import DASHI.Foundations.TernaryGolay.NonaryTernaryReduction as Reduction
import DASHI.Foundations.TernaryGolay.RetractedZ9CoxeterToddBoundary as Retraction
import DASHI.Foundations.TernaryGolay.SourceAtlas as Sources
import DASHI.Foundations.TernaryGolay.TGICWalshS3Decomposition as Walsh
import DASHI.Foundations.UBP.ExternalRepositoryProvenance as Provenance
import DASHI.Foundations.UBP.LeechValidMoveSet as Moves
import DASHI.Foundations.UBP.YIntervalCertificate as Interval

sourceCountRegression : Sources.canonicalTernaryGolaySourceCount ≡ 8
sourceCountRegression = Sources.canonicalTernaryGolaySourceCountIsEight

externalSourceCountRegression :
  Provenance.canonicalUBPExternalSourceCount ≡ 4
externalSourceCountRegression =
  Provenance.canonicalUBPExternalSourceCountIsFour

threePowerSixRegression : Code.pow 3 6 ≡ 729
threePowerSixRegression = Code.threePowerSix

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
nonaryReductionSample =
  Reduction.reducePreservesOne

nonaryReductionAddLawAvailable :
  Reduction.reduce9to3
    (DASHI.Foundations.Base369NonaryTruthRing.nonaryAdd non-7 non-7)
  ≡
  DASHI.Foundations.Base369TriTruthField.triAdd
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

focusedReceipts : List GenericReceipt.GenericReceipt
focusedReceipts =
  Provenance.externalRepositoryProvenanceGenericReceipt
  ∷ Sources.sourceAtlasReceipt
  ∷ Code.ternaryGolayBoundaryReceipt
  ∷ Retraction.retractedLiftGenericReceipt
  ∷ K12.coxeterToddRoutesGenericReceipt
  ∷ Mathieu.mathieuExceptionalBridgeReceipt
  ∷ Walsh.tgicWalshGenericReceipt
  ∷ Interval.yIntervalGenericReceipt
  ∷ Moves.leechValidMoveGenericReceipt
  ∷ []

allFocusedReceiptsNonPromoting :
  GenericReceipt.AllReceiptsNonPromoting focusedReceipts
allFocusedReceiptsNonPromoting =
  GenericReceipt.proveAllReceiptsNonPromoting focusedReceipts
