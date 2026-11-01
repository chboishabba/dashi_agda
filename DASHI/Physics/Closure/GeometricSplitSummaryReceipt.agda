module DASHI.Physics.Closure.GeometricSplitSummaryReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Disc11ExceptionReceipt as Disc11
import DASHI.Physics.Closure.LeptonYukawaFromLevelOverlapReceipt as D8Overlap
import DASHI.Physics.Closure.Paper8CoreThesisReceipt as Paper8
import DASHI.Physics.Closure.QuarkLeptonGeometricSplitReceipt as Split
import DASHI.Physics.Closure.TauLeptonGen3OverlapReceipt as TauOverlap
import DASHI.Physics.QFT.CSLevelFlowFullReceipt as CSFlow
import DASHI.Physics.QFT.SU3ColourFrom3LanesFusionReceipt as SU3Colour
import DASHI.Physics.QFT.U1YFromConductorReceipt as U1Y

------------------------------------------------------------------------
-- Paper 8 geometric split summary.
--
-- This receipt summarizes the geometric split result while delegating the
-- detailed level arithmetic to the specialized split/overlap receipts.  All
-- gauge readings remain candidate/diagnostic.  No Standard Model, DHR, Clay,
-- or terminal promotion is made here.

data Paper8GeometricSplitPoint : Set where
  quarkLevelsThreeFourSevenPairwiseCoprime :
    Paper8GeometricSplitPoint

  leptonLevelsEightElevenTwelveWithSixTwelveAmbiguity :
    Paper8GeometricSplitPoint

  dMinusEightOverlapsQuarkLevelFour :
    Paper8GeometricSplitPoint

  dMinusTwelveOverlapsQuarkLevelThree :
    Paper8GeometricSplitPoint

  dMinusElevenRecordedAsException :
    Paper8GeometricSplitPoint

  levelOverlapYukawaFactorsRecorded :
    Paper8GeometricSplitPoint

  su3su2u1CandidateGaugeReadingsRecorded :
    Paper8GeometricSplitPoint

canonicalPaper8GeometricSplitPoints :
  List Paper8GeometricSplitPoint
canonicalPaper8GeometricSplitPoints =
  quarkLevelsThreeFourSevenPairwiseCoprime
  ∷ leptonLevelsEightElevenTwelveWithSixTwelveAmbiguity
  ∷ dMinusEightOverlapsQuarkLevelFour
  ∷ dMinusTwelveOverlapsQuarkLevelThree
  ∷ dMinusElevenRecordedAsException
  ∷ levelOverlapYukawaFactorsRecorded
  ∷ su3su2u1CandidateGaugeReadingsRecorded
  ∷ []

data LevelOverlapYukawaFactor : Set where
  d8ToLevel4FactorOneHalf :
    LevelOverlapYukawaFactor

  d12Level6ToLevel3FactorOneThird :
    LevelOverlapYukawaFactor

  d12Level12ToLevel4FactorOneFourth :
    LevelOverlapYukawaFactor

canonicalLevelOverlapYukawaFactors :
  List LevelOverlapYukawaFactor
canonicalLevelOverlapYukawaFactors =
  d8ToLevel4FactorOneHalf
  ∷ d12Level6ToLevel3FactorOneThird
  ∷ d12Level12ToLevel4FactorOneFourth
  ∷ []

data GaugeCandidateReading : Set where
  su3ChiralLimitCandidate :
    GaugeCandidateReading

  su2LevelFlowCandidate :
    GaugeCandidateReading

  u1yZ6ToU1Candidate :
    GaugeCandidateReading

canonicalGaugeCandidateReadings :
  List GaugeCandidateReading
canonicalGaugeCandidateReadings =
  su3ChiralLimitCandidate
  ∷ su2LevelFlowCandidate
  ∷ u1yZ6ToU1Candidate
  ∷ []

data Paper8GeometricSplitBlocker : Set where
  geometricSplitNotMatterRepresentation :
    Paper8GeometricSplitBlocker

  leptonAmbiguityStillOpen :
    Paper8GeometricSplitBlocker

  discElevenBridgeStillOpen :
    Paper8GeometricSplitBlocker

  noSMClayOrTerminalPromotion :
    Paper8GeometricSplitBlocker

  noExactDHRGaugeGroupPromotion :
    Paper8GeometricSplitBlocker

canonicalPaper8GeometricSplitBlockers :
  List Paper8GeometricSplitBlocker
canonicalPaper8GeometricSplitBlockers =
  geometricSplitNotMatterRepresentation
  ∷ leptonAmbiguityStillOpen
  ∷ discElevenBridgeStillOpen
  ∷ noSMClayOrTerminalPromotion
  ∷ noExactDHRGaugeGroupPromotion
  ∷ []

data Paper8GeometricSplitPromotion : Set where

paper8GeometricSplitPromotionImpossibleHere :
  Paper8GeometricSplitPromotion →
  ⊥
paper8GeometricSplitPromotionImpossibleHere ()

paper8GeometricSplitStatement : String
paper8GeometricSplitStatement =
  "Paper 8 geometric split: quark levels 3,4,7 are pairwise coprime; D=-8 level 8 overlaps level 4, D=-12 level 6/12 overlaps levels 3/4, D=-11 is isolated by exception/exhaustion; overlap factors 1/2,1/3,1/4 and SU3/SU2/U1Y readings remain candidate/diagnostic."

record GeometricSplitSummaryReceipt : Setω where
  field
    paper8CoreReceipt :
      Paper8.Paper8CoreThesisReceipt

    paper8CoreTerminalStillFalse :
      Paper8.fullUnificationPromoted paper8CoreReceipt ≡ false

    splitReceipt :
      Split.QuarkLeptonGeometricSplitReceipt

    quarkLevelsPairwiseCoprime :
      Split.quarkLevelsPairwiseCoprime splitReceipt ≡ true

    leptonDMinusTwelveAmbiguousLevelIsSix :
      Split.leptonDMinusTwelveAmbiguousLevel splitReceipt ≡ 6

    dMinusEightOverlapRecorded :
      Split.dMinusEightOverlapsQuarkLevelFour splitReceipt ≡ true

    dMinusTwelveOverlapRecorded :
      Split.dMinusTwelveOverlapsQuarkLevelThree splitReceipt ≡ true

    discElevenExceptionRecorded :
      Split.disc11Exception splitReceipt ≡ true

    splitPhysicalPromotionFalse :
      Split.quarkLeptonPhysicalPromotion splitReceipt ≡ false

    splitSMMatterPromotionFalse :
      Split.smMatterPromoted splitReceipt ≡ false

    d8OverlapReceipt :
      D8Overlap.LeptonYukawaFromLevelOverlapReceipt

    d8OverlapRatioNumeratorIsOne :
      D8Overlap.genOneOverlapRatioNumerator d8OverlapReceipt ≡ 1

    d8OverlapRatioDenominatorIsTwo :
      D8Overlap.genOneOverlapRatioDenominator d8OverlapReceipt ≡ 2

    d8OverlapNoSMPromotion :
      D8Overlap.smMatterPromoted d8OverlapReceipt ≡ false

    tauOverlapReceipt :
      TauOverlap.TauLeptonGen3OverlapReceipt

    tauD12LevelSixRecorded :
      TauOverlap.levelSix tauOverlapReceipt ≡ 6

    tauD12LevelTwelveRecorded :
      TauOverlap.levelTwelve tauOverlapReceipt ≡ 12

    tauD12LevelSixRatioDenominatorIsThree :
      TauOverlap.ratioToP3CSLaneDenominator tauOverlapReceipt ≡ 3

    tauD12LevelTwelveRatioDenominatorIsFour :
      TauOverlap.ratioToP2UDLaneDenominator tauOverlapReceipt ≡ 4

    tauOverlapNoSMPromotion :
      TauOverlap.physicalSMPromoted tauOverlapReceipt ≡ false

    disc11Receipt :
      Disc11.Disc11ExceptionReceipt

    disc11IsolatedFromQuarkLevels :
      Disc11.disc11CoprimeToAllQuarkLevels disc11Receipt ≡ true

    disc11ExceptionByExhaustion :
      Disc11.disc11IsLeptonByExhaustion disc11Receipt ≡ true

    disc11NoSMPromotion :
      Disc11.smMatterPromoted disc11Receipt ≡ false

    levelOverlapYukawaFactors :
      List LevelOverlapYukawaFactor

    levelOverlapYukawaFactorsAreCanonical :
      levelOverlapYukawaFactors ≡ canonicalLevelOverlapYukawaFactors

    overlapFactorOneHalfRecorded :
      Bool

    overlapFactorOneHalfRecordedIsTrue :
      overlapFactorOneHalfRecorded ≡ true

    overlapFactorOneThirdRecorded :
      Bool

    overlapFactorOneThirdRecordedIsTrue :
      overlapFactorOneThirdRecorded ≡ true

    overlapFactorOneFourthRecorded :
      Bool

    overlapFactorOneFourthRecordedIsTrue :
      overlapFactorOneFourthRecorded ≡ true

    su3ColourReceipt :
      SU3Colour.SU3ColourFrom3LanesFusionReceipt

    su3ChiralLimitCandidateRecorded :
      SU3Colour.chiralLimitCandidate su3ColourReceipt ≡ true

    su3ExactPromotionFalse :
      SU3Colour.exactSU3cPromoted su3ColourReceipt ≡ false

    su3GDHRGSMFalse :
      SU3Colour.exactGDHREqualsGSMPromoted su3ColourReceipt ≡ false

    csLevelFlowReceipt :
      CSFlow.CSLevelFlowFullReceipt

    su2LevelFlowCandidateRecorded :
      CSFlow.p2FlowToSU2OneCandidate csLevelFlowReceipt ≡ true

    su2ExactPromotionFalse :
      CSFlow.exactSU2LPromotion csLevelFlowReceipt ≡ false

    csFlowExactSMFalse :
      CSFlow.exactStandardModelPromotion csLevelFlowReceipt ≡ false

    csFlowGDHRGSMFalse :
      CSFlow.exactGDHREqualsGSMPromotion csLevelFlowReceipt ≡ false

    u1yReceipt :
      U1Y.U1YFromConductorReceipt

    u1yZ6CandidateRecorded :
      U1Y.u1yChargesAsZ6Characters u1yReceipt ≡ true

    u1yContinuousEmbeddingStillFalse :
      U1Y.continuousU1Embedding u1yReceipt ≡ false

    u1yExactSMPromotionFalse :
      U1Y.exactStandardModelPromoted u1yReceipt ≡ false

    gaugeCandidateReadings :
      List GaugeCandidateReading

    gaugeCandidateReadingsAreCanonical :
      gaugeCandidateReadings ≡ canonicalGaugeCandidateReadings

    points :
      List Paper8GeometricSplitPoint

    pointsAreCanonical :
      points ≡ canonicalPaper8GeometricSplitPoints

    fivePointsRecorded :
      Bool

    fivePointsRecordedIsTrue :
      fivePointsRecorded ≡ true

    paper8GeometricSplitSummaryComplete :
      Bool

    paper8GeometricSplitSummaryCompleteIsTrue :
      paper8GeometricSplitSummaryComplete ≡ true

    deg23Promoted :
      Bool

    deg23PromotedIsFalse :
      deg23Promoted ≡ false

    ckmPromoted :
      Bool

    ckmPromotedIsFalse :
      ckmPromoted ≡ false

    standardModelPromoted :
      Bool

    standardModelPromotedIsFalse :
      standardModelPromoted ≡ false

    dhrGaugeGroupPromoted :
      Bool

    dhrGaugeGroupPromotedIsFalse :
      dhrGaugeGroupPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    terminalPromoted :
      Bool

    terminalPromotedIsFalse :
      terminalPromoted ≡ false

    blockers :
      List Paper8GeometricSplitBlocker

    blockersAreCanonical :
      blockers ≡ canonicalPaper8GeometricSplitBlockers

    promotionFlags :
      List Paper8GeometricSplitPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ paper8GeometricSplitStatement

    receiptBoundary :
      List String

open GeometricSplitSummaryReceipt public

canonicalGeometricSplitSummaryReceipt :
  GeometricSplitSummaryReceipt
canonicalGeometricSplitSummaryReceipt =
  record
    { paper8CoreReceipt =
        Paper8.canonicalPaper8CoreThesisReceipt
    ; paper8CoreTerminalStillFalse =
        refl
    ; splitReceipt =
        Split.canonicalQuarkLeptonGeometricSplitReceipt
    ; quarkLevelsPairwiseCoprime =
        refl
    ; leptonDMinusTwelveAmbiguousLevelIsSix =
        refl
    ; dMinusEightOverlapRecorded =
        refl
    ; dMinusTwelveOverlapRecorded =
        refl
    ; discElevenExceptionRecorded =
        refl
    ; splitPhysicalPromotionFalse =
        refl
    ; splitSMMatterPromotionFalse =
        refl
    ; d8OverlapReceipt =
        D8Overlap.canonicalLeptonYukawaFromLevelOverlapReceipt
    ; d8OverlapRatioNumeratorIsOne =
        refl
    ; d8OverlapRatioDenominatorIsTwo =
        refl
    ; d8OverlapNoSMPromotion =
        refl
    ; tauOverlapReceipt =
        TauOverlap.canonicalTauLeptonGen3OverlapReceipt
    ; tauD12LevelSixRecorded =
        refl
    ; tauD12LevelTwelveRecorded =
        refl
    ; tauD12LevelSixRatioDenominatorIsThree =
        refl
    ; tauD12LevelTwelveRatioDenominatorIsFour =
        refl
    ; tauOverlapNoSMPromotion =
        refl
    ; disc11Receipt =
        Disc11.canonicalDisc11ExceptionReceipt
    ; disc11IsolatedFromQuarkLevels =
        refl
    ; disc11ExceptionByExhaustion =
        refl
    ; disc11NoSMPromotion =
        refl
    ; levelOverlapYukawaFactors =
        canonicalLevelOverlapYukawaFactors
    ; levelOverlapYukawaFactorsAreCanonical =
        refl
    ; overlapFactorOneHalfRecorded =
        true
    ; overlapFactorOneHalfRecordedIsTrue =
        refl
    ; overlapFactorOneThirdRecorded =
        true
    ; overlapFactorOneThirdRecordedIsTrue =
        refl
    ; overlapFactorOneFourthRecorded =
        true
    ; overlapFactorOneFourthRecordedIsTrue =
        refl
    ; su3ColourReceipt =
        SU3Colour.canonicalSU3ColourFrom3LanesFusionReceipt
    ; su3ChiralLimitCandidateRecorded =
        refl
    ; su3ExactPromotionFalse =
        refl
    ; su3GDHRGSMFalse =
        refl
    ; csLevelFlowReceipt =
        CSFlow.canonicalCSLevelFlowFullReceipt
    ; su2LevelFlowCandidateRecorded =
        refl
    ; su2ExactPromotionFalse =
        refl
    ; csFlowExactSMFalse =
        refl
    ; csFlowGDHRGSMFalse =
        refl
    ; u1yReceipt =
        U1Y.canonicalU1YFromConductorReceipt
    ; u1yZ6CandidateRecorded =
        refl
    ; u1yContinuousEmbeddingStillFalse =
        refl
    ; u1yExactSMPromotionFalse =
        refl
    ; gaugeCandidateReadings =
        canonicalGaugeCandidateReadings
    ; gaugeCandidateReadingsAreCanonical =
        refl
    ; points =
        canonicalPaper8GeometricSplitPoints
    ; pointsAreCanonical =
        refl
    ; fivePointsRecorded =
        true
    ; fivePointsRecordedIsTrue =
        refl
    ; paper8GeometricSplitSummaryComplete =
        true
    ; paper8GeometricSplitSummaryCompleteIsTrue =
        refl
    ; deg23Promoted =
        false
    ; deg23PromotedIsFalse =
        refl
    ; ckmPromoted =
        false
    ; ckmPromotedIsFalse =
        refl
    ; standardModelPromoted =
        false
    ; standardModelPromotedIsFalse =
        refl
    ; dhrGaugeGroupPromoted =
        false
    ; dhrGaugeGroupPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; terminalPromoted =
        false
    ; terminalPromotedIsFalse =
        refl
    ; blockers =
        canonicalPaper8GeometricSplitBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        paper8GeometricSplitStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Point 1: quark levels D=-3 -> 3, D=-4 -> 4, D=-7 -> 7 are pairwise coprime"
        ∷ "Point 2: lepton levels D=-8 -> 8, D=-11 -> 11, and D=-12 -> 12 with level-6/12 ambiguity are recorded"
        ∷ "Point 3: D=-8 level 8 overlaps quark level 4 and records overlap factor 1/2"
        ∷ "Point 4: D=-12 records both level 6 over level 3 with factor 1/3 and level 12 over level 4 with factor 1/4"
        ∷ "Point 5: D=-11 is isolated from quark levels 3,4,7 and retained only by exception/exhaustion"
        ∷ "Gauge readings are SU3 chiral-limit candidate, SU2 level-flow candidate, and U1Y Z6-to-U1 candidate"
        ∷ "deg23, CKM, SM, DHR/G_DHR, Clay, and terminal promotion remain false"
        ∷ []
    }

geometricSplitSummaryKeepsSMFalse :
  standardModelPromoted canonicalGeometricSplitSummaryReceipt ≡ false
geometricSplitSummaryKeepsSMFalse =
  refl

geometricSplitSummaryRecordsOverlapFactors :
  levelOverlapYukawaFactors canonicalGeometricSplitSummaryReceipt
  ≡
  canonicalLevelOverlapYukawaFactors
geometricSplitSummaryRecordsOverlapFactors =
  refl

geometricSplitSummaryRecordsGaugeCandidates :
  gaugeCandidateReadings canonicalGeometricSplitSummaryReceipt
  ≡
  canonicalGaugeCandidateReadings
geometricSplitSummaryRecordsGaugeCandidates =
  refl

geometricSplitSummaryKeepsDHRFalse :
  dhrGaugeGroupPromoted canonicalGeometricSplitSummaryReceipt ≡ false
geometricSplitSummaryKeepsDHRFalse =
  refl

geometricSplitSummaryKeepsTerminalFalse :
  terminalPromoted canonicalGeometricSplitSummaryReceipt ≡ false
geometricSplitSummaryKeepsTerminalFalse =
  refl
