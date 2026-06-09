module DASHI.Physics.Closure.HeckeCarrierVsCMSplittingReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.P71HeckeMirrorSignLaneReceipt as P71
import DASHI.Physics.Closure.SSP15CMFieldSplittingCorrectionReceipt as CM15
import DASHI.Physics.Closure.SSP7Plus7Plus1AtomGrammarReceipt as Atom771

------------------------------------------------------------------------
-- Hecke carrier versus CM splitting correction.
--
-- This is the named bridge receipt requested by the audit.  It prevents a
-- category error: the CM arithmetic partition of the 15 SSP primes over
-- Q(sqrt(-7)) is 5 split + 9 inert + 1 ramified; the DASHI/Hecke atom
-- grammar is 7 geometry/amplitude lanes + 7 phase/dynamics lanes + 1
-- sign/reaction-orientation lane.  Both can be useful, but they are not the
-- same partition.  p71 is split in the CM table and is a sign/carry lane in
-- the Hecke atom grammar.  No time theorem or Clay promotion follows.

data HeckeCarrierVsCMSplittingStatus : Set where
  heckeCarrierAndCMSplittingSeparated_noClayPromotion :
    HeckeCarrierVsCMSplittingStatus

data CMSplittingShape : Set where
  split5_inert9_ramified1 :
    CMSplittingShape

data HeckeAtomGrammarShape : Set where
  mirrorA7_mirrorB7_sign1Shape :
    HeckeAtomGrammarShape

data HeckeAtomGrammarBlock : Set where
  MirrorA7 :
    HeckeAtomGrammarBlock

  MirrorB7 :
    HeckeAtomGrammarBlock

  Sign1 :
    HeckeAtomGrammarBlock

canonicalHeckeAtomGrammarBlocks :
  List HeckeAtomGrammarBlock
canonicalHeckeAtomGrammarBlocks =
  MirrorA7
  ∷ MirrorB7
  ∷ Sign1
  ∷ []

data PartitionSeparation : Set where
  cmArithmeticPartitionDistinctFromHeckeAtomGrammar :
    PartitionSeparation

data HeckeRoleP71 : Set where
  signLane :
    HeckeRoleP71

data SignCapacity : Set where
  terminalSSPBranchingCapacity :
    SignCapacity

data HeckeCMSplitLayer : Set where
  cmSplitLayerFiveNineOne :
    HeckeCMSplitLayer

data HeckeAtomSplitLayer : Set where
  heckeAtomLayerSevenSevenOne :
    HeckeAtomSplitLayer

data P71SignLaneJustification : Set where
  TerminalSSP :
    P71SignLaneJustification

  MonsterConjugateClass71A71B :
    P71SignLaneJustification

  BTBranchingCapacity71d :
    P71SignLaneJustification

  MoonshineTransparencyV71Zero :
    P71SignLaneJustification

canonicalFirst7ContainsInertPrimes :
  List Nat
canonicalFirst7ContainsInertPrimes =
  3 ∷ 5 ∷ 13 ∷ 17 ∷ []

canonicalP71SignLaneJustifications :
  List P71SignLaneJustification
canonicalP71SignLaneJustifications =
  TerminalSSP
  ∷ MonsterConjugateClass71A71B
  ∷ BTBranchingCapacity71d
  ∷ MoonshineTransparencyV71Zero
  ∷ []

data TimeTheorem : Set where

data ClayPromotion : Set where

timeTheoremImpossibleHere :
  TimeTheorem →
  ⊥
timeTheoremImpossibleHere ()

clayPromotionImpossibleHere :
  ClayPromotion →
  ⊥
clayPromotionImpossibleHere ()

heckeVsCMBoundaryStatement :
  String
heckeVsCMBoundaryStatement =
  "CM arithmetic split over Q(sqrt(-7)) is 5+9+1; DASHI/Hecke atom grammar is 7+7+1; these are distinct partitions."

p71BoundaryStatement :
  String
p71BoundaryStatement =
  "p71 is special as terminal SSP Hecke sign/carry/reaction-orientation lane, not because it is inert in Q(sqrt(-7))."

noTimeNoClayBoundaryStatement :
  String
noTimeNoClayBoundaryStatement =
  "The p71 sign-lane role is operational carry/reaction orientation only; it is not a literal time theorem and does not promote Clay."

record HeckeCarrierVsCMSplittingReceipt : Setω where
  field
    status :
      HeckeCarrierVsCMSplittingStatus

    statusIsCanonical :
      status ≡ heckeCarrierAndCMSplittingSeparated_noClayPromotion

    cmReceipt :
      CM15.SSP15CMFieldSplittingCorrectionReceipt

    cmReceiptStatusIsCanonical :
      CM15.status cmReceipt
      ≡
      CM15.qsqrtMinusSevenSSP15SplittingCorrectionRecorded

    atomGrammarReceipt :
      Atom771.SSP7Plus7Plus1AtomGrammarReceipt

    atomGrammarReceiptStatusIsCanonical :
      Atom771.status atomGrammarReceipt
      ≡
      Atom771.atomGrammarCorrectionReceipt3Recorded_noClayPromotion

    p71Receipt :
      P71.P71HeckeMirrorSignLaneReceipt

    p71ReceiptStatusIsCanonical :
      P71.status p71Receipt
      ≡
      P71.p71HeckeMirrorSignLaneRecorded_noClayPromotion

    cmSplitFiveNineOne :
      CMSplittingShape

    cmSplitFiveNineOneIsCanonical :
      cmSplitFiveNineOne ≡ split5_inert9_ramified1

    cmSplitLayer :
      HeckeCMSplitLayer

    cmSplitLayerIsFiveNineOne :
      cmSplitLayer ≡ cmSplitLayerFiveNineOne

    cmSplit591Label :
      String

    cmSplit591LabelIsRequested :
      cmSplit591Label ≡ "cmSplit_5_9_1"

    cmSplitPrimes :
      List Nat

    cmSplitPrimesAreCanonical :
      cmSplitPrimes ≡ CM15.canonicalQsqrtMinusSevenSplitPrimes

    cmSplitCount :
      Nat

    cmSplitCountIsFive :
      cmSplitCount ≡ 5

    cmInertCount :
      Nat

    cmInertCountIsNine :
      cmInertCount ≡ 9

    cmInertPrimes :
      List Nat

    cmInertPrimesAreCanonical :
      cmInertPrimes ≡ CM15.canonicalQsqrtMinusSevenInertPrimes

    cmRamifiedCount :
      Nat

    cmRamifiedCountIsOne :
      cmRamifiedCount ≡ 1

    cmRamifiedPrimes :
      List Nat

    cmRamifiedPrimesAreCanonical :
      cmRamifiedPrimes ≡ CM15.canonicalQsqrtMinusSevenRamifiedPrimes

    heckeAtomSplitSevenSevenOne :
      HeckeAtomGrammarShape

    heckeAtomSplitSevenSevenOneIsCanonical :
      heckeAtomSplitSevenSevenOne ≡ mirrorA7_mirrorB7_sign1Shape

    heckeAtomSplitLayer :
      HeckeAtomSplitLayer

    heckeAtomSplitLayerIsSevenSevenOne :
      heckeAtomSplitLayer ≡ heckeAtomLayerSevenSevenOne

    heckeAtomSplit771Label :
      String

    heckeAtomSplit771LabelIsRequested :
      heckeAtomSplit771Label ≡ "heckeAtomSplit_7_7_1"

    heckeAtomGrammarBlocks :
      List HeckeAtomGrammarBlock

    heckeAtomGrammarBlocksAreCanonical :
      heckeAtomGrammarBlocks ≡ canonicalHeckeAtomGrammarBlocks

    mirrorACount :
      Nat

    mirrorACountIsSeven :
      mirrorACount ≡ 7

    mirrorBCount :
      Nat

    mirrorBCountIsSeven :
      mirrorBCount ≡ 7

    signLaneCount :
      Nat

    signLaneCountIsOne :
      signLaneCount ≡ 1

    notSamePartition :
      PartitionSeparation

    notSamePartitionIsCanonical :
      notSamePartition ≡ cmArithmeticPartitionDistinctFromHeckeAtomGrammar

    notSamePartitionFlag :
      Bool

    notSamePartitionFlagIsTrue :
      notSamePartitionFlag ≡ true

    cmSplitAndHeckeAtomLayersAreDifferent :
      Bool

    cmSplitAndHeckeAtomLayersAreDifferentIsTrue :
      cmSplitAndHeckeAtomLayersAreDifferent ≡ true

    first7ContainsInertPrimes :
      List Nat

    first7ContainsInertPrimesAreCanonical :
      first7ContainsInertPrimes ≡ canonicalFirst7ContainsInertPrimes

    p71NotInertClaimRejected :
      Bool

    p71NotInertClaimRejectedIsTrue :
      p71NotInertClaimRejected ≡ true

    p71CMSplittingClass :
      CM15.CMPrimeSplittingClass

    p71CMSplittingClassIsSplit :
      p71CMSplittingClass ≡ CM15.split

    p71SignLane :
      HeckeRoleP71

    p71SignLaneIsCanonical :
      p71SignLane ≡ signLane

    p71SignCapacity :
      SignCapacity

    p71SignCapacityIsTerminalSSPBranchingCapacity :
      p71SignCapacity ≡ terminalSSPBranchingCapacity

    p71SignLaneJustifications :
      List P71SignLaneJustification

    p71SignLaneJustificationsAreCanonical :
      p71SignLaneJustifications ≡ canonicalP71SignLaneJustifications

    p71TerminalSSPJustification :
      P71SignLaneJustification

    p71TerminalSSPJustificationIsCanonical :
      p71TerminalSSPJustification ≡ TerminalSSP

    p71MonsterConjugateJustification :
      P71SignLaneJustification

    p71MonsterConjugateJustificationIsCanonical :
      p71MonsterConjugateJustification ≡ MonsterConjugateClass71A71B

    p71BTBranchingJustification :
      P71SignLaneJustification

    p71BTBranchingJustificationIsCanonical :
      p71BTBranchingJustification ≡ BTBranchingCapacity71d

    p71MoonshineTransparencyJustification :
      P71SignLaneJustification

    p71MoonshineTransparencyJustificationIsCanonical :
      p71MoonshineTransparencyJustification ≡ MoonshineTransparencyV71Zero

    noTimeTheoremFlag :
      Bool

    noTimeTheoremFlagIsTrue :
      noTimeTheoremFlag ≡ true

    noTimeTheorem :
      TimeTheorem →
      ⊥

    noClayPromotionFlag :
      Bool

    noClayPromotionFlagIsTrue :
      noClayPromotionFlag ≡ true

    noClayPromotion :
      ClayPromotion →
      ⊥

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ heckeVsCMBoundaryStatement

    p71Boundary :
      String

    p71BoundaryIsCanonical :
      p71Boundary ≡ p71BoundaryStatement

    noTimeNoClayBoundary :
      String

    noTimeNoClayBoundaryIsCanonical :
      noTimeNoClayBoundary ≡ noTimeNoClayBoundaryStatement

open HeckeCarrierVsCMSplittingReceipt public

canonicalHeckeCarrierVsCMSplittingReceipt :
  HeckeCarrierVsCMSplittingReceipt
canonicalHeckeCarrierVsCMSplittingReceipt =
  record
    { status =
        heckeCarrierAndCMSplittingSeparated_noClayPromotion
    ; statusIsCanonical =
        refl
    ; cmReceipt =
        CM15.canonicalSSP15CMFieldSplittingCorrectionReceipt
    ; cmReceiptStatusIsCanonical =
        refl
    ; atomGrammarReceipt =
        Atom771.canonicalSSP7Plus7Plus1AtomGrammarReceipt
    ; atomGrammarReceiptStatusIsCanonical =
        refl
    ; p71Receipt =
        P71.canonicalP71HeckeMirrorSignLaneReceipt
    ; p71ReceiptStatusIsCanonical =
        refl
    ; cmSplitFiveNineOne =
        split5_inert9_ramified1
    ; cmSplitFiveNineOneIsCanonical =
        refl
    ; cmSplitLayer =
        cmSplitLayerFiveNineOne
    ; cmSplitLayerIsFiveNineOne =
        refl
    ; cmSplit591Label =
        "cmSplit_5_9_1"
    ; cmSplit591LabelIsRequested =
        refl
    ; cmSplitPrimes =
        CM15.canonicalQsqrtMinusSevenSplitPrimes
    ; cmSplitPrimesAreCanonical =
        refl
    ; cmSplitCount =
        5
    ; cmSplitCountIsFive =
        refl
    ; cmInertCount =
        9
    ; cmInertCountIsNine =
        refl
    ; cmInertPrimes =
        CM15.canonicalQsqrtMinusSevenInertPrimes
    ; cmInertPrimesAreCanonical =
        refl
    ; cmRamifiedCount =
        1
    ; cmRamifiedCountIsOne =
        refl
    ; cmRamifiedPrimes =
        CM15.canonicalQsqrtMinusSevenRamifiedPrimes
    ; cmRamifiedPrimesAreCanonical =
        refl
    ; heckeAtomSplitSevenSevenOne =
        mirrorA7_mirrorB7_sign1Shape
    ; heckeAtomSplitSevenSevenOneIsCanonical =
        refl
    ; heckeAtomSplitLayer =
        heckeAtomLayerSevenSevenOne
    ; heckeAtomSplitLayerIsSevenSevenOne =
        refl
    ; heckeAtomSplit771Label =
        "heckeAtomSplit_7_7_1"
    ; heckeAtomSplit771LabelIsRequested =
        refl
    ; heckeAtomGrammarBlocks =
        canonicalHeckeAtomGrammarBlocks
    ; heckeAtomGrammarBlocksAreCanonical =
        refl
    ; mirrorACount =
        7
    ; mirrorACountIsSeven =
        refl
    ; mirrorBCount =
        7
    ; mirrorBCountIsSeven =
        refl
    ; signLaneCount =
        1
    ; signLaneCountIsOne =
        refl
    ; notSamePartition =
        cmArithmeticPartitionDistinctFromHeckeAtomGrammar
    ; notSamePartitionIsCanonical =
        refl
    ; notSamePartitionFlag =
        true
    ; notSamePartitionFlagIsTrue =
        refl
    ; cmSplitAndHeckeAtomLayersAreDifferent =
        true
    ; cmSplitAndHeckeAtomLayersAreDifferentIsTrue =
        refl
    ; first7ContainsInertPrimes =
        canonicalFirst7ContainsInertPrimes
    ; first7ContainsInertPrimesAreCanonical =
        refl
    ; p71NotInertClaimRejected =
        true
    ; p71NotInertClaimRejectedIsTrue =
        refl
    ; p71CMSplittingClass =
        CM15.split
    ; p71CMSplittingClassIsSplit =
        refl
    ; p71SignLane =
        signLane
    ; p71SignLaneIsCanonical =
        refl
    ; p71SignCapacity =
        terminalSSPBranchingCapacity
    ; p71SignCapacityIsTerminalSSPBranchingCapacity =
        refl
    ; p71SignLaneJustifications =
        canonicalP71SignLaneJustifications
    ; p71SignLaneJustificationsAreCanonical =
        refl
    ; p71TerminalSSPJustification =
        TerminalSSP
    ; p71TerminalSSPJustificationIsCanonical =
        refl
    ; p71MonsterConjugateJustification =
        MonsterConjugateClass71A71B
    ; p71MonsterConjugateJustificationIsCanonical =
        refl
    ; p71BTBranchingJustification =
        BTBranchingCapacity71d
    ; p71BTBranchingJustificationIsCanonical =
        refl
    ; p71MoonshineTransparencyJustification =
        MoonshineTransparencyV71Zero
    ; p71MoonshineTransparencyJustificationIsCanonical =
        refl
    ; noTimeTheoremFlag =
        true
    ; noTimeTheoremFlagIsTrue =
        refl
    ; noTimeTheorem =
        timeTheoremImpossibleHere
    ; noClayPromotionFlag =
        true
    ; noClayPromotionFlagIsTrue =
        refl
    ; noClayPromotion =
        clayPromotionImpossibleHere
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; boundary =
        heckeVsCMBoundaryStatement
    ; boundaryIsCanonical =
        refl
    ; p71Boundary =
        p71BoundaryStatement
    ; p71BoundaryIsCanonical =
        refl
    ; noTimeNoClayBoundary =
        noTimeNoClayBoundaryStatement
    ; noTimeNoClayBoundaryIsCanonical =
        refl
    }

canonicalHeckeCMNotSamePartition :
  notSamePartitionFlag canonicalHeckeCarrierVsCMSplittingReceipt ≡ true
canonicalHeckeCMNotSamePartition =
  refl

canonicalHeckeCMP71NotInertRejected :
  p71NotInertClaimRejected canonicalHeckeCarrierVsCMSplittingReceipt ≡ true
canonicalHeckeCMP71NotInertRejected =
  refl

canonicalHeckeCMP71SignLane :
  p71SignLane canonicalHeckeCarrierVsCMSplittingReceipt ≡ signLane
canonicalHeckeCMP71SignLane =
  refl

canonicalHeckeCMFirst7ContainsInertPrimes :
  first7ContainsInertPrimes canonicalHeckeCarrierVsCMSplittingReceipt
  ≡
  canonicalFirst7ContainsInertPrimes
canonicalHeckeCMFirst7ContainsInertPrimes =
  refl

canonicalHeckeCMLayersAreDifferent :
  cmSplitAndHeckeAtomLayersAreDifferent
    canonicalHeckeCarrierVsCMSplittingReceipt
  ≡
  true
canonicalHeckeCMLayersAreDifferent =
  refl

canonicalHeckeCMP71SignLaneJustifications :
  p71SignLaneJustifications canonicalHeckeCarrierVsCMSplittingReceipt
  ≡
  canonicalP71SignLaneJustifications
canonicalHeckeCMP71SignLaneJustifications =
  refl

canonicalHeckeCMNoTimeTheorem :
  noTimeTheoremFlag canonicalHeckeCarrierVsCMSplittingReceipt ≡ true
canonicalHeckeCMNoTimeTheorem =
  refl

canonicalHeckeCMNoClayPromotion :
  clayPromoted canonicalHeckeCarrierVsCMSplittingReceipt ≡ false
canonicalHeckeCMNoClayPromotion =
  refl
