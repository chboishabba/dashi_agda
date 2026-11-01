module DASHI.Physics.Closure.SSP7Plus7Plus1AtomGrammarFrameReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.SSP15CMFieldSplittingCorrectionReceipt as CM15
import DASHI.Physics.Closure.SSP7Plus7Plus1AtomGrammarReceipt as Atom771

------------------------------------------------------------------------
-- SSP 7+7+1 atom-grammar frame receipt.
--
-- This receipt records the frame-facing atom grammar correction.  The
-- fifteen SSP fields are partitioned as 7 MirrorA atom fields, 7 MirrorB
-- atom fields, and one sign lane.  The Gate 3 implication is aligned with
-- the corrected CM table: A_split > 0 uses MirrorA over the five split
-- primes {2,11,23,29,71}; A_inert > 0 uses MirrorB over the nine inert
-- primes {3,5,13,17,19,31,41,47,59}; p=7 is ramified/structural.  This is
-- architectural atom grammar, not CM splitting, and it makes no Clay
-- promotion.

data SSPAtomGrammarFrameStatus : Set where
  atomGrammarFrameRecorded_gate3Implication_noClayPromotion :
    SSPAtomGrammarFrameStatus

data AtomFrameLane : Set where
  MirrorA :
    AtomFrameLane

  MirrorB :
    AtomFrameLane

  signLane :
    AtomFrameLane

canonicalAtomFrameLanes :
  List AtomFrameLane
canonicalAtomFrameLanes =
  MirrorA ∷ MirrorB ∷ signLane ∷ []

data MirrorAAtomField : Set where
  position :
    MirrorAAtomField

  scale :
    MirrorAAtomField

  amplitude :
    MirrorAAtomField

  orientation :
    MirrorAAtomField

  anisotropy :
    MirrorAAtomField

  curvature :
    MirrorAAtomField

  depth :
    MirrorAAtomField

canonicalMirrorAAtomFields :
  List MirrorAAtomField
canonicalMirrorAAtomFields =
  position
  ∷ scale
  ∷ amplitude
  ∷ orientation
  ∷ anisotropy
  ∷ curvature
  ∷ depth
  ∷ []

data MirrorBAtomField : Set where
  phase :
    MirrorBAtomField

  twist :
    MirrorBAtomField

  helicity :
    MirrorBAtomField

  torsion :
    MirrorBAtomField

  pressureGradient :
    MirrorBAtomField

  transportDirection :
    MirrorBAtomField

  memoryCarry :
    MirrorBAtomField

canonicalMirrorBAtomFields :
  List MirrorBAtomField
canonicalMirrorBAtomFields =
  phase
  ∷ twist
  ∷ helicity
  ∷ torsion
  ∷ pressureGradient
  ∷ transportDirection
  ∷ memoryCarry
  ∷ []

data SignLaneAtomField : Set where
  sign :
    SignLaneAtomField

canonicalSignLaneAtomFields :
  List SignLaneAtomField
canonicalSignLaneAtomFields =
  sign ∷ []

data Gate3FrameImplication : Set where
  ASplitPositiveUsesMirrorAForSplitPrimes :
    Gate3FrameImplication

  AInertPositiveUsesMirrorBForInertPrimes :
    Gate3FrameImplication

  ARamifiedP7Structural :
    Gate3FrameImplication

  phaseBlindDictionaryFailsAtNineInertPrimes :
    Gate3FrameImplication

  mirrorBSevenVariablesSpanNineInertPrimeSpace :
    Gate3FrameImplication

  atomGrammarArchitecturalNotCMSplitting :
    Gate3FrameImplication

canonicalGate3FrameImplications :
  List Gate3FrameImplication
canonicalGate3FrameImplications =
  ASplitPositiveUsesMirrorAForSplitPrimes
  ∷ AInertPositiveUsesMirrorBForInertPrimes
  ∷ ARamifiedP7Structural
  ∷ phaseBlindDictionaryFailsAtNineInertPrimes
  ∷ mirrorBSevenVariablesSpanNineInertPrimeSpace
  ∷ atomGrammarArchitecturalNotCMSplitting
  ∷ []

canonicalSSP15Primes :
  List Nat
canonicalSSP15Primes =
  CM15.canonicalSSP15Primes

canonicalSplitPrimesForMirrorA :
  List Nat
canonicalSplitPrimesForMirrorA =
  CM15.canonicalQsqrtMinusSevenSplitPrimes

canonicalInertPrimesForMirrorB :
  List Nat
canonicalInertPrimesForMirrorB =
  CM15.canonicalQsqrtMinusSevenInertPrimes

canonicalRamifiedStructuralPrimes :
  List Nat
canonicalRamifiedStructuralPrimes =
  CM15.canonicalQsqrtMinusSevenRamifiedPrimes

atomGrammarFrameStatement :
  String
atomGrammarFrameStatement =
  "SSP atom grammar frame: MirrorA has position, scale, amplitude, orientation, anisotropy, curvature, depth; MirrorB has phase, twist, helicity, torsion, pressureGradient, transportDirection, memoryCarry; signLane has sign."

gate3FrameImplicationStatement :
  String
gate3FrameImplicationStatement =
  "Gate 3: A_split > 0 uses MirrorA for split primes {2,11,23,29,71}; A_inert > 0 uses MirrorB for inert primes {3,5,13,17,19,31,41,47,59}; p=7 is ramified structural."

architecturalBoundaryStatement :
  String
architecturalBoundaryStatement =
  "The 7+7+1 atom grammar is architectural and not a CM splitting theorem."

noClayPromotionStatement :
  String
noClayPromotionStatement =
  "No Clay promotion is made by this atom-grammar frame receipt."

data SSPAtomGrammarFramePromotion : Set where

sspAtomGrammarFramePromotionImpossibleHere :
  SSPAtomGrammarFramePromotion →
  ⊥
sspAtomGrammarFramePromotionImpossibleHere ()

record SSP7Plus7Plus1AtomGrammarFrameReceipt : Setω where
  field
    status :
      SSPAtomGrammarFrameStatus

    statusIsCanonical :
      status
      ≡
      atomGrammarFrameRecorded_gate3Implication_noClayPromotion

    atomGrammarReceipt :
      Atom771.SSP7Plus7Plus1AtomGrammarReceipt

    atomGrammarReceiptStatusIsCanonical :
      Atom771.status atomGrammarReceipt
      ≡
      Atom771.atomGrammarCorrectionReceipt3Recorded_noClayPromotion

    cmSplittingReceipt :
      CM15.SSP15CMFieldSplittingCorrectionReceipt

    cmSplittingReceiptStatusIsCanonical :
      CM15.status cmSplittingReceipt
      ≡
      CM15.qsqrtMinusSevenSSP15SplittingCorrectionRecorded

    atomFrameLanes :
      List AtomFrameLane

    atomFrameLanesAreCanonical :
      atomFrameLanes ≡ canonicalAtomFrameLanes

    mirrorA :
      List MirrorAAtomField

    mirrorAIsCanonical :
      mirrorA ≡ canonicalMirrorAAtomFields

    mirrorAFieldCount :
      Nat

    mirrorAFieldCountIsSeven :
      mirrorAFieldCount ≡ 7

    mirrorB :
      List MirrorBAtomField

    mirrorBIsCanonical :
      mirrorB ≡ canonicalMirrorBAtomFields

    mirrorBFieldCount :
      Nat

    mirrorBFieldCountIsSeven :
      mirrorBFieldCount ≡ 7

    signLaneFields :
      List SignLaneAtomField

    signLaneFieldsAreCanonical :
      signLaneFields ≡ canonicalSignLaneAtomFields

    signLaneFieldCount :
      Nat

    signLaneFieldCountIsOne :
      signLaneFieldCount ≡ 1

    totalAtomFields :
      Nat

    totalAtomFieldsIsFifteen :
      totalAtomFields ≡ 15

    totalAtomFieldsEqualsAtomGrammarReceipt :
      totalAtomFields
      ≡
      Atom771.totalAtomFields atomGrammarReceipt

    totalAtomFieldsEqualsSSP15 :
      totalAtomFields
      ≡
      CM15.splitCount cmSplittingReceipt
      + CM15.inertCount cmSplittingReceipt
      + CM15.ramifiedCount cmSplittingReceipt

    ssp15Primes :
      List Nat

    ssp15PrimesAreCanonical :
      ssp15Primes ≡ canonicalSSP15Primes

    splitPrimes :
      List Nat

    splitPrimesAreMirrorACanonical :
      splitPrimes ≡ canonicalSplitPrimesForMirrorA

    splitPrimeCount :
      Nat

    splitPrimeCountIsFive :
      splitPrimeCount ≡ 5

    ASplitPositiveUsesMirrorA :
      Bool

    ASplitPositiveUsesMirrorAIsTrue :
      ASplitPositiveUsesMirrorA ≡ true

    inertPrimes :
      List Nat

    inertPrimesAreMirrorBCanonical :
      inertPrimes ≡ canonicalInertPrimesForMirrorB

    inertPrimeCount :
      Nat

    inertPrimeCountIsNine :
      inertPrimeCount ≡ 9

    AInertPositiveUsesMirrorB :
      Bool

    AInertPositiveUsesMirrorBIsTrue :
      AInertPositiveUsesMirrorB ≡ true

    ramifiedStructuralPrimes :
      List Nat

    ramifiedStructuralPrimesAreCanonical :
      ramifiedStructuralPrimes ≡ canonicalRamifiedStructuralPrimes

    ramifiedStructuralPrimeCount :
      Nat

    ramifiedStructuralPrimeCountIsOne :
      ramifiedStructuralPrimeCount ≡ 1

    p7RamifiedStructural :
      Bool

    p7RamifiedStructuralIsTrue :
      p7RamifiedStructural ≡ true

    gate3FrameImplications :
      List Gate3FrameImplication

    gate3FrameImplicationsAreCanonical :
      gate3FrameImplications ≡ canonicalGate3FrameImplications

    phaseBlindDictionaryFailsAt9InertPrimes :
      Bool

    phaseBlindDictionaryFailsAt9InertPrimesIsTrue :
      phaseBlindDictionaryFailsAt9InertPrimes ≡ true

    phaseBlindDictionaryFailureMatchesAtomGrammarReceipt :
      phaseBlindDictionaryFailsAt9InertPrimes
      ≡
      Atom771.phaseBlindDictionaryFailsAt9InertPrimes atomGrammarReceipt

    mirrorB7VariablesSpan9InertPrimeSpace :
      Bool

    mirrorB7VariablesSpan9InertPrimeSpaceIsTrue :
      mirrorB7VariablesSpan9InertPrimeSpace ≡ true

    atomGrammar7plus7plus1IsArchitecturalNotCMSplitting :
      Bool

    atomGrammar7plus7plus1IsArchitecturalNotCMSplittingIsTrue :
      atomGrammar7plus7plus1IsArchitecturalNotCMSplitting ≡ true

    atomGrammarNotCMSplittingMatchesReceipt :
      atomGrammar7plus7plus1IsArchitecturalNotCMSplitting
      ≡
      Atom771.atomGrammarDistinctFromCMSplitting atomGrammarReceipt

    cmSplittingIsSeparateReceipt :
      Bool

    cmSplittingIsSeparateReceiptIsTrue :
      cmSplittingIsSeparateReceipt ≡ true

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    promotions :
      List SSPAtomGrammarFramePromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      SSPAtomGrammarFramePromotion →
      ⊥

    atomGrammarFrameBoundary :
      String

    atomGrammarFrameBoundaryIsCanonical :
      atomGrammarFrameBoundary ≡ atomGrammarFrameStatement

    gate3FrameImplicationBoundary :
      String

    gate3FrameImplicationBoundaryIsCanonical :
      gate3FrameImplicationBoundary ≡ gate3FrameImplicationStatement

    architecturalBoundary :
      String

    architecturalBoundaryIsCanonical :
      architecturalBoundary ≡ architecturalBoundaryStatement

    noClayPromotionBoundary :
      String

    noClayPromotionBoundaryIsCanonical :
      noClayPromotionBoundary ≡ noClayPromotionStatement

    receiptBoundary :
      List String

open SSP7Plus7Plus1AtomGrammarFrameReceipt public

canonicalSSP7Plus7Plus1AtomGrammarFrameReceipt :
  SSP7Plus7Plus1AtomGrammarFrameReceipt
canonicalSSP7Plus7Plus1AtomGrammarFrameReceipt =
  record
    { status =
        atomGrammarFrameRecorded_gate3Implication_noClayPromotion
    ; statusIsCanonical =
        refl
    ; atomGrammarReceipt =
        Atom771.canonicalSSP7Plus7Plus1AtomGrammarReceipt
    ; atomGrammarReceiptStatusIsCanonical =
        refl
    ; cmSplittingReceipt =
        CM15.canonicalSSP15CMFieldSplittingCorrectionReceipt
    ; cmSplittingReceiptStatusIsCanonical =
        refl
    ; atomFrameLanes =
        canonicalAtomFrameLanes
    ; atomFrameLanesAreCanonical =
        refl
    ; mirrorA =
        canonicalMirrorAAtomFields
    ; mirrorAIsCanonical =
        refl
    ; mirrorAFieldCount =
        7
    ; mirrorAFieldCountIsSeven =
        refl
    ; mirrorB =
        canonicalMirrorBAtomFields
    ; mirrorBIsCanonical =
        refl
    ; mirrorBFieldCount =
        7
    ; mirrorBFieldCountIsSeven =
        refl
    ; signLaneFields =
        canonicalSignLaneAtomFields
    ; signLaneFieldsAreCanonical =
        refl
    ; signLaneFieldCount =
        1
    ; signLaneFieldCountIsOne =
        refl
    ; totalAtomFields =
        15
    ; totalAtomFieldsIsFifteen =
        refl
    ; totalAtomFieldsEqualsAtomGrammarReceipt =
        refl
    ; totalAtomFieldsEqualsSSP15 =
        refl
    ; ssp15Primes =
        canonicalSSP15Primes
    ; ssp15PrimesAreCanonical =
        refl
    ; splitPrimes =
        canonicalSplitPrimesForMirrorA
    ; splitPrimesAreMirrorACanonical =
        refl
    ; splitPrimeCount =
        5
    ; splitPrimeCountIsFive =
        refl
    ; ASplitPositiveUsesMirrorA =
        true
    ; ASplitPositiveUsesMirrorAIsTrue =
        refl
    ; inertPrimes =
        canonicalInertPrimesForMirrorB
    ; inertPrimesAreMirrorBCanonical =
        refl
    ; inertPrimeCount =
        9
    ; inertPrimeCountIsNine =
        refl
    ; AInertPositiveUsesMirrorB =
        true
    ; AInertPositiveUsesMirrorBIsTrue =
        refl
    ; ramifiedStructuralPrimes =
        canonicalRamifiedStructuralPrimes
    ; ramifiedStructuralPrimesAreCanonical =
        refl
    ; ramifiedStructuralPrimeCount =
        1
    ; ramifiedStructuralPrimeCountIsOne =
        refl
    ; p7RamifiedStructural =
        true
    ; p7RamifiedStructuralIsTrue =
        refl
    ; gate3FrameImplications =
        canonicalGate3FrameImplications
    ; gate3FrameImplicationsAreCanonical =
        refl
    ; phaseBlindDictionaryFailsAt9InertPrimes =
        true
    ; phaseBlindDictionaryFailsAt9InertPrimesIsTrue =
        refl
    ; phaseBlindDictionaryFailureMatchesAtomGrammarReceipt =
        refl
    ; mirrorB7VariablesSpan9InertPrimeSpace =
        true
    ; mirrorB7VariablesSpan9InertPrimeSpaceIsTrue =
        refl
    ; atomGrammar7plus7plus1IsArchitecturalNotCMSplitting =
        true
    ; atomGrammar7plus7plus1IsArchitecturalNotCMSplittingIsTrue =
        refl
    ; atomGrammarNotCMSplittingMatchesReceipt =
        refl
    ; cmSplittingIsSeparateReceipt =
        true
    ; cmSplittingIsSeparateReceiptIsTrue =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        sspAtomGrammarFramePromotionImpossibleHere
    ; atomGrammarFrameBoundary =
        atomGrammarFrameStatement
    ; atomGrammarFrameBoundaryIsCanonical =
        refl
    ; gate3FrameImplicationBoundary =
        gate3FrameImplicationStatement
    ; gate3FrameImplicationBoundaryIsCanonical =
        refl
    ; architecturalBoundary =
        architecturalBoundaryStatement
    ; architecturalBoundaryIsCanonical =
        refl
    ; noClayPromotionBoundary =
        noClayPromotionStatement
    ; noClayPromotionBoundaryIsCanonical =
        refl
    ; receiptBoundary =
        "MirrorA = {position, scale, amplitude, orientation, anisotropy, curvature, depth}"
        ∷ "MirrorB = {phase, twist, helicity, torsion, pressureGradient, transportDirection, memoryCarry}"
        ∷ "signLane = {sign}"
        ∷ "totalAtomFields = 15 = |SSP15|"
        ∷ "A_split > 0 uses MirrorA for split primes {2,11,23,29,71}"
        ∷ "A_inert > 0 uses MirrorB for inert primes {3,5,13,17,19,31,41,47,59}"
        ∷ "A_ramified is structural for p=7"
        ∷ "phaseBlindDictionaryFailsAt9InertPrimes = true"
        ∷ "mirrorB7VariablesSpan9InertPrimeSpace = true"
        ∷ "atomGrammar7plus7plus1IsArchitecturalNotCMSplitting = true"
        ∷ "Clay promotion remains false"
        ∷ []
    }

mirrorAAtomGrammarFrameCountIs7 :
  mirrorAFieldCount canonicalSSP7Plus7Plus1AtomGrammarFrameReceipt ≡ 7
mirrorAAtomGrammarFrameCountIs7 =
  refl

mirrorBAtomGrammarFrameCountIs7 :
  mirrorBFieldCount canonicalSSP7Plus7Plus1AtomGrammarFrameReceipt ≡ 7
mirrorBAtomGrammarFrameCountIs7 =
  refl

signLaneAtomGrammarFrameCountIs1 :
  signLaneFieldCount canonicalSSP7Plus7Plus1AtomGrammarFrameReceipt ≡ 1
signLaneAtomGrammarFrameCountIs1 =
  refl

totalAtomGrammarFrameFieldsIsSSP15 :
  totalAtomFields canonicalSSP7Plus7Plus1AtomGrammarFrameReceipt ≡ 15
totalAtomGrammarFrameFieldsIsSSP15 =
  refl

gate3SplitFrameUsesMirrorA :
  ASplitPositiveUsesMirrorA
    canonicalSSP7Plus7Plus1AtomGrammarFrameReceipt
  ≡
  true
gate3SplitFrameUsesMirrorA =
  refl

gate3InertFrameUsesMirrorB :
  AInertPositiveUsesMirrorB
    canonicalSSP7Plus7Plus1AtomGrammarFrameReceipt
  ≡
  true
gate3InertFrameUsesMirrorB =
  refl

gate3RamifiedSevenIsStructural :
  p7RamifiedStructural canonicalSSP7Plus7Plus1AtomGrammarFrameReceipt
  ≡
  true
gate3RamifiedSevenIsStructural =
  refl

phaseBlindFailsAtNineInertPrimes :
  phaseBlindDictionaryFailsAt9InertPrimes
    canonicalSSP7Plus7Plus1AtomGrammarFrameReceipt
  ≡
  true
phaseBlindFailsAtNineInertPrimes =
  refl

mirrorBSevenSpansNineInertPrimeSpace :
  mirrorB7VariablesSpan9InertPrimeSpace
    canonicalSSP7Plus7Plus1AtomGrammarFrameReceipt
  ≡
  true
mirrorBSevenSpansNineInertPrimeSpace =
  refl

atomGrammarFrameArchitecturalNotCMSplitting :
  atomGrammar7plus7plus1IsArchitecturalNotCMSplitting
    canonicalSSP7Plus7Plus1AtomGrammarFrameReceipt
  ≡
  true
atomGrammarFrameArchitecturalNotCMSplitting =
  refl

atomGrammarFrameHasNoClayPromotion :
  clayPromoted canonicalSSP7Plus7Plus1AtomGrammarFrameReceipt ≡ false
atomGrammarFrameHasNoClayPromotion =
  refl
