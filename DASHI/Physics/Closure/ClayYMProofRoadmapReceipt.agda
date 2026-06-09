module DASHI.Physics.Closure.ClayYMProofRoadmapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayBlockerUpdateReceipt as Blocker
import DASHI.Physics.Closure.ClayMillenniumClosureTargetReceipt as Target
import DASHI.Physics.Closure.ScalarOSTransferMatrixReceipt as ScalarOS

------------------------------------------------------------------------
-- Yang-Mills Clay roadmap receipt.
--
-- This receipt records that the human-readable proof roadmap exists and
-- decomposes the current blocker map into a nine-lemma dependency chain.  It
-- deliberately consumes only fail-closed status from existing receipts.

data YMRoadmapLemma : Set where
  latticeYMMeasure :
    YMRoadmapLemma

  uniformCorrelatorBounds :
    YMRoadmapLemma

  cutoffMeasureTightness :
    YMRoadmapLemma

  continuumWeakLimit :
    YMRoadmapLemma

  continuumOSAxioms :
    YMRoadmapLemma

  wightmanReconstruction :
    YMRoadmapLemma

  uniformTransferSpectralGap :
    YMRoadmapLemma

  continuumGapSurvival :
    YMRoadmapLemma

  physicalMassGapIdentification :
    YMRoadmapLemma

canonicalYMRoadmapLemmas : List YMRoadmapLemma
canonicalYMRoadmapLemmas =
  latticeYMMeasure
  ∷ uniformCorrelatorBounds
  ∷ cutoffMeasureTightness
  ∷ continuumWeakLimit
  ∷ continuumOSAxioms
  ∷ wightmanReconstruction
  ∷ uniformTransferSpectralGap
  ∷ continuumGapSurvival
  ∷ physicalMassGapIdentification
  ∷ []

ymRoadmapDocPath : String
ymRoadmapDocPath =
  "Docs/ClayYMProofRoadmap.md"

ymRoadmapStatement : String
ymRoadmapStatement =
  "Clay YM roadmap decomposes existence and mass-gap closure into L1-L9; current carrier status is scalar-sector OS plus finite/conditional RG scaffolding only."

record ClayYMProofRoadmapReceipt : Setω where
  field
    blockerUpdateReceipt :
      Blocker.ClayBlockerUpdateReceipt

    blockerUpdateKeepsYMClayFalse :
      Blocker.yangMillsMassGapClayPromoted blockerUpdateReceipt ≡ false

    blockerUpdateKeepsTerminalFalse :
      Blocker.terminalClayClaimPromoted blockerUpdateReceipt ≡ false

    targetReceipt :
      Target.CarrierOSPositivityAndWightmanTargetReceipt

    targetKeepsClayFalse :
      Target.clayYangMillsClosed targetReceipt ≡ false

    targetWightmanStillFalse :
      Target.wightmanReconstructionApplied targetReceipt ≡ false

    scalarOSReceipt :
      ScalarOS.ScalarOSTransferMatrixReceipt

    scalarOSRecorded :
      ScalarOS.osReflectionPositivityForScalar scalarOSReceipt ≡ true

    scalarOSDoesNotPromoteClay :
      ScalarOS.yangMillsClayPromoted scalarOSReceipt ≡ false

    roadmapDoc :
      String

    roadmapDocIsCanonical :
      roadmapDoc ≡ ymRoadmapDocPath

    lemmaCount :
      Nat

    lemmaCountIsNine :
      lemmaCount ≡ 9

    lemmas :
      List YMRoadmapLemma

    lemmasAreCanonical :
      lemmas ≡ canonicalYMRoadmapLemmas

    scalarOSOnlyPartial :
      Bool

    scalarOSOnlyPartialIsTrue :
      scalarOSOnlyPartial ≡ true

    gaugeYMMeasureConstructed :
      Bool

    gaugeYMMeasureConstructedIsFalse :
      gaugeYMMeasureConstructed ≡ false

    continuumYMConstructed :
      Bool

    continuumYMConstructedIsFalse :
      continuumYMConstructed ≡ false

    uniformMassGapConstructed :
      Bool

    uniformMassGapConstructedIsFalse :
      uniformMassGapConstructed ≡ false

    wightmanReconstructionConstructed :
      Bool

    wightmanReconstructionConstructedIsFalse :
      wightmanReconstructionConstructed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ ymRoadmapStatement

    receiptBoundary :
      List String

open ClayYMProofRoadmapReceipt public

canonicalClayYMProofRoadmapReceipt :
  ClayYMProofRoadmapReceipt
canonicalClayYMProofRoadmapReceipt =
  record
    { blockerUpdateReceipt =
        Blocker.canonicalClayBlockerUpdateReceipt
    ; blockerUpdateKeepsYMClayFalse =
        refl
    ; blockerUpdateKeepsTerminalFalse =
        refl
    ; targetReceipt =
        Target.canonicalCarrierOSPositivityAndWightmanTargetReceipt
    ; targetKeepsClayFalse =
        refl
    ; targetWightmanStillFalse =
        refl
    ; scalarOSReceipt =
        ScalarOS.canonicalScalarOSTransferMatrixReceipt
    ; scalarOSRecorded =
        refl
    ; scalarOSDoesNotPromoteClay =
        refl
    ; roadmapDoc =
        ymRoadmapDocPath
    ; roadmapDocIsCanonical =
        refl
    ; lemmaCount =
        9
    ; lemmaCountIsNine =
        refl
    ; lemmas =
        canonicalYMRoadmapLemmas
    ; lemmasAreCanonical =
        refl
    ; scalarOSOnlyPartial =
        true
    ; scalarOSOnlyPartialIsTrue =
        refl
    ; gaugeYMMeasureConstructed =
        false
    ; gaugeYMMeasureConstructedIsFalse =
        refl
    ; continuumYMConstructed =
        false
    ; continuumYMConstructedIsFalse =
        refl
    ; uniformMassGapConstructed =
        false
    ; uniformMassGapConstructedIsFalse =
        refl
    ; wightmanReconstructionConstructed =
        false
    ; wightmanReconstructionConstructedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; statement =
        ymRoadmapStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "The roadmap is a dependency graph, not a proof"
        ∷ "Scalar-sector OS positivity is the only inhabited necessary condition recorded here"
        ∷ "Gauge YM measure, continuum construction, Wightman reconstruction, and uniform mass gap remain false"
        ∷ []
    }

clayYMRoadmapKeepsClayFalse :
  clayYangMillsPromoted canonicalClayYMProofRoadmapReceipt ≡ false
clayYMRoadmapKeepsClayFalse =
  refl

clayYMRoadmapKeepsTerminalFalse :
  terminalClaimPromoted canonicalClayYMProofRoadmapReceipt ≡ false
clayYMRoadmapKeepsTerminalFalse =
  refl
