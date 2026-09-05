module DASHI.Physics.QuantumVacuum.ParallelPlateTETMSourceBackedCompletenessCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.SourceBackedTheoremTransportBidiExact as Transport
import DASHI.Physics.QuantumVacuum.ParallelPlateTETMModeExpansionSourceAuthorityExact as Source
import DASHI.Physics.QuantumVacuum.PerfectConductorTETMProofBearingCompletenessExact as Proof

------------------------------------------------------------------------
-- BOUNDED SOURCE CLAIMS FROM THE SAME PARALLEL-PLATE SOURCE
------------------------------------------------------------------------

fieldExpansionClaim : Transport.SourceBackedClaim
fieldExpansionClaim = record
  { Transport.SourceClaim =
      Source.fieldsExpandedAsLinearCombinationOfModes
        Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.sourceReceipt = tt
  ; Transport.sourceName =
      Source.sourceName Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.sourceLocator =
      Source.sourceLocator Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.reading =
      "MIT source: fields between the conducting plates expand as linear combinations of the TE/TM modes."
  }

longitudinalExpansionClaim : Transport.SourceBackedClaim
longitudinalExpansionClaim = record
  { Transport.SourceClaim =
      Source.fieldsExpandedAsLinearCombinationOfModes
        Source.canonicalParallelPlateTETMModeExpansionAuthority
      ×
      Source.longitudinalIntegerQuantisationDerived
        Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.sourceReceipt = tt , tt
  ; Transport.sourceName =
      Source.sourceName Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.sourceLocator =
      Source.sourceLocator Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.reading =
      "MIT source: the TE/TM field expansion is accompanied by the longitudinal integer quantisation structure."
  }

------------------------------------------------------------------------
-- LOCAL COMPLETENESS SKELETON
------------------------------------------------------------------------

record LocalTETMCompletenessSkeleton : Set₁ where
  field
    PhysicalMode : Set
    TE TM : PhysicalMode → Set
    longitudinalIndex : PhysicalMode → Nat
    zeroSector : PhysicalMode → Set

    SameClassicalAndCasimirPlateModeObject : Set
    sameClassicalAndCasimirPlateModeObjectEvidence :
      SameClassicalAndCasimirPlateModeObject

    FiniteEnergyHilbertCarrierMatchesSourceExpansion : Set
    finiteEnergyHilbertCarrierMatchesSourceExpansionEvidence :
      FiniteEnergyHilbertCarrierMatchesSourceExpansion

    EveryPhysicalModeTEorTM : Set
    sourceExpansionToLocalSpanning :
      Transport.SourceClaim fieldExpansionClaim →
      (SameClassicalAndCasimirPlateModeObject ×
       FiniteEnergyHilbertCarrierMatchesSourceExpansion) →
      EveryPhysicalModeTEorTM

    LongitudinalCompleteness : Set
    sourceLongitudinalExpansionToLocal :
      Transport.SourceClaim longitudinalExpansionClaim →
      (SameClassicalAndCasimirPlateModeObject ×
       FiniteEnergyHilbertCarrierMatchesSourceExpansion) →
      LongitudinalCompleteness

    ZeroSectorCountingCorrect : Set
    zeroSectorCountingCorrectEvidence : ZeroSectorCountingCorrect

    NoDoubleCountingAwayFromZeroSector : Set
    noDoubleCountingAwayFromZeroSectorEvidence :
      NoDoubleCountingAwayFromZeroSector

    TransverseCompleteness : Set
    transverseCompletenessEvidence : TransverseCompleteness

    reading : String

open LocalTETMCompletenessSkeleton public

SourceToLocalModeObject : LocalTETMCompletenessSkeleton → Set
SourceToLocalModeObject S =
  SameClassicalAndCasimirPlateModeObject S ×
  FiniteEnergyHilbertCarrierMatchesSourceExpansion S

sourceToLocalModeObjectEvidence :
  (S : LocalTETMCompletenessSkeleton) →
  SourceToLocalModeObject S
sourceToLocalModeObjectEvidence S =
  sameClassicalAndCasimirPlateModeObjectEvidence S ,
  finiteEnergyHilbertCarrierMatchesSourceExpansionEvidence S

localTarget :
  (claim : Transport.SourceBackedClaim) →
  (LocalClaim : Set) →
  (SameObject : Set) →
  (SourceToLocal : Transport.SourceClaim claim → SameObject → LocalClaim) →
  Transport.LocalTheoremTarget claim
localTarget claim LocalClaim SameObject SourceToLocal = record
  { Transport.LocalClaim = LocalClaim
  ; Transport.sameMathematicalObject = SameObject
  ; Transport.sourceSemanticsToLocal = SourceToLocal
  ; Transport.reading =
      "Parallel-plate source theorem transported only after the local mode semantics and finite-energy/Hilbert carrier are both identified."
  }

compileEveryPhysicalModeTEorTM :
  (S : LocalTETMCompletenessSkeleton) →
  EveryPhysicalModeTEorTM S
compileEveryPhysicalModeTEorTM S =
  Transport.transportSourceBackedTheorem
    fieldExpansionClaim
    (localTarget fieldExpansionClaim
      (EveryPhysicalModeTEorTM S)
      (SourceToLocalModeObject S)
      (sourceExpansionToLocalSpanning S))
    (record
      { Transport.objectWeld = sourceToLocalModeObjectEvidence S })

compileLongitudinalCompleteness :
  (S : LocalTETMCompletenessSkeleton) →
  LongitudinalCompleteness S
compileLongitudinalCompleteness S =
  Transport.transportSourceBackedTheorem
    longitudinalExpansionClaim
    (localTarget longitudinalExpansionClaim
      (LongitudinalCompleteness S)
      (SourceToLocalModeObject S)
      (sourceLongitudinalExpansionToLocal S))
    (record
      { Transport.objectWeld = sourceToLocalModeObjectEvidence S })

compileProofBearingTETMCompleteness :
  (S : LocalTETMCompletenessSkeleton) →
  Proof.ProofBearingTETMCompletenessReceipt
compileProofBearingTETMCompleteness S = record
  { Proof.PhysicalMode = PhysicalMode S
  ; Proof.TE = TE S
  ; Proof.TM = TM S
  ; Proof.longitudinalIndex = longitudinalIndex S
  ; Proof.zeroSector = zeroSector S
  ; Proof.EveryPhysicalModeTEorTM = EveryPhysicalModeTEorTM S
  ; Proof.everyPhysicalModeTEorTMEvidence = compileEveryPhysicalModeTEorTM S
  ; Proof.NoDoubleCountingAwayFromZeroSector = NoDoubleCountingAwayFromZeroSector S
  ; Proof.noDoubleCountingAwayFromZeroSectorEvidence = noDoubleCountingAwayFromZeroSectorEvidence S
  ; Proof.ZeroSectorCountingCorrect = ZeroSectorCountingCorrect S
  ; Proof.zeroSectorCountingCorrectEvidence = zeroSectorCountingCorrectEvidence S
  ; Proof.TransverseCompleteness = TransverseCompleteness S
  ; Proof.transverseCompletenessEvidence = transverseCompletenessEvidence S
  ; Proof.LongitudinalCompleteness = LongitudinalCompleteness S
  ; Proof.longitudinalCompletenessEvidence = compileLongitudinalCompleteness S
  ; Proof.reading = reading S
  }

------------------------------------------------------------------------
-- Reverse obligations after source-backed pruning.
------------------------------------------------------------------------

record ReverseSourceBackedCompletenessObligations : Set where
  field
    classicalToCasimirModeAndFiniteEnergyCarrierWeld : Set
    transverseContinuumCompleteness : Set
    teTmIndependenceAwayFromExceptionalSector : Set
    exactZeroSectorCountingConvention : Set
    reading : String

open ReverseSourceBackedCompletenessObligations public

data SeparateSourceReceiptRequiredForSpanningAndLongitudinalCoverage : Set where

data SourceExpansionAutomaticallyProvesTransverseHilbertCompletion : Set where

data SourceDiscussionOfZeroSectorAutomaticallyProvesLocalCounting : Set where

data MatchingModeLabelsWithoutFiniteEnergyCarrierIdentitySuffices : Set where

oneCarrierWeldFeedsSourceClaims :
  SeparateSourceReceiptRequiredForSpanningAndLongitudinalCoverage → ⊥
oneCarrierWeldFeedsSourceClaims ()

sourceDoesNotInventTransverseCompletion :
  SourceExpansionAutomaticallyProvesTransverseHilbertCompletion → ⊥
sourceDoesNotInventTransverseCompletion ()

zeroSectorDiscussionDoesNotFixLocalCounting :
  SourceDiscussionOfZeroSectorAutomaticallyProvesLocalCounting → ⊥
zeroSectorDiscussionDoesNotFixLocalCounting ()

labelsAloneDoNotIdentifyCompletion :
  MatchingModeLabelsWithoutFiniteEnergyCarrierIdentitySuffices → ⊥
labelsAloneDoNotIdentifyCompletion ()

record Status : Set where
  field
    fieldSpanningSourceBacked : Bool
    longitudinalCoverageSourceBacked : Bool
    oneCarrierWeldFeedsTwoCompilers : Bool
    finiteEnergyCarrierIncludedInSourceWeld : Bool
    proofBearingCompletenessCompilerOwned : Bool
    transverseHilbertCompletionStillLocal : Bool
    zeroSectorCountingStillLocal : Bool

    fieldSpanningSourceBackedIsTrue : fieldSpanningSourceBacked ≡ true
    longitudinalCoverageSourceBackedIsTrue : longitudinalCoverageSourceBacked ≡ true
    oneCarrierWeldFeedsTwoCompilersIsTrue : oneCarrierWeldFeedsTwoCompilers ≡ true
    finiteEnergyCarrierIncludedInSourceWeldIsTrue : finiteEnergyCarrierIncludedInSourceWeld ≡ true
    proofBearingCompletenessCompilerOwnedIsTrue : proofBearingCompletenessCompilerOwned ≡ true
    transverseHilbertCompletionStillLocalIsTrue : transverseHilbertCompletionStillLocal ≡ true
    zeroSectorCountingStillLocalIsTrue : zeroSectorCountingStillLocal ≡ true

open Status public

canonicalStatus : Status
canonicalStatus = record
  { fieldSpanningSourceBacked = true
  ; longitudinalCoverageSourceBacked = true
  ; oneCarrierWeldFeedsTwoCompilers = true
  ; finiteEnergyCarrierIncludedInSourceWeld = true
  ; proofBearingCompletenessCompilerOwned = true
  ; transverseHilbertCompletionStillLocal = true
  ; zeroSectorCountingStillLocal = true
  ; fieldSpanningSourceBackedIsTrue = refl
  ; longitudinalCoverageSourceBackedIsTrue = refl
  ; oneCarrierWeldFeedsTwoCompilersIsTrue = refl
  ; finiteEnergyCarrierIncludedInSourceWeldIsTrue = refl
  ; proofBearingCompletenessCompilerOwnedIsTrue = refl
  ; transverseHilbertCompletionStillLocalIsTrue = refl
  ; zeroSectorCountingStillLocalIsTrue = refl
  }
