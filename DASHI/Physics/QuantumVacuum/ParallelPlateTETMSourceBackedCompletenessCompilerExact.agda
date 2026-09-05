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
--
-- The source can close spanning and longitudinal-index coverage only after one
-- same-object carrier/convention weld.  It does NOT by itself close the exact
-- zero-sector counting, transverse Hilbert completion, or TE/TM independence
-- convention used by the Casimir consumer.
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

    EveryPhysicalModeTEorTM : Set
    sourceExpansionToLocalSpanning :
      Transport.SourceClaim fieldExpansionClaim →
      SameClassicalAndCasimirPlateModeObject →
      EveryPhysicalModeTEorTM

    LongitudinalCompleteness : Set
    sourceLongitudinalExpansionToLocal :
      Transport.SourceClaim longitudinalExpansionClaim →
      SameClassicalAndCasimirPlateModeObject →
      LongitudinalCompleteness

    ZeroSectorCountingCorrect : Set
    zeroSectorCountingCorrectEvidence : ZeroSectorCountingCorrect

    NoDoubleCountingAwayFromZeroSector : Set
    noDoubleCountingAwayFromZeroSectorEvidence :
      NoDoubleCountingAwayFromZeroSector

    TransverseCompleteness : Set
    transverseCompletenessEvidence : TransverseCompleteness

    FiniteEnergyHilbertCarrierMatchesSourceExpansion : Set
    finiteEnergyHilbertCarrierMatchesSourceExpansionEvidence :
      FiniteEnergyHilbertCarrierMatchesSourceExpansion

    reading : String

open LocalTETMCompletenessSkeleton public

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
      "Parallel-plate source theorem transported only after the common local mode-object weld."
  }

compileEveryPhysicalModeTEorTM :
  (S : LocalTETMCompletenessSkeleton) →
  EveryPhysicalModeTEorTM S
compileEveryPhysicalModeTEorTM S =
  Transport.transportSourceBackedTheorem
    fieldExpansionClaim
    (localTarget fieldExpansionClaim
      (EveryPhysicalModeTEorTM S)
      (SameClassicalAndCasimirPlateModeObject S)
      (sourceExpansionToLocalSpanning S))
    (record
      { Transport.objectWeld = sameClassicalAndCasimirPlateModeObjectEvidence S })

compileLongitudinalCompleteness :
  (S : LocalTETMCompletenessSkeleton) →
  LongitudinalCompleteness S
compileLongitudinalCompleteness S =
  Transport.transportSourceBackedTheorem
    longitudinalExpansionClaim
    (localTarget longitudinalExpansionClaim
      (LongitudinalCompleteness S)
      (SameClassicalAndCasimirPlateModeObject S)
      (sourceLongitudinalExpansionToLocal S))
    (record
      { Transport.objectWeld = sameClassicalAndCasimirPlateModeObjectEvidence S })

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
    oneClassicalToCasimirModeObjectWeld : Set
    finiteEnergyHilbertCarrierIdentification : Set
    transverseContinuumCompleteness : Set
    teTmIndependenceAwayFromExceptionalSector : Set
    exactZeroSectorCountingConvention : Set
    reading : String

open ReverseSourceBackedCompletenessObligations public

data SeparateSourceReceiptRequiredForSpanningAndLongitudinalCoverage : Set where

data SourceExpansionAutomaticallyProvesTransverseHilbertCompletion : Set where

data SourceDiscussionOfZeroSectorAutomaticallyProvesLocalCounting : Set where

oneModeObjectWeldFeedsSourceClaims :
  SeparateSourceReceiptRequiredForSpanningAndLongitudinalCoverage → ⊥
oneModeObjectWeldFeedsSourceClaims ()

sourceDoesNotInventTransverseCompletion :
  SourceExpansionAutomaticallyProvesTransverseHilbertCompletion → ⊥
sourceDoesNotInventTransverseCompletion ()

zeroSectorDiscussionDoesNotFixLocalCounting :
  SourceDiscussionOfZeroSectorAutomaticallyProvesLocalCounting → ⊥
zeroSectorDiscussionDoesNotFixLocalCounting ()

record Status : Set where
  field
    fieldSpanningSourceBacked : Bool
    longitudinalCoverageSourceBacked : Bool
    oneModeObjectWeldFeedsTwoCompilers : Bool
    proofBearingCompletenessCompilerOwned : Bool
    transverseHilbertCompletionStillLocal : Bool
    zeroSectorCountingStillLocal : Bool

    fieldSpanningSourceBackedIsTrue : fieldSpanningSourceBacked ≡ true
    longitudinalCoverageSourceBackedIsTrue : longitudinalCoverageSourceBacked ≡ true
    oneModeObjectWeldFeedsTwoCompilersIsTrue : oneModeObjectWeldFeedsTwoCompilers ≡ true
    proofBearingCompletenessCompilerOwnedIsTrue : proofBearingCompletenessCompilerOwned ≡ true
    transverseHilbertCompletionStillLocalIsTrue : transverseHilbertCompletionStillLocal ≡ true
    zeroSectorCountingStillLocalIsTrue : zeroSectorCountingStillLocal ≡ true

open Status public

canonicalStatus : Status
canonicalStatus = record
  { fieldSpanningSourceBacked = true
  ; longitudinalCoverageSourceBacked = true
  ; oneModeObjectWeldFeedsTwoCompilers = true
  ; proofBearingCompletenessCompilerOwned = true
  ; transverseHilbertCompletionStillLocal = true
  ; zeroSectorCountingStillLocal = true
  ; fieldSpanningSourceBackedIsTrue = refl
  ; longitudinalCoverageSourceBackedIsTrue = refl
  ; oneModeObjectWeldFeedsTwoCompilersIsTrue = refl
  ; proofBearingCompletenessCompilerOwnedIsTrue = refl
  ; transverseHilbertCompletionStillLocalIsTrue = refl
  ; zeroSectorCountingStillLocalIsTrue = refl
  }
