module DASHI.Physics.QuantumVacuum.ParallelPlateTETMSourceBackedCompletenessCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.SourceBackedTheoremTransportBidiExact as Transport
import DASHI.Physics.QuantumVacuum.ParallelPlateTETMModeExpansionSourceAuthorityExact as Source
import DASHI.Physics.QuantumVacuum.PerfectConductorTETMProofBearingCompletenessExact as Proof

------------------------------------------------------------------------
-- FOUR BOUNDED SOURCE CLAIMS FROM THE SAME PARALLEL-PLATE SOURCE
------------------------------------------------------------------------

teTmGenerationClaim : Transport.SourceBackedClaim
teTmGenerationClaim = record
  { Transport.SourceClaim = Source.teTmModesDerived Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.sourceReceipt = tt
  ; Transport.sourceName = Source.sourceName Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.sourceLocator = Source.sourceLocator Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.reading = "MIT source: TE/TM modes are derived for the conducting parallel-plate problem."
  }

longitudinalQuantisationClaim : Transport.SourceBackedClaim
longitudinalQuantisationClaim = record
  { Transport.SourceClaim = Source.longitudinalIntegerQuantisationDerived Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.sourceReceipt = tt
  ; Transport.sourceName = Source.sourceName Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.sourceLocator = Source.sourceLocator Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.reading = "MIT source: longitudinal plate modes carry the integer quantisation structure."
  }

fieldExpansionClaim : Transport.SourceBackedClaim
fieldExpansionClaim = record
  { Transport.SourceClaim = Source.fieldsExpandedAsLinearCombinationOfModes Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.sourceReceipt = tt
  ; Transport.sourceName = Source.sourceName Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.sourceLocator = Source.sourceLocator Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.reading = "MIT source: fields between the plates expand as linear combinations of the TE/TM modes."
  }

zeroSectorClaim : Transport.SourceBackedClaim
zeroSectorClaim = record
  { Transport.SourceClaim = Source.exceptionalZeroSectorDiscussed Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.sourceReceipt = tt
  ; Transport.sourceName = Source.sourceName Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.sourceLocator = Source.sourceLocator Source.canonicalParallelPlateTETMModeExpansionAuthority
  ; Transport.reading = "MIT source: the exceptional zero sector is treated explicitly."
  }

------------------------------------------------------------------------
-- LOCAL COMPLETENESS SKELETON
--
-- Source claims can compile the four source-level coordinates only after one
-- same-object carrier/convention weld.  The genuinely local Hilbert/transverse
-- and independence facts remain proof-bearing inputs.
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
    LongitudinalCompleteness : Set
    ZeroSectorCountingCorrect : Set

    sourceGenerationToLocal :
      Transport.SourceClaim teTmGenerationClaim →
      SameClassicalAndCasimirPlateModeObject →
      EveryPhysicalModeTEorTM

    sourceLongitudinalToLocal :
      Transport.SourceClaim longitudinalQuantisationClaim →
      SameClassicalAndCasimirPlateModeObject →
      LongitudinalCompleteness

    sourceZeroSectorToLocal :
      Transport.SourceClaim zeroSectorClaim →
      SameClassicalAndCasimirPlateModeObject →
      ZeroSectorCountingCorrect

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
  ; Transport.reading = "Parallel-plate source theorem transported only after the common local mode-object weld."
  }

compileEveryPhysicalModeTEorTM :
  (S : LocalTETMCompletenessSkeleton) →
  EveryPhysicalModeTEorTM S
compileEveryPhysicalModeTEorTM S =
  Transport.transportSourceBackedTheorem
    teTmGenerationClaim
    (localTarget teTmGenerationClaim
      (EveryPhysicalModeTEorTM S)
      (SameClassicalAndCasimirPlateModeObject S)
      (sourceGenerationToLocal S))
    (record
      { Transport.objectWeld = sameClassicalAndCasimirPlateModeObjectEvidence S })

compileLongitudinalCompleteness :
  (S : LocalTETMCompletenessSkeleton) →
  LongitudinalCompleteness S
compileLongitudinalCompleteness S =
  Transport.transportSourceBackedTheorem
    longitudinalQuantisationClaim
    (localTarget longitudinalQuantisationClaim
      (LongitudinalCompleteness S)
      (SameClassicalAndCasimirPlateModeObject S)
      (sourceLongitudinalToLocal S))
    (record
      { Transport.objectWeld = sameClassicalAndCasimirPlateModeObjectEvidence S })

compileZeroSectorCounting :
  (S : LocalTETMCompletenessSkeleton) →
  ZeroSectorCountingCorrect S
compileZeroSectorCounting S =
  Transport.transportSourceBackedTheorem
    zeroSectorClaim
    (localTarget zeroSectorClaim
      (ZeroSectorCountingCorrect S)
      (SameClassicalAndCasimirPlateModeObject S)
      (sourceZeroSectorToLocal S))
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
  ; Proof.zeroSectorCountingCorrectEvidence = compileZeroSectorCounting S
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
    reading : String

open ReverseSourceBackedCompletenessObligations public

data SeparateSourceReceiptRequiredForGenerationQuantisationAndZeroSector : Set where

data SourceExpansionAutomaticallyProvesTransverseHilbertCompletion : Set where

oneModeObjectWeldFeedsSourceClaims :
  SeparateSourceReceiptRequiredForGenerationQuantisationAndZeroSector → ⊥
oneModeObjectWeldFeedsSourceClaims ()

sourceDoesNotInventTransverseCompletion :
  SourceExpansionAutomaticallyProvesTransverseHilbertCompletion → ⊥
sourceDoesNotInventTransverseCompletion ()

record Status : Set where
  field
    teTmGenerationSourceBacked : Bool
    longitudinalCompletenessSourceBacked : Bool
    exceptionalZeroSectorSourceBacked : Bool
    oneModeObjectWeldFeedsThreeCompilers : Bool
    proofBearingCompletenessCompilerOwned : Bool
    transverseHilbertCompletionStillLocal : Bool

    teTmGenerationSourceBackedIsTrue : teTmGenerationSourceBacked ≡ true
    longitudinalCompletenessSourceBackedIsTrue : longitudinalCompletenessSourceBacked ≡ true
    exceptionalZeroSectorSourceBackedIsTrue : exceptionalZeroSectorSourceBacked ≡ true
    oneModeObjectWeldFeedsThreeCompilersIsTrue : oneModeObjectWeldFeedsThreeCompilers ≡ true
    proofBearingCompletenessCompilerOwnedIsTrue : proofBearingCompletenessCompilerOwned ≡ true
    transverseHilbertCompletionStillLocalIsTrue : transverseHilbertCompletionStillLocal ≡ true

open Status public

canonicalStatus : Status
canonicalStatus = record
  { teTmGenerationSourceBacked = true
  ; longitudinalCompletenessSourceBacked = true
  ; exceptionalZeroSectorSourceBacked = true
  ; oneModeObjectWeldFeedsThreeCompilers = true
  ; proofBearingCompletenessCompilerOwned = true
  ; transverseHilbertCompletionStillLocal = true
  ; teTmGenerationSourceBackedIsTrue = refl
  ; longitudinalCompletenessSourceBackedIsTrue = refl
  ; exceptionalZeroSectorSourceBackedIsTrue = refl
  ; oneModeObjectWeldFeedsThreeCompilersIsTrue = refl
  ; proofBearingCompletenessCompilerOwnedIsTrue = refl
  ; transverseHilbertCompletionStillLocalIsTrue = refl
  }
