module DASHI.Mathematics.NumberTheory.PrimeGap2026SourceAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.SourceAcquisitionGeometryExact as Acquisition
import DASHI.Mathematics.NumberTheory.PrimeGap2026ClaimAuditExact as Audit

------------------------------------------------------------------------
-- PRIME-GAP 2026 SOURCE ACQUISITION CUT
--
-- Current public evidence includes an announcement by Jared Duker Lichtman
-- that GPT-5.6 improved the large-prime-gap record and that Boris Alexeev has
-- formalized the result in Lean.  This owner does NOT promote that announcement
-- into the exact theorem statement, manuscript, Lean artifact, or statement
-- correspondence receipt.
--
-- The exact manuscript and exact Alexeev Lean target were not recovered during
-- this tranche.  Therefore the correct action is an explicit acquisition gate,
-- not an invented theorem transcription.
------------------------------------------------------------------------

primeGapManuscriptTarget : Acquisition.SourceAcquisitionTarget
primeGapManuscriptTarget =
  Acquisition.sourceAcquisitionTarget
    "2026 reported large-prime-gap improvement announced by Jared Duker Lichtman"
    "exact manuscript / theorem statement not yet recovered"
    Acquisition.directDigitalArchive
    Acquisition.publisherBackfile
    false
    false
    false

alexeevLeanTarget : Acquisition.SourceAcquisitionTarget
alexeevLeanTarget =
  Acquisition.sourceAcquisitionTarget
    "Boris Alexeev Lean formalization of the 2026 reported large-prime-gap improvement"
    "exact repository path, commit, theorem name and dependency closure not yet recovered"
    Acquisition.directDigitalArchive
    Acquisition.commercialBackfile
    false
    false
    false

manuscriptRecovered : Bool
manuscriptRecovered = Acquisition.fullTextAcquired primeGapManuscriptTarget

leanArtifactRecovered : Bool
leanArtifactRecovered = Acquisition.fullTextAcquired alexeevLeanTarget

exactStatementCorrespondenceChecked : Bool
exactStatementCorrespondenceChecked = false

manuscriptRecoveredIsFalse : manuscriptRecovered ≡ false
manuscriptRecoveredIsFalse = refl

leanArtifactRecoveredIsFalse : leanArtifactRecovered ≡ false
leanArtifactRecoveredIsFalse = refl

exactStatementCorrespondenceCheckedIsFalse :
  exactStatementCorrespondenceChecked ≡ false
exactStatementCorrespondenceCheckedIsFalse = refl

-- Existing claim-audit gate remains the authority surface once sources arrive.
promotionGate : Set
promotionGate = Audit.AgdaPromotionGate

record PrimeGapSourceAcquisitionBoundary : Set where
  constructor primeGapSourceAcquisitionBoundary
  field
    announcementEqualsExactTheoremStatement : Bool
    announcementEqualsExactTheoremStatementIsFalse :
      announcementEqualsExactTheoremStatement ≡ false
    reportedLeanFormalizationEqualsRecoveredLeanArtifact : Bool
    reportedLeanFormalizationEqualsRecoveredLeanArtifactIsFalse :
      reportedLeanFormalizationEqualsRecoveredLeanArtifact ≡ false
    theoremMayBeInventedWhilePrimarySourceMissing : Bool
    theoremMayBeInventedWhilePrimarySourceMissingIsFalse :
      theoremMayBeInventedWhilePrimarySourceMissing ≡ false

canonicalPrimeGapSourceAcquisitionBoundary : PrimeGapSourceAcquisitionBoundary
canonicalPrimeGapSourceAcquisitionBoundary =
  primeGapSourceAcquisitionBoundary false refl false refl false refl

sourceAcquisitionReading : String
sourceAcquisitionReading =
  "Stay at provenance/acquisition strength until the exact 2026 prime-gap manuscript and Alexeev Lean artifact are recovered; then compare the literal informal theorem to the literal Lean theorem before any Agda promotion."
