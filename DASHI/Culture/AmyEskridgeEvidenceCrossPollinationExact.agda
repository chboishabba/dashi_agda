module DASHI.Culture.AmyEskridgeEvidenceCrossPollinationExact where

------------------------------------------------------------------------
-- ESKRIDGE EVIDENCE CROSS-POLLINATION
--
-- Reuses the generic evidence hyperfabric together with DASHI's governed
-- provenance calculus.  The key transfer is temporal/source-lineage discipline:
-- later repetition cannot retroactively become an independent pre-event source,
-- and a public classification cannot reconstruct hidden evidence coordinates.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.EvidenceHyperfabricExact as Evidence
import DASHI.Core.GovernedObservationProvenanceExact as Governed
import DASHI.Culture.AmyEskridgeEvidenceHyperfabricExact as Eskridge

------------------------------------------------------------------------
-- 1. Retrospective addition is new lineage, not restoration of inherited
-- pre-event evidence.
------------------------------------------------------------------------

postEventAdditionAfterErasureIsIntroduced :
  Governed.applyTwoEffects
    Governed.erasesCoordinate
    Governed.addsCoordinate
    Governed.inheritedCoordinate
  ≡ Governed.introducedCoordinate
postEventAdditionAfterErasureIsIntroduced =
  Governed.additionAfterErasureIsIntroducedNotInherited

postEventRepetitionCannotRestoreInheritedPreEventLineage :
  Governed.applyTwoEffects
    Governed.erasesCoordinate
    Governed.addsCoordinate
    Governed.inheritedCoordinate
  ≡ Governed.inheritedCoordinate → ⊥
postEventRepetitionCannotRestoreInheritedPreEventLineage =
  Governed.additionAfterErasureDoesNotRestoreInheritedLineage

------------------------------------------------------------------------
-- 2. Repetition and independence remain distinct source coordinates.
------------------------------------------------------------------------

sharedLineageIsNotIndependent :
  Evidence.sharedLineage ≡ Evidence.independent → ⊥
sharedLineageIsNotIndependent ()

independentIsNotSharedLineage :
  Evidence.independent ≡ Evidence.sharedLineage → ⊥
independentIsNotSharedLineage = Evidence.independent≠sharedLineage

------------------------------------------------------------------------
-- 3. The public label is provably insufficient for the residual evidence
-- coordinate in the Eskridge fixture.
------------------------------------------------------------------------

publicSurfaceDoesNotDetermineEvidenceFibre :
  Evidence.ResidualDescendsThroughPublicLabel
    Eskridge.publicLabel
    Eskridge.residualEvidence →
  ⊥
publicSurfaceDoesNotDetermineEvidenceFibre =
  Eskridge.publicLabelCannotReconstructEvidence

------------------------------------------------------------------------
-- 4. Missing-record semantics cross-pollinate directly into reopening logic:
-- notLocated is a live acquisition state, not a negative finding.
------------------------------------------------------------------------

notLocatedRecordIsNotNegativeFinding :
  Evidence.notLocated ≡ Evidence.knownAbsent → ⊥
notLocatedRecordIsNotNegativeFinding = Evidence.notLocated≠knownAbsent

------------------------------------------------------------------------
-- 5. Cross-domain boundary manifest.  These are reusable consequences, not
-- case-outcome claims.
------------------------------------------------------------------------

record CrossPollinationBoundary : Set where
  constructor crossPollinationBoundary
  field
    postEventAdditionRestoresPreEventLineage : Bool
    postEventAdditionRestoresPreEventLineageIsFalse :
      postEventAdditionRestoresPreEventLineage ≡ false
    repeatedSharedSourceCountsAsIndependentSource : Bool
    repeatedSharedSourceCountsAsIndependentSourceIsFalse :
      repeatedSharedSourceCountsAsIndependentSource ≡ false
    publicLabelDeterminesResidualEvidence : Bool
    publicLabelDeterminesResidualEvidenceIsFalse :
      publicLabelDeterminesResidualEvidence ≡ false
    notLocatedRecordCountsAsKnownAbsent : Bool
    notLocatedRecordCountsAsKnownAbsentIsFalse :
      notLocatedRecordCountsAsKnownAbsent ≡ false

canonicalCrossPollinationBoundary : CrossPollinationBoundary
canonicalCrossPollinationBoundary =
  crossPollinationBoundary
    false refl
    false refl
    false refl
    false refl
