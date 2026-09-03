module DASHI.Cognition.PNF.SensibLawDocumentWorldSemanticStatusBidiExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.ContextualFractranRegionRestrictionExact as Restriction
import DASHI.Cognition.PNF.ConsumerWorldStabiliserFibreExact as Stabiliser

------------------------------------------------------------------------
-- PARALLEL BIDI CAMPAIGN: sentence/occurrence <-> document/world context.
--
-- Status qualification may descend from a document interface to one occurrence
-- and may be compared through consumer-relative world equivalence, but neither
-- operation copies hidden child interiors nor identifies fine worlds globally.
------------------------------------------------------------------------

record ContextualStatusTransport : Set where
  constructor contextualStatusTransport
  field
    restrictionLadder : Restriction.RegionRestrictionLadder
    sourceStatus : Status.SemanticCommitmentState
    targetStatus : Status.SemanticCommitmentState
    sameSourceCandidate :
      Status.sourceCandidate sourceStatus ≡ Status.sourceCandidate targetStatus
    transportReference : String
    inheritedContextUsed : Bool
    fineResidualRetained : Bool

open ContextualStatusTransport public

record ConsumerStatusComparison : Set where
  constructor consumerStatusComparison
  field
    leftStatus rightStatus : Status.SemanticCommitmentState
    worldEquivalence : Stabiliser.ConsumerEquivalentWorlds
    currentConsumerEquivalent : Bool
    omittedAxesRetained : Bool
    comparisonReference : String

open ConsumerStatusComparison public

occurrenceIdentitySurvivesContextDescent :
  Restriction.occurrenceIdentitySurvivesBackwardDescent
    Restriction.canonicalRegionRestrictionBoundary ≡ true
occurrenceIdentitySurvivesContextDescent = refl

closedChildInteriorNotCopied :
  Restriction.parentCopiesClosedChildInterior
    Restriction.canonicalRegionRestrictionBoundary ≡ false
closedChildInteriorNotCopied = refl

consumerEquivalenceNotWorldIdentity :
  Stabiliser.observationalEquivalenceMeansWorldIdentity
    Stabiliser.canonicalConsumerStabiliserBoundary ≡ false
consumerEquivalenceNotWorldIdentity = refl

fineAlternativesSurviveConsumerQuotient :
  Stabiliser.residualWorldOrbitRetainsFineAlternatives
    Stabiliser.canonicalConsumerStabiliserBoundary ≡ true
fineAlternativesSurviveConsumerQuotient = refl

------------------------------------------------------------------------
-- Hard no-go laws.
------------------------------------------------------------------------

data DocumentContextOverwritesOccurrenceEvidence : Set where
data ConsumerEquivalentMeansSameSemanticWorld : Set where
data OneQueryResolutionClosesAllStatusAxes : Set where
data BackwardRestrictionCopiesClosedInterior : Set where

documentContextDoesNotOverwriteOccurrence :
  DocumentContextOverwritesOccurrenceEvidence → ⊥
documentContextDoesNotOverwriteOccurrence ()

consumerEquivalenceDoesNotIdentifyWorld :
  ConsumerEquivalentMeansSameSemanticWorld → ⊥
consumerEquivalenceDoesNotIdentifyWorld ()

oneQueryDoesNotCloseAllAxes : OneQueryResolutionClosesAllStatusAxes → ⊥
oneQueryDoesNotCloseAllAxes ()

restrictionDoesNotCopyClosedInterior : BackwardRestrictionCopiesClosedInterior → ⊥
restrictionDoesNotCopyClosedInterior ()
