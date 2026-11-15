module DASHI.Education.DigitalESDReviewedTemporalWorldJoinExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Education.DigitalESDEfSSourceCrossPollinationExact as Cases
import DASHI.Education.DigitalESDJointHyperfabricConsumerExact as Joint
import DASHI.Education.DigitalESDConnectedTimeFibreHyperfabricExact as Temporal

-- Integration contract over existing independent owners, not another
-- research world ontology and not a canonical empirical inhabitant.
-- A reviewed hyperedge must bind to the *same* recorded source in both
-- temporal observations, and those observations must belong to the
-- supplied temporal fabric at their exact observer/time coordinates.
-- Source-review packet/observation/full-text membership is already
-- required by JointReviewHyperedge; do not replace it with a boolean.
record ReviewedTemporalWorldJoin
  (case : Cases.CrossPollinationCase)
  (original revision : Temporal.TemporalSourceFibre) : Set₂ where
  constructor reviewed-temporal-world-join
  field
    world : Temporal.ConnectedDigitalESDTimeHyperfabric
    reviewed : Joint.JointReviewHyperedge case
    revisionDependency : Temporal.HistoricalRevisionDependency original revision
    originalObserver : Temporal.SituatedObserver
    revisionObserver : Temporal.SituatedObserver
    originalIsWorldObservation :
      Temporal.ConnectedDigitalESDTimeHyperfabric.observationsAt
        world (Temporal.time original) originalObserver ≡ original
    revisionIsWorldObservation :
      Temporal.ConnectedDigitalESDTimeHyperfabric.observationsAt
        world (Temporal.time revision) revisionObserver ≡ revision
    originalIsReviewedSource :
      Temporal.sourceIdentity original ≡
        Source.canonicalURL (Cases.attributedSource case)
    revisionIsReviewedSource :
      Temporal.sourceIdentity revision ≡
        Source.canonicalURL (Cases.attributedSource case)

-- Open obligations: establish study-specific historical dependence and
-- selective conclusion invalidation using the existing lineage owner;
-- enumerate every source/claim/observation/edge in an executable census;
-- supply actual reviewed observations and source admission. This record
-- deliberately offers no constructor from candidate-only evidence.
