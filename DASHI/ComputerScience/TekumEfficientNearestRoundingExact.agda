module DASHI.ComputerScience.TekumEfficientNearestRoundingExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Relation.Nullary.Negation.Core using (¬_)

import DASHI.ComputerScience.TekumRawNearestCorrectionExact as Raw

------------------------------------------------------------------------
-- EFFICIENT RAW-LOCAL CORRECTION: FAIL-CLOSED
--
-- The proposed implementation strategy was to raw-truncate and inspect a
-- small fixed source-code neighbourhood.  Exact exhaustive discovery refutes
-- that strategy as a uniform small-radius implementation: already at 10→8 a
-- same-object witness needs displacement 6558, the entire ordinary 8-trit
-- carrier size, and at 12→10 the observed maximum is 59046.
--
-- The kernel theorem below closes the first nontrivial radius claim.  The full
-- census remains a reproducible Python receipt; it is not promoted to a
-- stronger Agda theorem without a general analytic proof.
------------------------------------------------------------------------

uniformLocalCorrectionNotEstablished :
  ¬ Raw.UniformRadiusOneRawCorrection
uniformLocalCorrectionNotEstablished =
  Raw.uniformRadiusOneRawCorrectionRefuted

record EfficientNearestRoundingBoundary : Set where
  constructor efficientNearestRoundingBoundary
  field
    radiusOneRawNeighbourhoodRefuted : Bool
    fullCarrierScaleDisplacementObserved10to8 : Bool
    fullCarrierScaleDisplacementObserved12to10 : Bool
    exhaustiveOracleRemainsSemanticReference : Bool
    efficientNearestImplementationPaid : Bool
    efficientNearestEqualsCanonicalNearestPaid : Bool

canonicalEfficientNearestRoundingBoundary : EfficientNearestRoundingBoundary
canonicalEfficientNearestRoundingBoundary =
  efficientNearestRoundingBoundary
    true true true true false false
