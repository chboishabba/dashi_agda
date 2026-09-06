module DASHI.Core.CommutingProvenanceBidiCrossPollination2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.Base369MonsterFiftyFourFiveModeResidualActionBidiExact as SameActionDonor

------------------------------------------------------------------------
-- COMMUTING PROVENANCE -- BIDI CROSS-POLLINATION
--
-- Repository donor:
-- DASHI.Moonshine.Base369MonsterFiftyFourFiveModeResidualActionBidiExact,
-- merged PR #695.  The donor's same-action discipline requires a residual
-- action to be a literal restriction of the same ambient action, not merely a
-- dimension match.
--
-- DASHI extension: use the same commuting-square discipline for provenance and
-- observation.  A coarse report is a lawful projection of a fine process when
-- projection after the fine transition equals coarse transition after
-- projection.  No Monster representation or group action is transferred.
------------------------------------------------------------------------

record CommutingProjection
    (Fine Coarse : Set)
    (fineStep : Fine → Fine)
    (coarseStep : Coarse → Coarse)
    (observe : Fine → Coarse) : Set where
  constructor commuting-projection
  field
    commutes : (x : Fine) → observe (fineStep x) ≡ coarseStep (observe x)
    projectionReference : String

open CommutingProjection public

record SameProcessProjection
    (Fine Coarse : Set) : Set₁ where
  constructor same-process-projection
  field
    fineStep : Fine → Fine
    coarseStep : Coarse → Coarse
    observe : Fine → Coarse
    square : CommutingProjection Fine Coarse fineStep coarseStep observe
    fineProcessReference : String
    coarseProcessReference : String

open SameProcessProjection public

------------------------------------------------------------------------
-- Exact consequence: equal fine states necessarily have equal projected
-- post-transition states.  This is intentionally modest; the converse is not
-- claimed because projection may erase distinctions.
------------------------------------------------------------------------

projectedPostCongruence :
  ∀ {Fine Coarse : Set}
    {fineStep : Fine → Fine}
    {coarseStep : Coarse → Coarse}
    {observe : Fine → Coarse} →
  CommutingProjection Fine Coarse fineStep coarseStep observe →
  (x y : Fine) → x ≡ y →
  observe (fineStep x) ≡ observe (fineStep y)
projectedPostCongruence square x .x refl = refl

------------------------------------------------------------------------
-- No-promotion boundaries.
------------------------------------------------------------------------

data SameNumberMeansSameProcess : Set where
data SameOutputMeansSameProvenance : Set where
data SameCarrierSizeMeansCommutingProjection : Set where
data CommutingProjectionCreatesAuthority : Set where

sameNumberDoesNotMeanSameProcess : SameNumberMeansSameProcess → ⊥
sameNumberDoesNotMeanSameProcess ()

sameOutputDoesNotMeanSameProvenance : SameOutputMeansSameProvenance → ⊥
sameOutputDoesNotMeanSameProvenance ()

sameCarrierSizeDoesNotMeanCommutingProjection : SameCarrierSizeMeansCommutingProjection → ⊥
sameCarrierSizeDoesNotMeanCommutingProjection ()

commutingProjectionDoesNotCreateAuthority : CommutingProjectionCreatesAuthority → ⊥
commutingProjectionDoesNotCreateAuthority ()

record CommutingProvenanceBoundary : Set where
  constructor commuting-provenance-boundary
  field
    sameProcessNeedsSquare : Bool
    matchingOutputsInsufficient : Bool
    projectionMayEraseResidual : Bool
    mathematicalShapeDoesNotTransferMonsterAuthority : Bool

canonicalCommutingProvenanceBoundary : CommutingProvenanceBoundary
canonicalCommutingProvenanceBoundary =
  commuting-provenance-boundary true true true true
