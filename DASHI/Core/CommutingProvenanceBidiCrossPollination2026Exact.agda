module DASHI.Core.CommutingProvenanceBidiCrossPollination2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.Base369MonsterFiftyFourFiveModeResidualActionBidiExact as SameActionDonor

record CommutingProjection
    (Fine Coarse : Set)
    (fineStep : Fine → Fine)
    (coarseStep : Coarse → Coarse)
    (observe : Fine → Coarse) : Set where
  constructor commuting-projection
  field commutes : (x : Fine) → observe (fineStep x) ≡ coarseStep (observe x)
        projectionReference : String
open CommutingProjection public

record SameProcessProjection (Fine Coarse : Set) : Set₁ where
  constructor same-process-projection
  field fineStep : Fine → Fine
        coarseStep : Coarse → Coarse
        observe : Fine → Coarse
        square : CommutingProjection Fine Coarse fineStep coarseStep observe
        fineProcessReference coarseProcessReference : String
open SameProcessProjection public

projectedPostCongruence :
  ∀ {Fine Coarse : Set}
    {fineStep : Fine → Fine}
    {coarseStep : Coarse → Coarse}
    {observe : Fine → Coarse} →
  CommutingProjection Fine Coarse fineStep coarseStep observe →
  (x y : Fine) → x ≡ y → observe (fineStep x) ≡ observe (fineStep y)
projectedPostCongruence square x .x refl = refl

data SameOutputMeansSameProvenance : Set where
data SameCarrierSizeMeansCommutingProjection : Set where

sameOutputDoesNotMeanSameProvenance : SameOutputMeansSameProvenance → ⊥
sameOutputDoesNotMeanSameProvenance ()
sameCarrierSizeDoesNotMeanCommutingProjection : SameCarrierSizeMeansCommutingProjection → ⊥
sameCarrierSizeDoesNotMeanCommutingProjection ()

record CommutingProvenanceBoundary : Set where
  constructor commuting-provenance-boundary
  field sameProcessNeedsSquare matchingOutputsInsufficient projectionMayEraseResidual mathematicalShapeDoesNotTransferMonsterAuthority : Bool

canonicalCommutingProvenanceBoundary : CommutingProvenanceBoundary
canonicalCommutingProvenanceBoundary = commuting-provenance-boundary true true true true
