module DASHI.Cognition.PNF.OrientedZeroCanonicalPartitionPresentationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.OrientedZeroCanonicalFutureExact as Canonical
import DASHI.Cognition.PNF.OrientedZeroFutureQuotientExact as Wave
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.GenericFuturePartitionRefinementExact as Refinement
import DASHI.Core.StablePartitionCanonicalFutureBridgeExact as Bridge

step : Canonical.Action → Wave.Wave4 → Wave.Wave4
step Canonical.tick = Wave.waveStep

label : Canonical.Action → String
label Canonical.tick = "advance oriented wave phase"

refinesRefl :
  (depth : Nat) → (state : Wave.Wave4) →
  Refinement.RefinesToDepth depth Wave.scalar step state state
refinesRefl zero state = refl
refinesRefl (suc depth) state =
  refl , λ Canonical.tick → refinesRefl depth (Wave.waveStep state)

depthOneRefinementInjective :
  ∀ {left right : Wave.Wave4} →
  Refinement.RefinesToDepth 1 Wave.scalar step left right →
  left ≡ right
depthOneRefinementInjective {Wave.negativeOne} {Wave.negativeOne} refined = refl
depthOneRefinementInjective {Wave.negativeOne} {Wave.negativeZero} refined with proj₁ refined
... | ()
depthOneRefinementInjective {Wave.negativeOne} {Wave.positiveZero} refined with proj₁ refined
... | ()
depthOneRefinementInjective {Wave.negativeOne} {Wave.positiveOne} refined with proj₁ refined
... | ()
depthOneRefinementInjective {Wave.negativeZero} {Wave.negativeOne} refined with proj₁ refined
... | ()
depthOneRefinementInjective {Wave.negativeZero} {Wave.negativeZero} refined = refl
depthOneRefinementInjective {Wave.negativeZero} {Wave.positiveZero} refined
  with proj₂ refined Canonical.tick
... | ()
depthOneRefinementInjective {Wave.negativeZero} {Wave.positiveOne} refined with proj₁ refined
... | ()
depthOneRefinementInjective {Wave.positiveZero} {Wave.negativeOne} refined with proj₁ refined
... | ()
depthOneRefinementInjective {Wave.positiveZero} {Wave.negativeZero} refined
  with proj₂ refined Canonical.tick
... | ()
depthOneRefinementInjective {Wave.positiveZero} {Wave.positiveZero} refined = refl
depthOneRefinementInjective {Wave.positiveZero} {Wave.positiveOne} refined with proj₁ refined
... | ()
depthOneRefinementInjective {Wave.positiveOne} {Wave.negativeOne} refined with proj₁ refined
... | ()
depthOneRefinementInjective {Wave.positiveOne} {Wave.negativeZero} refined with proj₁ refined
... | ()
depthOneRefinementInjective {Wave.positiveOne} {Wave.positiveZero} refined with proj₁ refined
... | ()
depthOneRefinementInjective {Wave.positiveOne} {Wave.positiveOne} refined = refl

orientedZeroStableAtDepthOne : Refinement.StableAt 1 Wave.scalar step
orientedZeroStableAtDepthOne = Refinement.stableAt forward Refinement.refinementMonotone
  where
    forward :
      ∀ {left right} →
      Refinement.RefinesToDepth 1 Wave.scalar step left right →
      Refinement.RefinesToDepth 2 Wave.scalar step left right
    forward {left} {right} refined
      with depthOneRefinementInjective refined
    ... | refl = refinesRefl 2 left

depthOneExactlyCanonicalFuture :
  (left right : Wave.Wave4) →
  (Refinement.RefinesToDepth 1 Wave.scalar step left right →
    Future.FutureObservationEquivalent
      (Bridge.deterministicSystem step label) Wave.scalar left right)
  ×
  (Future.FutureObservationEquivalent
      (Bridge.deterministicSystem step label) Wave.scalar left right →
    Refinement.RefinesToDepth 1 Wave.scalar step left right)
depthOneExactlyCanonicalFuture =
  Bridge.stableRefinementExactlyCanonicalFuture orientedZeroStableAtDepthOne
