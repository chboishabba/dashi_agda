module DASHI.Physics.Closure.NSClayFacingBPositiveMaxCut20261004Test where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSClayFacingBPositiveMaxCut20261004Exact as Cut

pairExtractionClosed : Cut.deepPairExtractionClosed ≡ true
pairExtractionClosed = refl

r406AggregationClosed : Cut.r406GlobalAggregationClosed ≡ true
r406AggregationClosed = refl

strictMarginStillOpen : Cut.b4StrictMarginClosed ≡ false
strictMarginStillOpen = refl
