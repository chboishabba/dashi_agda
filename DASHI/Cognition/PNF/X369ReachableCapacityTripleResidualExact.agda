module DASHI.Cognition.PNF.X369ReachableCapacityTripleResidualExact where

-- Original Leech-LILA: Anatolii Kornienko. DASHI exact source weld.
-- The three native same-capacity endpoints are evidence inputs, not
-- kernel constants. Reuse the existing future-separation owner.
-- H is the DECLARED reachable carrier, closed under admitted controls.
-- A witness in a larger control carrier is not a witness in a smaller one.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as Future
import DASHI.Cognition.PNF.X369RetainedChartFutureSeparationExact as Retained

record ThreeDistinct {R : Set} (a b c : R) : Set where
  constructor threeDistinct
  field
    ab : a ≡ b → ⊥
    ac : a ≡ c → ⊥
    bc : b ≡ c → ⊥

noBooleanTriple : (a b c : Bool) → ThreeDistinct a b c → ⊥
noBooleanTriple false false c d = ThreeDistinct.ab d refl
noBooleanTriple true true c d = ThreeDistinct.ab d refl
noBooleanTriple false true false d = ThreeDistinct.ac d refl
noBooleanTriple false true true d = ThreeDistinct.bc d refl
noBooleanTriple true false true d = ThreeDistinct.ac d refl
noBooleanTriple true false false d = ThreeDistinct.bc d refl

module CapacityResidual
  (H U O Q R : Set)
  (step : U → H → H)
  (observe : U → H → O)
  (coarse : H → Q)
  (residual : H → R) where

  module W = Retained.RetainedChart H U O Q R step observe coarse residual

  module Stable
    (outputStable : (u : U) (x y : H) →
      W.repaired x ≡ W.repaired y → observe u x ≡ observe u y)
    (transitionStable : (u : U) (x y : H) →
      W.repaired x ≡ W.repaired y →
      W.repaired (step u x) ≡ W.repaired (step u y)) where

    module S = W.Stable outputStable transitionStable

    -- Three actual source endpoints in a single capacity fibre and
    -- three pairwise observed future separations force THREE labels,
    -- even when the original experiment was two anchor comparisons.
    consumerTripleRequiresDistinctResiduals :
      (x y z : H) (uv uw vw : List U) →
      coarse x ≡ coarse y →
      coarse x ≡ coarse z →
      coarse y ≡ coarse z →
      (Future.trace step observe uv x ≡ Future.trace step observe uv y → ⊥) →
      (Future.trace step observe uw x ≡ Future.trace step observe uw z → ⊥) →
      (Future.trace step observe vw y ≡ Future.trace step observe vw z → ⊥) →
      ThreeDistinct (residual x) (residual y) (residual z)
    consumerTripleRequiresDistinctResiduals x y z uv uw vw xy xz yz dxy dxz dyz =
      threeDistinct
        (S.consumerWitnessForcesResidual uv x y xy dxy)
        (S.consumerWitnessForcesResidual uw x z xz dxz)
        (S.consumerWitnessForcesResidual vw y z yz dyz)

-- Any genuinely sufficient repaired Boolean residual is impossible
-- on the declared reachable carrier containing such a triple.
module BooleanNoGo
  (H U O Q : Set)
  (step : U → H → H)
  (observe : U → H → O)
  (coarse : H → Q)
  (residual : H → Bool) where

  module W = CapacityResidual H U O Q Bool step observe coarse residual

  noOneBitRepair :
    (x y z : H) (uv uw vw : List U) →
    coarse x ≡ coarse y →
    coarse x ≡ coarse z →
    coarse y ≡ coarse z →
    (Future.trace step observe uv x ≡ Future.trace step observe uv y → ⊥) →
    (Future.trace step observe uw x ≡ Future.trace step observe uw z → ⊥) →
    (Future.trace step observe vw y ≡ Future.trace step observe vw z → ⊥) →
    ((u : U) (a b : H) →
      W.W.repaired a ≡ W.W.repaired b → observe u a ≡ observe u b) →
    ((u : U) (a b : H) →
      W.W.repaired a ≡ W.W.repaired b →
      W.W.repaired (step u a) ≡ W.W.repaired (step u b)) → ⊥
  noOneBitRepair x y z uv uw vw xy xz yz dxy dxz dyz out trans =
    noBooleanTriple (residual x) (residual y) (residual z)
      (W.Stable.consumerTripleRequiresDistinctResiduals out trans
        x y z uv uw vw xy xz yz dxy dxz dyz)
