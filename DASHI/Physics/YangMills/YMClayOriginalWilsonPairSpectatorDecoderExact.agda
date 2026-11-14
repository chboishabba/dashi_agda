module DASHI.Physics.YangMills.YMClayOriginalWilsonPairSpectatorDecoderExact where

-- M.02 / F19 original physical source: construct a TRUE, bidirectional
-- finite decoder for exactly 64 adjacent ordered source bond pairs and
-- 896 spectator links. No abstract "the original fields factor" premise.
--
-- The pair representation is Torus.Product; order is first link then
-- second link, matching the physically sorted 1024-link source.
-- The theorem is about positions, NOT gauge blocking or Haar estimates.
--
-- This closes the structural vector splitting seam needed by the
-- all-observable canonical-to-F19 physical Wilson weighted reindex.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Vec.Base as Vec
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.YMClayOriginalWilsonF19ConcreteWeightExact as Original
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

splitOriginalPairsSpectators :
  ∀ {A : Set} {n m : Nat} →
  Vec.Vec A (Original.twice n + m) →
  Torus.Product
    (Vec.Vec (Torus.Product A A) n)
    (Vec.Vec A m)
splitOriginalPairsSpectators {n = zero} values =
  Torus.pair Vec.[] values
splitOriginalPairsSpectators {n = suc n}
    (first Vec.∷ second Vec.∷ rest)
    with splitOriginalPairsSpectators {n = n} rest
... | Torus.pair pairs spectators =
  Torus.pair (Torus.pair first second Vec.∷ pairs) spectators

splitJoinedOriginalExactly :
  ∀ {A : Set} {n m : Nat}
    (pairs : Vec.Vec (Torus.Product A A) n)
    (spectators : Vec.Vec A m) →
  splitOriginalPairsSpectators
    (Original.appendVec (Original.flattenPairs pairs) spectators)
    ≡ Torus.pair pairs spectators
splitJoinedOriginalExactly {n = zero} Vec.[] spectators = refl
splitJoinedOriginalExactly {n = suc n}
    (Torus.pair first second Vec.∷ rest) spectators
    rewrite splitJoinedOriginalExactly rest spectators = refl

joinedSplitOriginalExactly :
  ∀ {A : Set} {n m : Nat}
    (values : Vec.Vec A (Original.twice n + m)) →
  Original.appendVec
    (Original.flattenPairs
      (Torus.first (splitOriginalPairsSpectators values)))
    (Torus.second (splitOriginalPairsSpectators values))
  ≡ values
joinedSplitOriginalExactly {n = zero} values = refl
joinedSplitOriginalExactly {n = suc n}
    (first Vec.∷ second Vec.∷ rest)
    rewrite joinedSplitOriginalExactly {n = n} rest = refl

-- This codec can be specialized to exactly 64 pairs and 896
-- original spectators without assuming that the Wilson Gibbs
-- density factors into pair and spectator weights.
sourceSideFourDecode :
  ∀ {A : Set} →
  Vec.Vec A (Original.twice 64 + 896) →
  Torus.Product
    (Vec.Vec (Torus.Product A A) 64)
    (Vec.Vec A 896)
sourceSideFourDecode = splitOriginalPairsSpectators

sourceSideFourSplitJoin :
  ∀ {A : Set}
    (pairs : Vec.Vec (Torus.Product A A) 64)
    (spectators : Vec.Vec A 896) →
  sourceSideFourDecode
    (Original.appendVec (Original.flattenPairs pairs) spectators)
  ≡ Torus.pair pairs spectators
sourceSideFourSplitJoin = splitJoinedOriginalExactly
