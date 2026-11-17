module DASHI.Physics.Closure.R2P281PlaneOrbit41RankSortConvolutionExact where

------------------------------------------------------------------------
-- FIVE-IN-NINE PLANE: UNCONDITIONAL 41-PRODUCT / 81-PAIR CONVOLUTION.
--
-- Reuses the EXISTING five-class Hermitian9 owner and original true
-- plane 81-pair operator. Rank sorting/permutation is imported from
-- R2P227729Orbit365RankSortPermutationExact (the generic function),
-- and the original finite Q(omega) commutative fold from the 365 owner.
-- Distinct from D4 irreducible representation; no Monster/NS promotion.
-- All proof terms source-written; Agda kernel typecheck pending.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import Data.Product using (_,_)

import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as I
import DASHI.Physics.Closure.R2P2ThreeModeBinaryTernaryNSAliasingCutExact as M
import DASHI.Physics.Closure.R2P281PlaneHermitianFiveOrbitConvolutionExact as Plane
import DASHI.Physics.Closure.R2P227729AntipodalThirteenFiveOrbitFourierCutExact as Ant
import DASHI.Physics.Closure.R2P227729OrbitWeighted365ConvolutionExact as Orbit
import DASHI.Physics.Closure.R2P227729Orbit365PermutationReductionExact as Generic
import DASHI.Physics.Closure.R2P227729Orbit365RankSortPermutationExact as Sort
import DASHI.Physics.Closure.R2P227729HermitianThirteenPairFourierCodecExact as Herm
import DASHI.Biology.Physical.C3CubeCyclotomicFourierExact as C3

planeRank : Ant.Plane9 → Nat
planeRank (a , b) = 3 * I.modeRank a + I.modeRank b

planeOrderedPairRank : Plane.PlanePair81 → Nat
planeOrderedPairRank (p , q) = 9 * planeRank p + planeRank q

expandPlanePair : Plane.PlanePair81 → List Plane.PlanePair81
expandPlanePair pair with Orbit.isCentralPlanePair pair
... | true = pair ∷ []
... | false = pair ∷ Orbit.negatePlaneOrderedPair pair ∷ []

expanded41PlanePairs : List Plane.PlanePair81
expanded41PlanePairs =
  I.concatMapL expandPlanePair Orbit.canonicalPlaneOrderedPairs

expanded41PlanePairsHave81Entries :
  I.lengthL expanded41PlanePairs ≡ 81
expanded41PlanePairsHave81Entries = refl

rankSorted41PlaneIsOriginal81 :
  Sort.sortByRank planeOrderedPairRank expanded41PlanePairs
  ≡ Plane.planePairs81
rankSorted41PlaneIsOriginal81 = refl

planeSortedPermutationToOriginal :
  Sort.sortByRank planeOrderedPairRank expanded41PlanePairs
    Perm.↭ Plane.planePairs81
planeSortedPermutationToOriginal
  rewrite rankSorted41PlaneIsOriginal81 = Perm.refl

originalPlanePairsPermuteToExpanded41 :
  Plane.planePairs81 Perm.↭ expanded41PlanePairs
originalPlanePairsPermuteToExpanded41 =
  Perm.trans (PermP.↭-sym planeSortedPermutationToOriginal)
    (Sort.sortByRankPermutation planeOrderedPairRank expanded41PlanePairs)

emitPlaneEqualsExpandedMap :
  (a b : Herm.Hermitian9) (pair : Plane.PlanePair81) →
  Orbit.emitCanonicalPlanePair a b pair
    ≡ I.mapL (Orbit.planeSourceEvent a b) (expandPlanePair pair)
emitPlaneEqualsExpandedMap a b pair with Orbit.isCentralPlanePair pair
... | true = refl
... | false =
  cong (λ z → Orbit.planeSourceEvent a b pair ∷ z ∷ [])
    (sym (Orbit.reflectedPlaneEventIsConjugate a b pair))

planeEventsMatchExpandedAddresses :
  (a b : Herm.Hermitian9) →
  Orbit.orbitWeightedPlaneEvents a b
    ≡ I.mapL (Orbit.planeSourceEvent a b) expanded41PlanePairs
planeEventsMatchExpandedAddresses a b =
  trans
    (Generic.concatMapCong
      (Orbit.emitCanonicalPlanePair a b)
      (λ pair → I.mapL (Orbit.planeSourceEvent a b) (expandPlanePair pair))
      (emitPlaneEqualsExpandedMap a b)
      Orbit.canonicalPlaneOrderedPairs)
    (sym (Generic.mapConcat
      (Orbit.planeSourceEvent a b) expandPlanePair
      Orbit.canonicalPlaneOrderedPairs))

planeEventAt :
  Plane.WidePlane25 → Orbit.WeightedPlaneEvent → C3.Cyclotomic3
planeEventAt target e
  with Plane.planeOutputEqual (Orbit.planeOutput e) target
... | true = Orbit.planeWeight e
... | false = C3.zeroC

planeEventSumAsFold :
  (target : Plane.WidePlane25) (xs : List Orbit.WeightedPlaneEvent) →
  Orbit.sumPlaneEventsAt target xs ≡ Generic.foldC (planeEventAt target) xs
planeEventSumAsFold target [] = refl
planeEventSumAsFold target (e ∷ es)
  with Plane.planeOutputEqual (Orbit.planeOutput e) target
... | true =
  cong (C3._+C_ (Orbit.planeWeight e))
    (planeEventSumAsFold target es)
... | false =
  trans (planeEventSumAsFold target es)
    (sym (Generic.addIdentityLeft (Generic.foldC (planeEventAt target) es)))

planeEventSumPermInvariant :
  (target : Plane.WidePlane25)
  {xs ys : List Orbit.WeightedPlaneEvent} →
  xs Perm.↭ ys →
  Orbit.sumPlaneEventsAt target xs ≡ Orbit.sumPlaneEventsAt target ys
planeEventSumPermInvariant target {xs} {ys} perm =
  trans (planeEventSumAsFold target xs)
    (trans (Generic.foldRespPermutation (planeEventAt target) perm)
      (sym (planeEventSumAsFold target ys)))

rawPlaneEventSum :
  (a b : Herm.Hermitian9) →
  Plane.WidePlane25 → C3.Cyclotomic3
rawPlaneEventSum a b target =
  Orbit.sumPlaneEventsAt target
    (I.mapL (Orbit.planeSourceEvent a b) Plane.planePairs81)

rawPlaneEventSumMatchesOrbit41 :
  (a b : Herm.Hermitian9) (target : Plane.WidePlane25) →
  rawPlaneEventSum a b target
    ≡ Orbit.orbitWeightedPlaneConvolutionAt a b target
rawPlaneEventSumMatchesOrbit41 a b target =
  trans
    (planeEventSumPermInvariant target
      (PermP.map⁺ (Orbit.planeSourceEvent a b)
        originalPlanePairsPermuteToExpanded41))
    (cong (Orbit.sumPlaneEventsAt target)
      (sym (planeEventsMatchExpandedAddresses a b)))

-- Bridges the original plane owner's choice-weighted sum to a map of
-- weighted events. The false-membership branch needs zero-left.
rawEventSumIsOriginalPlaneOperatorOnList :
  (a b : Herm.Hermitian9) (target : Plane.WidePlane25)
  (xs : List Plane.PlanePair81) →
  Orbit.sumPlaneEventsAt target (I.mapL (Orbit.planeSourceEvent a b) xs)
    ≡ Plane.sumPlane xs
        (Plane.planePairContribution
          (Herm.coefficient9 a) (Herm.coefficient9 b) target)
rawEventSumIsOriginalPlaneOperatorOnList a b target [] = refl
rawEventSumIsOriginalPlaneOperatorOnList a b target
  (pair@(p , q) ∷ rest)
  with Plane.planeOutputEqual (Plane.planeTruePairSum pair) target
... | true =
  cong
    (C3._+C_ (C3._*C_ (Herm.coefficient9 a p) (Herm.coefficient9 b q)))
    (rawEventSumIsOriginalPlaneOperatorOnList a b target rest)
... | false =
  trans
    (rawEventSumIsOriginalPlaneOperatorOnList a b target rest)
    (sym (Generic.addIdentityLeft
      (Plane.sumPlane rest
        (Plane.planePairContribution
          (Herm.coefficient9 a) (Herm.coefficient9 b) target))))

sourceFiveInNineTrueConvolutionEqualsOrbit41 :
  (a b : Herm.Hermitian9) (target : Plane.WidePlane25) →
  Plane.truePlaneBilinearAt
    (Herm.coefficient9 a) (Herm.coefficient9 b) target
    ≡ Orbit.orbitWeightedPlaneConvolutionAt a b target
sourceFiveInNineTrueConvolutionEqualsOrbit41 a b target =
  trans
    (sym (rawEventSumIsOriginalPlaneOperatorOnList
      a b target Plane.planePairs81))
    (rawPlaneEventSumMatchesOrbit41 a b target)

-- The selected 41 products are EXACT for the original 25 true integer
-- plane outputs and two different real-Hermitian Q(omega) fields.
-- No physical dimensional reduction, D4 irrep or NS regularity claim.
