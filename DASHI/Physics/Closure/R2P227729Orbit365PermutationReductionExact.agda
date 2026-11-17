module DASHI.Physics.Closure.R2P227729Orbit365PermutationReductionExact where

------------------------------------------------------------------------
-- REUSE OF ALREADY SOURCE-OWNED PERMUTATION AND FINITE FOLD MACHINERY.
--
-- Original proof owners:
--   Mathematics.NumberTheory.FiniteWeightedReindexExact:
--     uniqueMembershipEquivalenceToPermutation.
--   Physics.Closure.NSTriadKNFiniteConvolutionReconstruction:
--     proof pattern for finite convolution sums under permutations.
--   R2P227729OrbitWeighted365ConvolutionExact:
--     real 365 representatives, 729 events, reflected Q(omega) weights.
--
-- This module proves the exact conditional source-vs-orbit SUM theorem.
-- The only remaining *specific list* proof is the permutation of the
-- actual pair729 with the explicit expanded 365 canonical list.
-- No postulates and no hidden promotion. Agda kernel not run.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.Unique.Propositional as Unique
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Data.List.Relation.Binary.Permutation.Propositional.Properties as PermP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as I
import DASHI.Physics.Closure.R2P227729PairOrbit365CanonicalSymmetryExact as Pair
import DASHI.Physics.Closure.R2P227729AntipodalThirteenFiveOrbitFourierCutExact as Ant
import DASHI.Physics.Closure.R2P227729OrbitWeighted365ConvolutionExact as Orbit
import DASHI.Physics.Closure.R2P227729FiniteQuadraticConvolutionExact as Conv
import DASHI.Physics.Closure.R2P227729HermitianThirteenPairFourierCodecExact as Herm
import DASHI.Biology.Physical.C3CubeCyclotomicFourierExact as C3

expandCanonicalPair : I.ModePair729 → List I.ModePair729
expandCanonicalPair pair with Pair.isCentralPair pair
... | true = pair ∷ []
... | false =
  pair ∷ Ant.simultaneouslyNegateOrderedPair pair ∷ []

expandedCanonicalPairs : List I.ModePair729
expandedCanonicalPairs =
  I.concatMapL expandCanonicalPair Orbit.canonicalOrderedPairs

expandedCanonicalPairCount :
  I.lengthL expandedCanonicalPairs ≡ 729
expandedCanonicalPairCount = refl

-- GENERAL LIST FUSION: no reliance on 729-element normalization.
mapAppend :
  ∀ {A B : Set} (f : A → B) (xs ys : List A) →
  I.mapL f (I._++L_ xs ys) ≡ I._++L_ (I.mapL f xs) (I.mapL f ys)
mapAppend f [] ys = refl
mapAppend f (x ∷ xs) ys =
  cong (λ rest → f x ∷ rest) (mapAppend f xs ys)

mapConcat :
  ∀ {A B C : Set}
  (f : B → C) (g : A → List B) (xs : List A) →
  I.mapL f (I.concatMapL g xs)
    ≡ I.concatMapL (λ x → I.mapL f (g x)) xs
mapConcat f g [] = refl
mapConcat f g (x ∷ xs) =
  trans
    (mapAppend f (g x) (I.concatMapL g xs))
    (cong (λ tail → I._++L_ (I.mapL f (g x)) tail)
      (mapConcat f g xs))

concatMapCong :
  ∀ {A B : Set}
    (f g : A → List B) →
    ((x : A) → f x ≡ g x) →
    (xs : List A) →
    I.concatMapL f xs ≡ I.concatMapL g xs
concatMapCong f g agree [] = refl
concatMapCong f g agree (x ∷ xs) =
  cong₂ I._++L_ (agree x) (concatMapCong f g agree xs)

-- Mathematical reflection was already proved in the original orbit
-- owner; this only transports it into the explicit expanded addresses.
emitPairEqualsMapExpanded :
  (a b : Herm.Hermitian27) (pair : I.ModePair729) →
  Orbit.emitCanonicalPair a b pair
    ≡ I.mapL (Orbit.sourceEvent a b) (expandCanonicalPair pair)
emitPairEqualsMapExpanded a b pair with Pair.isCentralPair pair
... | true = refl
... | false =
  cong (λ z → Orbit.sourceEvent a b pair ∷ z ∷ [])
    (sym (Orbit.reflectedEventIsConjugate a b pair))

emittedEventsMatchExpandedAddresses :
  (a b : Herm.Hermitian27) →
  Orbit.orbitWeightedEvents a b
    ≡ I.mapL (Orbit.sourceEvent a b) expandedCanonicalPairs
emittedEventsMatchExpandedAddresses a b =
  trans
    (concatMapCong
      (Orbit.emitCanonicalPair a b)
      (λ pair → I.mapL (Orbit.sourceEvent a b) (expandCanonicalPair pair))
      (emitPairEqualsMapExpanded a b)
      Orbit.canonicalOrderedPairs)
    (sym
      (mapConcat (Orbit.sourceEvent a b) expandCanonicalPair
        Orbit.canonicalOrderedPairs))

------------------------------------------------------------------------
-- Q(omega) finite commutative addition: only source algebra is reused.
------------------------------------------------------------------------

addAssociative :
  (x y z : C3.Cyclotomic3) →
  C3._+C_ (C3._+C_ x y) z
    ≡ C3._+C_ x (C3._+C_ y z)
addAssociative (C3.cyc a b) (C3.cyc c d) (C3.cyc e f) =
  C3.cyc-ext solve-∀ solve-∀

addCommutative :
  (x y : C3.Cyclotomic3) → C3._+C_ x y ≡ C3._+C_ y x
addCommutative (C3.cyc a b) (C3.cyc c d) =
  C3.cyc-ext solve-∀ solve-∀

addIdentityLeft :
  (x : C3.Cyclotomic3) → C3._+C_ C3.zeroC x ≡ x
addIdentityLeft (C3.cyc a b) = C3.cyc-ext solve-∀ solve-∀

foldC :
  ∀ {A : Set} (f : A → C3.Cyclotomic3) (xs : List A) →
  C3.Cyclotomic3
foldC f [] = C3.zeroC
foldC f (x ∷ xs) = C3._+C_ (f x) (foldC f xs)

foldRespPermutation :
  ∀ {A : Set} (f : A → C3.Cyclotomic3)
    {xs ys : List A} →
    xs Perm.↭ ys → foldC f xs ≡ foldC f ys
foldRespPermutation f Perm.refl = refl
foldRespPermutation f (Perm.prep x permutation) =
  cong (C3._+C_ (f x)) (foldRespPermutation f permutation)
foldRespPermutation f (Perm.swap {ys = ys} x y permutation) =
  trans
    (cong
      (λ t → C3._+C_ (f x) (C3._+C_ (f y) t))
      (foldRespPermutation f permutation))
    (trans
      (sym (addAssociative (f x) (f y) (foldC f ys)))
      (trans
        (cong
          (λ v → C3._+C_ v (foldC f ys))
          (addCommutative (f x) (f y)))
        (addAssociative (f y) (f x) (foldC f ys))))
foldRespPermutation f (Perm.trans first second) =
  trans (foldRespPermutation f first) (foldRespPermutation f second)

eventAt :
  (target : Conv.WideCube125) →
  Orbit.WeightedEvent → C3.Cyclotomic3
eventAt target event with Conv.eqWideCube (Orbit.output event) target
... | true = Orbit.weight event
... | false = C3.zeroC

eventSumAsFold :
  (target : Conv.WideCube125) (xs : List Orbit.WeightedEvent) →
  Orbit.sumEventsAt target xs ≡ foldC (eventAt target) xs
eventSumAsFold target [] = refl
eventSumAsFold target (e ∷ es)
  with Conv.eqWideCube (Orbit.output e) target
... | true =
  cong (C3._+C_ (Orbit.weight e)) (eventSumAsFold target es)
... | false =
  trans (eventSumAsFold target es)
    (sym (addIdentityLeft (foldC (eventAt target) es)))

eventSumRespPermutation :
  (target : Conv.WideCube125)
  {xs ys : List Orbit.WeightedEvent} →
  xs Perm.↭ ys →
  Orbit.sumEventsAt target xs ≡ Orbit.sumEventsAt target ys
eventSumRespPermutation target {xs} {ys} permutation =
  trans
    (eventSumAsFold target xs)
    (trans
      (foldRespPermutation (eventAt target) permutation)
      (sym (eventSumAsFold target ys)))

-- HIGHEST-ALPHA LAST MILE: no separate finite sum algebra is needed.
-- Once the ACTUAL 729 address permutation is supplied, the entire
-- arbitrary-Hermitian Q(omega) operator equality follows by composition.
fullPairSumEqualsOrbitSumGivenPermutation :
  (a b : Herm.Hermitian27) (target : Conv.WideCube125) →
  I.pair729 Perm.↭ expandedCanonicalPairs →
  Orbit.unreducedConvolutionAt a b target
    ≡ Orbit.orbitWeightedConvolutionAt a b target
fullPairSumEqualsOrbitSumGivenPermutation a b target addresses =
  trans
    (eventSumRespPermutation target
      (PermP.map⁺ (Orbit.sourceEvent a b) addresses))
    (cong (Orbit.sumEventsAt target)
      (sym (emittedEventsMatchExpandedAddresses a b)))

-- Reuse source generic constructive theorem; its 4 hypotheses are
-- the only UNPROVED specific-address premises, not postulates.
specific365PermutationFromUniqueMembership :
  Unique.Unique I.pair729 →
  Unique.Unique expandedCanonicalPairs →
  (∀ {p} → p ∈ I.pair729 → p ∈ expandedCanonicalPairs) →
  (∀ {p} → p ∈ expandedCanonicalPairs → p ∈ I.pair729) →
  I.pair729 Perm.↭ expandedCanonicalPairs
specific365PermutationFromUniqueMembership =
  Reindex.uniqueMembershipEquivalenceToPermutation
