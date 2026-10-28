module DASHI.Mathematics.Topology.AlexanderHornedNativeTernaryS3LocalValuesExact where

------------------------------------------------------------------------
-- EXACT LOCAL S3 VALUE PERMUTATIONS ON THE NATIVE C3 x T^n END TOWER
--
-- Cross-pollination uses the ORIGINAL S3 permutation owner, its C3
-- cyclic subgroup embedding, and the existing native end carrier.
-- A GLOBAL S3 action uses the same permutation at every address;
-- a LOCAL S3 gauge chooses independently at every address.
--
-- This is a different action from the external C3 SECTOR permutation.
-- It extends the C3 value-translation group pointwise but not the
-- original horned exterior's perfect π1 or binary-icosahedral holonomy.
-- At depth 2 there are 6^27 local S3 transformations.
--
-- Unlike the perfect A5 / 2I target groups, S3 is solvable
-- (S3' = C3, C3' = 1), and so is a finite direct product S3^X.
-- Adding external sector C3 yields a solvable finite extension.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Product using (_,_)
open import Data.Vec.Base using ([])
open import Data.Empty using (⊥)

import Base369 as Base
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3
import DASHI.Foundations.TernaryPermutationCyclicSubgroupsExact as Cyclic
import DASHI.Mathematics.Topology.AlexanderHornedNativeBalancedTernaryEndTowerExact as End
import DASHI.Mathematics.Topology.AlexanderHornedNativeTernaryFibreActionExact as Local

LocalS3 : Set → Set
LocalS3 X = X → Perm.TriPermutation

GaugeS3 : (n : Nat) → Set
GaugeS3 n = LocalS3 (End.BalancedLevel n)

ValueField : (n : Nat) → Set
ValueField n = End.BalancedLevel n → Base.TriTruth

identityGauge : ∀ {n} → GaugeS3 n
identityGauge _ = Perm.permIdentity

combineGauge : ∀ {n} → GaugeS3 n → GaugeS3 n → GaugeS3 n
combineGauge g h x = S3._∙_ (g x) (h x)

actGauge : ∀ {n} → GaugeS3 n → ValueField n → ValueField n
actGauge g f x = Perm.applyPermutation (g x) (f x)

localS3ActionComposition :
  ∀ {n} (g h : GaugeS3 n) (f : ValueField n)
  (x : End.BalancedLevel n) →
  actGauge (combineGauge g h) f x
  ≡ actGauge g (actGauge h f) x
localS3ActionComposition g h f x =
  S3.applyComposition (g x) (h x) (f x)

localS3ActionIdentity :
  ∀ {n} (f : ValueField n) (x : End.BalancedLevel n) →
  actGauge identityGauge f x ≡ f x
localS3ActionIdentity f x = refl

constantS3 :
  ∀ {n} → Perm.TriPermutation → GaugeS3 n
constantS3 p _ = p

-- Chosen depth-zero independent reflection at just ONE sector.
localReflectionOnlyFirstSector : GaugeS3 0
localReflectionOnlyFirstSector (C3.c0 , []) =
  Perm.permSwapLowHigh
localReflectionOnlyFirstSector (C3.c1 , []) =
  Perm.permIdentity
localReflectionOnlyFirstSector (C3.c2 , []) =
  Perm.permIdentity

allLow : ValueField 0
allLow _ = Base.tri-low

localReflectionMovesFirst :
  actGauge localReflectionOnlyFirstSector allLow (C3.c0 , [])
    ≡ Base.tri-high
localReflectionMovesFirst = refl

localReflectionLeavesSecond :
  actGauge localReflectionOnlyFirstSector allLow (C3.c1 , [])
    ≡ Base.tri-low
localReflectionLeavesSecond = refl

globalReflectionMovesSecond :
  actGauge (constantS3 Perm.permSwapLowHigh) allLow
    (C3.c1 , []) ≡ Base.tri-high
globalReflectionMovesSecond = refl

localIsNotGlobalReflection :
  actGauge localReflectionOnlyFirstSector allLow (C3.c1 , [])
  ≡ actGauge (constantS3 Perm.permSwapLowHigh) allLow
    (C3.c1 , []) → ⊥
localIsNotGlobalReflection ()

-- Bridging the older HORN C3 group and the pre-existing phase-C3
-- subgroup embedding in the S3 owner: the carrier conversion preserves
-- the actual group law, not merely the label count.
hornC3ToPhase : C3.C3 → Phase.Phase3
hornC3ToPhase C3.c0 = Phase.phase0
hornC3ToPhase C3.c1 = Phase.phase1
hornC3ToPhase C3.c2 = Phase.phase2

hornC3MatchesPhase :
  (a b : C3.C3) →
  hornC3ToPhase (C3._∙_ a b)
    ≡ Cyclic._+₃_ (hornC3ToPhase a) (hornC3ToPhase b)
hornC3MatchesPhase C3.c0 C3.c0 = refl
hornC3MatchesPhase C3.c0 C3.c1 = refl
hornC3MatchesPhase C3.c0 C3.c2 = refl
hornC3MatchesPhase C3.c1 C3.c0 = refl
hornC3MatchesPhase C3.c1 C3.c1 = refl
hornC3MatchesPhase C3.c1 C3.c2 = refl
hornC3MatchesPhase C3.c2 C3.c0 = refl
hornC3MatchesPhase C3.c2 C3.c1 = refl
hornC3MatchesPhase C3.c2 C3.c2 = refl

embedLocalC3InLocalS3 :
  ∀ {n} → Local.FibreAction n → GaugeS3 n
embedLocalC3InLocalS3 g x =
  Cyclic.embedC3InS3 (hornC3ToPhase (g x))

localC3SubgroupHomomorphism :
  ∀ {n} (g h : Local.FibreAction n)
  (x : End.BalancedLevel n) →
  embedLocalC3InLocalS3 (Local.combine g h) x
    ≡ combineGauge (embedLocalC3InLocalS3 g)
                    (embedLocalC3InLocalS3 h) x
localC3SubgroupHomomorphism g h x =
  trans
    (cong Cyclic.embedC3InS3 (hornC3MatchesPhase (g x) (h x)))
    (Cyclic.embedC3Homomorphism
      (hornC3ToPhase (g x)) (hornC3ToPhase (h x)))

-- Full local S3 is a real enlargement of C3 but is still solvable;
-- there is no algebraic route from merely selecting S3-valued
-- functions to the nontrivial perfect Hatcher source or its 2I target.
