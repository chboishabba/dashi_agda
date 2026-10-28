module DASHI.Mathematics.Topology.AlexanderHornedS3DerivedMonodromyNoGoExact where

------------------------------------------------------------------------
-- REUSE-FIRST SOURCE OWNER: Hatcher's classical recursive commutator
-- meridians plus EXACT existing S3 permutation multiplication.
--
-- The finite braid image in S3 is SOLVABLE, despite being nonabelian.
-- A meridian representation that satisfies the full Hatcher recursion
-- cannot have a nontrivial image in S3. Proof uses the original generic
-- HornedProPSolvableBlindExact theorem with a CONCRETE S3 instance.
--
-- This does NOT kill the generic polynomial-root monodromy S3 itself:
-- the polynomial coefficient loop group is NOT the Hatcher group.
-- Perfect 2I/A5 targets remain different unsolvable/nonabelian actors.
--
-- Original owners: Alexander 1924; Hatcher AT 2B.2; Galois/Jordan
-- derived series; DASHI pre-existing S3 and solvable blind lemma.
-- Source written by DASHI continuation, Agda kernel NOT YET checked.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3
import DASHI.Mathematics.Topology.AlexanderHornedProPSolvableBlindExact as Blind

commutatorS3 : Perm.TriPermutation → Perm.TriPermutation →
  Perm.TriPermutation
commutatorS3 a b =
  S3._∙_ (S3._∙_ (S3._∙_ a b)
    (Perm.inversePermutation a)) (Perm.inversePermutation b)

data EvenS3 : Perm.TriPermutation → Set where
  evenIdentity : EvenS3 Perm.permIdentity
  evenRotate : EvenS3 Perm.permRotate
  evenRotate2 : EvenS3 Perm.permRotate2

-- All 36 S3 commutators lie in the existing 3-cycle subgroup C3.
commutatorIsEven : (a b : Perm.TriPermutation) →
  EvenS3 (commutatorS3 a b)
commutatorIsEven Perm.permIdentity Perm.permIdentity = evenIdentity
commutatorIsEven Perm.permIdentity Perm.permRotate = evenIdentity
commutatorIsEven Perm.permIdentity Perm.permRotate2 = evenIdentity
commutatorIsEven Perm.permIdentity Perm.permSwapLowMid = evenIdentity
commutatorIsEven Perm.permIdentity Perm.permSwapLowHigh = evenIdentity
commutatorIsEven Perm.permIdentity Perm.permSwapMidHigh = evenIdentity
commutatorIsEven Perm.permRotate Perm.permIdentity = evenIdentity
commutatorIsEven Perm.permRotate Perm.permRotate = evenIdentity
commutatorIsEven Perm.permRotate Perm.permRotate2 = evenIdentity
commutatorIsEven Perm.permRotate Perm.permSwapLowMid = evenRotate2
commutatorIsEven Perm.permRotate Perm.permSwapLowHigh = evenRotate2
commutatorIsEven Perm.permRotate Perm.permSwapMidHigh = evenRotate2
commutatorIsEven Perm.permRotate2 Perm.permIdentity = evenIdentity
commutatorIsEven Perm.permRotate2 Perm.permRotate = evenIdentity
commutatorIsEven Perm.permRotate2 Perm.permRotate2 = evenIdentity
commutatorIsEven Perm.permRotate2 Perm.permSwapLowMid = evenRotate
commutatorIsEven Perm.permRotate2 Perm.permSwapLowHigh = evenRotate
commutatorIsEven Perm.permRotate2 Perm.permSwapMidHigh = evenRotate
commutatorIsEven Perm.permSwapLowMid Perm.permIdentity = evenIdentity
commutatorIsEven Perm.permSwapLowMid Perm.permRotate = evenRotate
commutatorIsEven Perm.permSwapLowMid Perm.permRotate2 = evenRotate2
commutatorIsEven Perm.permSwapLowMid Perm.permSwapLowMid = evenIdentity
commutatorIsEven Perm.permSwapLowMid Perm.permSwapLowHigh = evenRotate
commutatorIsEven Perm.permSwapLowMid Perm.permSwapMidHigh = evenRotate2
commutatorIsEven Perm.permSwapLowHigh Perm.permIdentity = evenIdentity
commutatorIsEven Perm.permSwapLowHigh Perm.permRotate = evenRotate
commutatorIsEven Perm.permSwapLowHigh Perm.permRotate2 = evenRotate2
commutatorIsEven Perm.permSwapLowHigh Perm.permSwapLowMid = evenRotate2
commutatorIsEven Perm.permSwapLowHigh Perm.permSwapLowHigh = evenIdentity
commutatorIsEven Perm.permSwapLowHigh Perm.permSwapMidHigh = evenRotate
commutatorIsEven Perm.permSwapMidHigh Perm.permIdentity = evenIdentity
commutatorIsEven Perm.permSwapMidHigh Perm.permRotate = evenRotate
commutatorIsEven Perm.permSwapMidHigh Perm.permRotate2 = evenRotate2
commutatorIsEven Perm.permSwapMidHigh Perm.permSwapLowMid = evenRotate
commutatorIsEven Perm.permSwapMidHigh Perm.permSwapLowHigh = evenRotate2
commutatorIsEven Perm.permSwapMidHigh Perm.permSwapMidHigh = evenIdentity

-- A second commutator always vanishes on even/C3 inputs.
commutatorOfEvenPermutationsIsIdentity :
  (a b : Perm.TriPermutation) →
  EvenS3 a → EvenS3 b →
  commutatorS3 a b ≡ Perm.permIdentity
commutatorOfEvenPermutationsIsIdentity Perm.permIdentity Perm.permIdentity evenIdentity evenIdentity = refl
commutatorOfEvenPermutationsIsIdentity Perm.permIdentity Perm.permRotate evenIdentity evenRotate = refl
commutatorOfEvenPermutationsIsIdentity Perm.permIdentity Perm.permRotate2 evenIdentity evenRotate2 = refl
commutatorOfEvenPermutationsIsIdentity Perm.permRotate Perm.permIdentity evenRotate evenIdentity = refl
commutatorOfEvenPermutationsIsIdentity Perm.permRotate Perm.permRotate evenRotate evenRotate = refl
commutatorOfEvenPermutationsIsIdentity Perm.permRotate Perm.permRotate2 evenRotate evenRotate2 = refl
commutatorOfEvenPermutationsIsIdentity Perm.permRotate2 Perm.permIdentity evenRotate2 evenIdentity = refl
commutatorOfEvenPermutationsIsIdentity Perm.permRotate2 Perm.permRotate evenRotate2 evenRotate = refl
commutatorOfEvenPermutationsIsIdentity Perm.permRotate2 Perm.permRotate2 evenRotate2 evenRotate2 = refl

-- At level zero: any S3 permutation.
-- At level one: even/C3.
-- At levels two and beyond: the identity.
DerivedS3 : Nat → Perm.TriPermutation → Set
DerivedS3 zero _ = ⊤
DerivedS3 (suc zero) p = EvenS3 p
DerivedS3 (suc (suc n)) p = p ≡ Perm.permIdentity

derivedS3Step :
  (n : Nat) (a b : Perm.TriPermutation) →
  DerivedS3 n a → DerivedS3 n b →
  DerivedS3 (suc n) (commutatorS3 a b)
derivedS3Step zero a b _ _ = commutatorIsEven a b
derivedS3Step (suc zero) a b pa pb =
  commutatorOfEvenPermutationsIsIdentity a b pa pb
derivedS3Step (suc (suc n)) a b pa pb
  rewrite pa | pb = refl

-- This is an ACTUAL instance, not an uninhabited interface.
solvableS3Target : Blind.SolvableCommutatorTarget
solvableS3Target = record
  { Carrier = Perm.TriPermutation
  ; identity = Perm.permIdentity
  ; commutator = commutatorS3
  ; Derived = DerivedS3
  ; derivedZero = λ _ → tt
  ; derivedCommutator = derivedS3Step
  ; derivedLength = 2
  ; derivedLengthTrivial = λ _ proof → proof
  }

hatcherMeridianCannotRetainS3RootLabel :
  (rho : Blind.HornMeridianRepresentation solvableS3Target) →
  ∀ address →
  Blind.image rho address ≡ Perm.permIdentity
hatcherMeridianCannotRetainS3RootLabel =
  Blind.everySolvableMeridianImageTrivial solvableS3Target

-- No negative conclusion about arbitrary root braid loops follows:
-- this theorem requires Hatcher's specific recursive meridian relation.
