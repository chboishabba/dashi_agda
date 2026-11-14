module DASHI.Physics.YangMills.YMClayNativeC3AdjacentSortProgramExact where

------------------------------------------------------------------------
-- R443: CONSTRUCT the missing NATIVE adjacent-swap C3 program itself.
--
-- The existing YMClayNativeC3SingleVectorPermutationCertificateExact
-- proved that a single 1024-label equality implies C3 equality for
-- ALL original SUN matrix link vectors and thus the original N-link
-- Haar invariance. It previously left the LinkPermutation program
-- as an externally supplied input.
--
-- Here we construct a concrete deterministic original LinkPermutation
-- by stable bubble-to-front insertion over the exact ORIGINAL positive
-- bond labels and the original selected C3.forwardVector target.
-- Thus there is NO free "program" field in this new candidate.
--
-- The remaining obligation is ONE CLOSED source equality:
--
--  permuteLinks constructedNativeC3Program canonicalLabelVector
--      ≡ C3.forwardVector canonicalLabelVector.
--
-- It should be decidable by reduction of the native finite vectors,
-- but a 1024-vector quadratic normalization is substantial. We DO NOT
-- fill it with a fake "refl" or an unverified axiom. Once the kernel
-- certifies the closed target, the previously-owned universal theorem
-- immediately supplies arbitrary original native SU(N) links.
--
-- The constructed program is not a source of compact Borel Haar,
-- integrable test classes, Gibbs reflection positivity, continuum
-- CMP116 decay or Clay gap. Existing owners remain credited.
-- SOURCE WRITTEN; Agda kernel acceptance PENDING.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Vec.Base as Vec

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Product
import DASHI.Physics.YangMills.YMClayNativeSideFourC3VectorWeldExact as C3
import DASHI.Physics.YangMills.YMClayNativeC3SingleVectorPermutationCertificateExact as Single

Bond : Set
Bond = Single.Bond

Count : Nat
Count = Single.Count

-- The original 4D periodic site + axis DecEq, on native bond labels.
originalBondDecide : Torus.DecidableEquality Bond
originalBondDecide =
  Torus.productDecidableEquality
    (Torus.periodicTorus4DecidableEquality Torus.four)
    Torus.cyclicIndexDecidableEquality

-- If desired is in the vector, move its FIRST occurrence to the head.
-- If it is absent, return a harmless permutation; our concrete C3
-- target is a permutation of the original distinct native bonds.
originalBubbleDesired :
  ∀ {n} → Bond → Vec.Vec Bond n → Product.LinkPermutation n
originalBubbleDesired {n = zero} desired Vec.[] =
  Product.identity
originalBubbleDesired {n = suc zero}
    desired (Vec._∷_ first Vec.[]) =
  Product.identity
originalBubbleDesired {n = suc (suc n)}
    desired (Vec._∷_ first (Vec._∷_ second rest))
  with originalBondDecide first desired
... | Torus.yes _ = Product.identity
... | Torus.no _ =
  Product.compose
    Product.swapHead
    (Product.fixHead
      (originalBubbleDesired desired (Vec._∷_ second rest)))

originalTail :
  ∀ {A : Set} {n} → Vec.Vec A (suc n) → Vec.Vec A n
originalTail (Vec._∷_ head tail) = tail

-- This is an actual original LinkPermutation PROGRAM for any target
-- vector. For a genuine target permutation of original distinct labels,
-- it computes a swap sort; its correctness is a separate equality.
originalSortToTarget :
  ∀ {n} →
  Vec.Vec Bond n →
  Vec.Vec Bond n →
  Product.LinkPermutation n
originalSortToTarget {n = zero} Vec.[] Vec.[] =
  Product.identity
originalSortToTarget {n = suc n}
    (Vec._∷_ desired wantedTail) source =
  let
    bubble = originalBubbleDesired desired source
    moved = Product.permuteLinks bubble source
    continuation =
      originalSortToTarget wantedTail (originalTail moved)
  in
  Product.compose (Product.fixHead continuation) bubble

-- Actual computed source code, no caller-supplied LinkPermutation.
constructedNativeC3Program : Product.LinkPermutation Count
constructedNativeC3Program =
  originalSortToTarget
    (C3.forwardVector Single.canonicalLabelVector)
    Single.canonicalLabelVector

-- Precisely ONE kernel-observable closed equality; no unsolved meta.
-- The missing lemma is still a source-level obligation, not marked DONE.
constructedNativeC3CanonicalLabelGoal : Set
constructedNativeC3CanonicalLabelGoal =
  Product.permuteLinks constructedNativeC3Program
    Single.canonicalLabelVector
  ≡ C3.forwardVector Single.canonicalLabelVector

-- When the closed finite equality is actually kernel-accepted,
-- construct the ORIGINAL single-vector certificate and obtain
-- native universal C3 permutation without any additional SU(N) input.
constructedNativeC3Certificate :
  constructedNativeC3CanonicalLabelGoal →
  Single.SingleVectorC3PermutationCertificate
constructedNativeC3Certificate proof = record
  { Single.program = constructedNativeC3Program
  ; Single.onCanonicalLabels = proof
  }

constructedNativeC3AllVectors :
  constructedNativeC3CanonicalLabelGoal →
  ∀ {Value : Set} (values : Vec.Vec Value Count) →
  Product.permuteLinks constructedNativeC3Program values
  ≡ C3.forwardVector values
constructedNativeC3AllVectors proof values =
  Single.singleVectorC3ImpliesAllVectors
    (constructedNativeC3Certificate proof) values
