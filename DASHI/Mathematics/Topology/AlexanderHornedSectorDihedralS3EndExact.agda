module DASHI.Mathematics.Topology.AlexanderHornedSectorDihedralS3EndExact where

------------------------------------------------------------------------
-- THE VIDEO'S SIX ABC PERMUTATIONS ACT ON THREE HORNED ROOT SECTORS.
--
-- Reuse pre-existing EXACT S3 multiplication/action and the original
-- native balanced-ternary end TOWER. A selected S3 permutation acts
-- on the EXTERNAL sector coordinate while preserving every trit
-- prefix. The existing C3 sector rotation is its even 3-cycle part.
--
-- A chosen reflection exchanges TWO sectors and conjugates the external
-- C3 to its inverse: s r s = r^-1. Thus the abstract sector-label
-- dihedral D3 really is S3 (six actions), NOT C6. This is the
-- mathematically legitimate ABC permutation cross-pollination.
--
-- A sector-label reflection is NOT automatically an actual ambient
-- reflection of three supported wild balls: geometric collars, same
-- objects and ambient equivariance still require independent proof.
-- Nor is it root-path monodromy in polynomial coefficient space.
--
-- Original owners: Dixon--Mortimer finite S3; DASHI TernaryPermutation
-- S3LawsExact; #1244 native end inverse-limit and Hatcher classic.
-- No ESD edits / no postulates; Agda source written, kernel pending.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3
import DASHI.Mathematics.Topology.AlexanderHornedNativeBalancedTernaryEndTowerExact as End
import DASHI.Mathematics.Topology.AlexanderHornedLocalFibreTetrationTransportExact as Chart

permuteSector : Perm.TriPermutation → C3.C3 → C3.C3
permuteSector p c =
  Chart.truthAsSector
    (Perm.applyPermutation p (Chart.sectorAsTruth c))

permuteAddress :
  (n : Nat) → Perm.TriPermutation →
  End.BalancedLevel n → End.BalancedLevel n
permuteAddress n p (c , xs) = permuteSector p c , xs

permuteSectorIdentity :
  (c : C3.C3) →
  permuteSector Perm.permIdentity c ≡ c
permuteSectorIdentity c = Chart.sectorTruthRoundTrip c

permuteSectorComposition :
  (p q : Perm.TriPermutation) (c : C3.C3) →
  permuteSector (S3._∙_ p q) c
    ≡ permuteSector p (permuteSector q c)
permuteSectorComposition p q c
  rewrite Chart.truthSectorRoundTrip
    (Perm.applyPermutation q (Chart.sectorAsTruth c)) =
  cong Chart.truthAsSector
    (S3.applyComposition p q (Chart.sectorAsTruth c))

permuteAddressComposition :
  (n : Nat) (p q : Perm.TriPermutation)
  (x : End.BalancedLevel n) →
  permuteAddress n (S3._∙_ p q) x
    ≡ permuteAddress n p (permuteAddress n q x)
permuteAddressComposition n p q (c , xs) =
  cong (λ d → (d , xs)) (permuteSectorComposition p q c)

permuteAddressIdentity :
  (n : Nat) (x : End.BalancedLevel n) →
  permuteAddress n Perm.permIdentity x ≡ x
permuteAddressIdentity n (c , xs) =
  cong (λ d → (d , xs)) (permuteSectorIdentity c)

permutationCommutesWithEndProjection :
  (n : Nat) (p : Perm.TriPermutation)
  (x : End.BalancedLevel (suc n)) →
  End.balancedProjection n (permuteAddress (suc n) p x)
    ≡ permuteAddress n p (End.balancedProjection n x)
permutationCommutesWithEndProjection n p (c , xs) = refl

-- Full 6×3 table: a sector action with the original six permutations.
sectorPermutationRoundTripWitness :
  (p : Perm.TriPermutation) (c : C3.C3) →
  permuteSector (Perm.inversePermutation p) (permuteSector p c) ≡ c
sectorPermutationRoundTripWitness Perm.permIdentity C3.c0 = refl
sectorPermutationRoundTripWitness Perm.permIdentity C3.c1 = refl
sectorPermutationRoundTripWitness Perm.permIdentity C3.c2 = refl
sectorPermutationRoundTripWitness Perm.permRotate C3.c0 = refl
sectorPermutationRoundTripWitness Perm.permRotate C3.c1 = refl
sectorPermutationRoundTripWitness Perm.permRotate C3.c2 = refl
sectorPermutationRoundTripWitness Perm.permRotate2 C3.c0 = refl
sectorPermutationRoundTripWitness Perm.permRotate2 C3.c1 = refl
sectorPermutationRoundTripWitness Perm.permRotate2 C3.c2 = refl
sectorPermutationRoundTripWitness Perm.permSwapLowMid C3.c0 = refl
sectorPermutationRoundTripWitness Perm.permSwapLowMid C3.c1 = refl
sectorPermutationRoundTripWitness Perm.permSwapLowMid C3.c2 = refl
sectorPermutationRoundTripWitness Perm.permSwapLowHigh C3.c0 = refl
sectorPermutationRoundTripWitness Perm.permSwapLowHigh C3.c1 = refl
sectorPermutationRoundTripWitness Perm.permSwapLowHigh C3.c2 = refl
sectorPermutationRoundTripWitness Perm.permSwapMidHigh C3.c0 = refl
sectorPermutationRoundTripWitness Perm.permSwapMidHigh C3.c1 = refl
sectorPermutationRoundTripWitness Perm.permSwapMidHigh C3.c2 = refl

externalCycleExactlyOriginalRotation :
  (n : Nat) (x : End.BalancedLevel n) →
  permuteAddress n Perm.permRotate x
    ≡ End.rotateBalancedLevel n x
externalCycleExactlyOriginalRotation n (C3.c0 , xs) = refl
externalCycleExactlyOriginalRotation n (C3.c1 , xs) = refl
externalCycleExactlyOriginalRotation n (C3.c2 , xs) = refl

-- The selected reflection s swaps the outer two sector labels.
-- In the original S3 table s*r*s=r² and s²=identity.
sectorReflectionConjugatesCycle :
  S3._∙_
    (S3._∙_ Perm.permSwapLowHigh Perm.permRotate)
    Perm.permSwapLowHigh
  ≡ Perm.permRotate2
sectorReflectionConjugatesCycle = refl

sectorReflectionInvolutive :
  S3._∙_ Perm.permSwapLowHigh Perm.permSwapLowHigh
    ≡ Perm.permIdentity
sectorReflectionInvolutive = refl

-- Sign reversal of INTERNAL address trits is a separate involution.
-- Only this chosen EXTERNAL reflection inverts the external C3.
