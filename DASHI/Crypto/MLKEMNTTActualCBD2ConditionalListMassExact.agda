module DASHI.Crypto.MLKEMNTTActualCBD2ConditionalListMassExact where

------------------------------------------------------------------------
-- CONDITIONAL LIST MASS FROM THE EXHAUSTIVE CBD2 COLLISION PROFILE
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Defensive partial-information / reconciliation context (not a proof input):
-- Yen-Ting Kuo; Atsushi Takayasu,
-- "A Lattice Attack on CRYSTALS-Kyber with Correlation Power Analysis",
-- ICISC 2023, LNCS, 202--220.
-- DOI: 10.1007/978-981-97-1235-9_11.
-- Earlier version: IACR ePrint 2023/1781.
--
-- The cited work motivates treating residual candidate ambiguity as a defensive
-- audit quantity.  Its lattice-recovery algorithm is not imported here.
--
-- If a finite candidate set of size N is partitioned by an observation, then
-- the sum, over candidates, of the size of the candidate's observation fibre is
--
--   N + 2 * (# unordered colliding candidate pairs).
--
-- Each candidate contributes itself once; each unordered pair in one fibre
-- contributes once to each endpoint.  The exhaustive 5^3 CBD2 triple slice has
-- N=125, 16 unordered collisions under scalar0, and zero under the joint
-- (scalar0,scalar2) observation.  Hence its conditional-list masses are
--
--   125 + 2*16 = 157,
--   125 + 2*0  = 125.
--
-- Under the uniform finite prior, these correspond to mean list sizes 157/125
-- and 125/125.  We keep the fractions as exact numerator/denominator data and
-- do not promote them into Shannon/min-entropy or full-scheme complexity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Crypto.MLKEMNTTActualCBD2FullTripleListProfileExact as Profile

listMassFromPairCollisions : Nat → Nat → Nat
listMassFromPairCollisions candidates unorderedPairs =
  candidates + 2 * unorderedPairs

firstScalarListMass : Nat
firstScalarListMass =
  listMassFromPairCollisions
    (Profile.candidateCount Profile.actualCBD2TripleSliceProfile)
    (Profile.firstCollisionPairs Profile.actualCBD2TripleSliceProfile)

jointTwoScalarListMass : Nat
jointTwoScalarListMass =
  listMassFromPairCollisions
    (Profile.candidateCount Profile.actualCBD2TripleSliceProfile)
    (Profile.twoScalarCollisionPairs Profile.actualCBD2TripleSliceProfile)

firstScalarListMassIs157 : firstScalarListMass ≡ 157
firstScalarListMassIs157 = refl

jointTwoScalarListMassIs125 : jointTwoScalarListMass ≡ 125
jointTwoScalarListMassIs125 = refl

record UniformMeanListSize : Set where
  constructor uniformMeanListSize
  field
    numerator denominator : Nat

open UniformMeanListSize public

firstScalarMeanListSize : UniformMeanListSize
firstScalarMeanListSize = uniformMeanListSize 157 125

twoScalarMeanListSize : UniformMeanListSize
twoScalarMeanListSize = uniformMeanListSize 125 125

firstScalarMeanNumeratorIs157 :
  numerator firstScalarMeanListSize ≡ 157
firstScalarMeanNumeratorIs157 = refl

twoScalarMeanNumeratorIs125 :
  numerator twoScalarMeanListSize ≡ 125
twoScalarMeanNumeratorIs125 = refl

commonDenominatorIs125 :
  denominator firstScalarMeanListSize ≡ 125
commonDenominatorIs125 = refl
