module DASHI.Foundations.PolynomialS3RegularRationalBlockCertificateExact where

-- EXACT S3 REGULAR SIX-BLOCK CERTIFICATE WITH NO UNCHECKED AXIOMS.
-- Integer 6x6 basis and 54-scaled two-sided inverse. The actual
-- S3 left-regular action is conjugate to 1 ⊕ sign ⊕ std2 ⊕ std2.
-- Source mathematics: ordinary rational representation of S3,
-- Maschke (1899), Serre (1977); this explicit matrix owns no original
-- representation-theory theorem. Actual native 27 carrier bridge is
-- implemented independently and must be combined for O40.
-- Proofs are constructor-exhaustive Agda source; KERNEL PENDING.
-- No coefficient-root, wild-Hatcher or Monster3B same-object claim.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Data.Integer.Base using (_+_; _*_)
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3

data Six : Set where
  slot0 slot1 slot2 slot3 slot4 slot5 : Six

data Two : Set where
  lowIndex highIndex : Two

rowPermutation : Six → Perm.TriPermutation
rowPermutation slot0 = Perm.permIdentity
rowPermutation slot1 = Perm.permRotate
rowPermutation slot2 = Perm.permRotate2
rowPermutation slot3 = Perm.permSwapLowMid
rowPermutation slot4 = Perm.permSwapLowHigh
rowPermutation slot5 = Perm.permSwapMidHigh

permutationRow : Perm.TriPermutation → Six
permutationRow Perm.permIdentity = slot0
permutationRow Perm.permRotate = slot1
permutationRow Perm.permRotate2 = slot2
permutationRow Perm.permSwapLowMid = slot3
permutationRow Perm.permSwapLowHigh = slot4
permutationRow Perm.permSwapMidHigh = slot5

rowPermutationRoundTrip : (i : Six) →
  permutationRow (rowPermutation i) ≡ i
rowPermutationRoundTrip slot0 = refl
rowPermutationRoundTrip slot1 = refl
rowPermutationRoundTrip slot2 = refl
rowPermutationRoundTrip slot3 = refl
rowPermutationRoundTrip slot4 = refl
rowPermutationRoundTrip slot5 = refl

permutationRowRoundTrip : (p : Perm.TriPermutation) →
  rowPermutation (permutationRow p) ≡ p
permutationRowRoundTrip Perm.permIdentity = refl
permutationRowRoundTrip Perm.permRotate = refl
permutationRowRoundTrip Perm.permRotate2 = refl
permutationRowRoundTrip Perm.permSwapLowMid = refl
permutationRowRoundTrip Perm.permSwapLowHigh = refl
permutationRowRoundTrip Perm.permSwapMidHigh = refl

leftInverseRow : Perm.TriPermutation → Six → Six
leftInverseRow p g =
  permutationRow (S3._∙_ (Perm.inversePermutation p) (rowPermutation g))

signInt : Perm.TriPermutation → Int
signInt Perm.permIdentity = pos 1
signInt Perm.permRotate = pos 1
signInt Perm.permRotate2 = pos 1
signInt Perm.permSwapLowMid = negsuc 0
signInt Perm.permSwapLowHigh = negsuc 0
signInt Perm.permSwapMidHigh = negsuc 0

rho : Perm.TriPermutation → Two → Two → Int
rho Perm.permIdentity lowIndex lowIndex = pos 1
rho Perm.permIdentity lowIndex highIndex = pos 0
rho Perm.permIdentity highIndex lowIndex = pos 0
rho Perm.permIdentity highIndex highIndex = pos 1
rho Perm.permRotate lowIndex lowIndex = negsuc 0
rho Perm.permRotate lowIndex highIndex = negsuc 0
rho Perm.permRotate highIndex lowIndex = pos 1
rho Perm.permRotate highIndex highIndex = pos 0
rho Perm.permRotate2 lowIndex lowIndex = pos 0
rho Perm.permRotate2 lowIndex highIndex = pos 1
rho Perm.permRotate2 highIndex lowIndex = negsuc 0
rho Perm.permRotate2 highIndex highIndex = negsuc 0
rho Perm.permSwapLowMid lowIndex lowIndex = pos 0
rho Perm.permSwapLowMid lowIndex highIndex = pos 1
rho Perm.permSwapLowMid highIndex lowIndex = pos 1
rho Perm.permSwapLowMid highIndex highIndex = pos 0
rho Perm.permSwapLowHigh lowIndex lowIndex = negsuc 0
rho Perm.permSwapLowHigh lowIndex highIndex = negsuc 0
rho Perm.permSwapLowHigh highIndex lowIndex = pos 0
rho Perm.permSwapLowHigh highIndex highIndex = pos 1
rho Perm.permSwapMidHigh lowIndex lowIndex = pos 1
rho Perm.permSwapMidHigh lowIndex highIndex = pos 0
rho Perm.permSwapMidHigh highIndex lowIndex = negsuc 0
rho Perm.permSwapMidHigh highIndex highIndex = negsuc 0

-- Basis row order: identity, r, r², s01, s02, s12.
-- Columns: trivial, sign, and matrix coefficients
-- rho(g^-1)_00, rho(g^-1)_01, rho(g^-1)_10, rho(g^-1)_11.
basis6 : Six → Six → Int
basis6 slot0 slot0 = pos 1
basis6 slot0 slot1 = pos 1
basis6 slot0 slot2 = pos 1
basis6 slot0 slot3 = pos 0
basis6 slot0 slot4 = pos 0
basis6 slot0 slot5 = pos 1
basis6 slot1 slot0 = pos 1
basis6 slot1 slot1 = pos 1
basis6 slot1 slot2 = pos 0
basis6 slot1 slot3 = pos 1
basis6 slot1 slot4 = negsuc 0
basis6 slot1 slot5 = negsuc 0
basis6 slot2 slot0 = pos 1
basis6 slot2 slot1 = pos 1
basis6 slot2 slot2 = negsuc 0
basis6 slot2 slot3 = negsuc 0
basis6 slot2 slot4 = pos 1
basis6 slot2 slot5 = pos 0
basis6 slot3 slot0 = pos 1
basis6 slot3 slot1 = negsuc 0
basis6 slot3 slot2 = pos 0
basis6 slot3 slot3 = pos 1
basis6 slot3 slot4 = pos 1
basis6 slot3 slot5 = pos 0
basis6 slot4 slot0 = pos 1
basis6 slot4 slot1 = negsuc 0
basis6 slot4 slot2 = negsuc 0
basis6 slot4 slot3 = negsuc 0
basis6 slot4 slot4 = pos 0
basis6 slot4 slot5 = pos 1
basis6 slot5 slot0 = pos 1
basis6 slot5 slot1 = negsuc 0
basis6 slot5 slot2 = pos 1
basis6 slot5 slot3 = pos 0
basis6 slot5 slot4 = negsuc 0
basis6 slot5 slot5 = negsuc 0

-- Exactly 54 * inverse(basis6), with only integer entries.
scaledInverse6 : Six → Six → Int
scaledInverse6 slot0 slot0 = pos 9
scaledInverse6 slot0 slot1 = pos 9
scaledInverse6 slot0 slot2 = pos 9
scaledInverse6 slot0 slot3 = pos 9
scaledInverse6 slot0 slot4 = pos 9
scaledInverse6 slot0 slot5 = pos 9
scaledInverse6 slot1 slot0 = pos 9
scaledInverse6 slot1 slot1 = pos 9
scaledInverse6 slot1 slot2 = pos 9
scaledInverse6 slot1 slot3 = negsuc 8
scaledInverse6 slot1 slot4 = negsuc 8
scaledInverse6 slot1 slot5 = negsuc 8
scaledInverse6 slot2 slot0 = pos 18
scaledInverse6 slot2 slot1 = negsuc 17
scaledInverse6 slot2 slot2 = pos 0
scaledInverse6 slot2 slot3 = pos 0
scaledInverse6 slot2 slot4 = negsuc 17
scaledInverse6 slot2 slot5 = pos 18
scaledInverse6 slot3 slot0 = pos 0
scaledInverse6 slot3 slot1 = pos 18
scaledInverse6 slot3 slot2 = negsuc 17
scaledInverse6 slot3 slot3 = pos 18
scaledInverse6 slot3 slot4 = pos 0
scaledInverse6 slot3 slot5 = negsuc 17
scaledInverse6 slot4 slot0 = pos 0
scaledInverse6 slot4 slot1 = negsuc 17
scaledInverse6 slot4 slot2 = pos 18
scaledInverse6 slot4 slot3 = pos 18
scaledInverse6 slot4 slot4 = negsuc 17
scaledInverse6 slot4 slot5 = pos 0
scaledInverse6 slot5 slot0 = pos 18
scaledInverse6 slot5 slot1 = pos 0
scaledInverse6 slot5 slot2 = negsuc 17
scaledInverse6 slot5 slot3 = pos 0
scaledInverse6 slot5 slot4 = pos 18
scaledInverse6 slot5 slot5 = negsuc 17

deltaSix : Six → Six → Int
deltaSix slot0 slot0 = pos 1
deltaSix slot0 slot1 = pos 0
deltaSix slot0 slot2 = pos 0
deltaSix slot0 slot3 = pos 0
deltaSix slot0 slot4 = pos 0
deltaSix slot0 slot5 = pos 0
deltaSix slot1 slot0 = pos 0
deltaSix slot1 slot1 = pos 1
deltaSix slot1 slot2 = pos 0
deltaSix slot1 slot3 = pos 0
deltaSix slot1 slot4 = pos 0
deltaSix slot1 slot5 = pos 0
deltaSix slot2 slot0 = pos 0
deltaSix slot2 slot1 = pos 0
deltaSix slot2 slot2 = pos 1
deltaSix slot2 slot3 = pos 0
deltaSix slot2 slot4 = pos 0
deltaSix slot2 slot5 = pos 0
deltaSix slot3 slot0 = pos 0
deltaSix slot3 slot1 = pos 0
deltaSix slot3 slot2 = pos 0
deltaSix slot3 slot3 = pos 1
deltaSix slot3 slot4 = pos 0
deltaSix slot3 slot5 = pos 0
deltaSix slot4 slot0 = pos 0
deltaSix slot4 slot1 = pos 0
deltaSix slot4 slot2 = pos 0
deltaSix slot4 slot3 = pos 0
deltaSix slot4 slot4 = pos 1
deltaSix slot4 slot5 = pos 0
deltaSix slot5 slot0 = pos 0
deltaSix slot5 slot1 = pos 0
deltaSix slot5 slot2 = pos 0
deltaSix slot5 slot3 = pos 0
deltaSix slot5 slot4 = pos 0
deltaSix slot5 slot5 = pos 1

dotSix : (A B : Six → Six → Int) → Six → Six → Int
dotSix A B i j =
  A i slot0 * B slot0 j + A i slot1 * B slot1 j
  + A i slot2 * B slot2 j + A i slot3 * B slot3 j
  + A i slot4 * B slot4 j + A i slot5 * B slot5 j

basisScaledInverse : (i j : Six) → dotSix basis6 scaledInverse6 i j ≡ (pos 54) * deltaSix i j
basisScaledInverse slot0 slot0 = refl
basisScaledInverse slot0 slot1 = refl
basisScaledInverse slot0 slot2 = refl
basisScaledInverse slot0 slot3 = refl
basisScaledInverse slot0 slot4 = refl
basisScaledInverse slot0 slot5 = refl
basisScaledInverse slot1 slot0 = refl
basisScaledInverse slot1 slot1 = refl
basisScaledInverse slot1 slot2 = refl
basisScaledInverse slot1 slot3 = refl
basisScaledInverse slot1 slot4 = refl
basisScaledInverse slot1 slot5 = refl
basisScaledInverse slot2 slot0 = refl
basisScaledInverse slot2 slot1 = refl
basisScaledInverse slot2 slot2 = refl
basisScaledInverse slot2 slot3 = refl
basisScaledInverse slot2 slot4 = refl
basisScaledInverse slot2 slot5 = refl
basisScaledInverse slot3 slot0 = refl
basisScaledInverse slot3 slot1 = refl
basisScaledInverse slot3 slot2 = refl
basisScaledInverse slot3 slot3 = refl
basisScaledInverse slot3 slot4 = refl
basisScaledInverse slot3 slot5 = refl
basisScaledInverse slot4 slot0 = refl
basisScaledInverse slot4 slot1 = refl
basisScaledInverse slot4 slot2 = refl
basisScaledInverse slot4 slot3 = refl
basisScaledInverse slot4 slot4 = refl
basisScaledInverse slot4 slot5 = refl
basisScaledInverse slot5 slot0 = refl
basisScaledInverse slot5 slot1 = refl
basisScaledInverse slot5 slot2 = refl
basisScaledInverse slot5 slot3 = refl
basisScaledInverse slot5 slot4 = refl
basisScaledInverse slot5 slot5 = refl

inverseScaledBasis : (i j : Six) → dotSix scaledInverse6 basis6 i j ≡ (pos 54) * deltaSix i j
inverseScaledBasis slot0 slot0 = refl
inverseScaledBasis slot0 slot1 = refl
inverseScaledBasis slot0 slot2 = refl
inverseScaledBasis slot0 slot3 = refl
inverseScaledBasis slot0 slot4 = refl
inverseScaledBasis slot0 slot5 = refl
inverseScaledBasis slot1 slot0 = refl
inverseScaledBasis slot1 slot1 = refl
inverseScaledBasis slot1 slot2 = refl
inverseScaledBasis slot1 slot3 = refl
inverseScaledBasis slot1 slot4 = refl
inverseScaledBasis slot1 slot5 = refl
inverseScaledBasis slot2 slot0 = refl
inverseScaledBasis slot2 slot1 = refl
inverseScaledBasis slot2 slot2 = refl
inverseScaledBasis slot2 slot3 = refl
inverseScaledBasis slot2 slot4 = refl
inverseScaledBasis slot2 slot5 = refl
inverseScaledBasis slot3 slot0 = refl
inverseScaledBasis slot3 slot1 = refl
inverseScaledBasis slot3 slot2 = refl
inverseScaledBasis slot3 slot3 = refl
inverseScaledBasis slot3 slot4 = refl
inverseScaledBasis slot3 slot5 = refl
inverseScaledBasis slot4 slot0 = refl
inverseScaledBasis slot4 slot1 = refl
inverseScaledBasis slot4 slot2 = refl
inverseScaledBasis slot4 slot3 = refl
inverseScaledBasis slot4 slot4 = refl
inverseScaledBasis slot4 slot5 = refl
inverseScaledBasis slot5 slot0 = refl
inverseScaledBasis slot5 slot1 = refl
inverseScaledBasis slot5 slot2 = refl
inverseScaledBasis slot5 slot3 = refl
inverseScaledBasis slot5 slot4 = refl
inverseScaledBasis slot5 slot5 = refl

-- Diagonal 1 ⊕ sign ⊕ rho ⊕ rho.
blockAction : Perm.TriPermutation → Six → Six → Int
blockAction p slot0 slot0 = pos 1
blockAction p slot0 slot1 = pos 0
blockAction p slot0 slot2 = pos 0
blockAction p slot0 slot3 = pos 0
blockAction p slot0 slot4 = pos 0
blockAction p slot0 slot5 = pos 0
blockAction p slot1 slot0 = pos 0
blockAction p slot1 slot1 = signInt p
blockAction p slot1 slot2 = pos 0
blockAction p slot1 slot3 = pos 0
blockAction p slot1 slot4 = pos 0
blockAction p slot1 slot5 = pos 0
blockAction p slot2 slot0 = pos 0
blockAction p slot2 slot1 = pos 0
blockAction p slot2 slot2 = rho p lowIndex lowIndex
blockAction p slot2 slot3 = rho p lowIndex highIndex
blockAction p slot2 slot4 = pos 0
blockAction p slot2 slot5 = pos 0
blockAction p slot3 slot0 = pos 0
blockAction p slot3 slot1 = pos 0
blockAction p slot3 slot2 = rho p highIndex lowIndex
blockAction p slot3 slot3 = rho p highIndex highIndex
blockAction p slot3 slot4 = pos 0
blockAction p slot3 slot5 = pos 0
blockAction p slot4 slot0 = pos 0
blockAction p slot4 slot1 = pos 0
blockAction p slot4 slot2 = pos 0
blockAction p slot4 slot3 = pos 0
blockAction p slot4 slot4 = rho p lowIndex lowIndex
blockAction p slot4 slot5 = rho p lowIndex highIndex
blockAction p slot5 slot0 = pos 0
blockAction p slot5 slot1 = pos 0
blockAction p slot5 slot2 = pos 0
blockAction p slot5 slot3 = pos 0
blockAction p slot5 slot4 = rho p highIndex lowIndex
blockAction p slot5 slot5 = rho p highIndex highIndex

-- All 6 × 6 × 6 instances of the actual S3-intertwining square.
regularBlockIntertwines :
  (p : Perm.TriPermutation) (i j : Six) →
  basis6 (leftInverseRow p i) j ≡ dotSix basis6 (blockAction p) i j
regularBlockIntertwines Perm.permIdentity slot0 slot0 = refl
regularBlockIntertwines Perm.permIdentity slot0 slot1 = refl
regularBlockIntertwines Perm.permIdentity slot0 slot2 = refl
regularBlockIntertwines Perm.permIdentity slot0 slot3 = refl
regularBlockIntertwines Perm.permIdentity slot0 slot4 = refl
regularBlockIntertwines Perm.permIdentity slot0 slot5 = refl
regularBlockIntertwines Perm.permIdentity slot1 slot0 = refl
regularBlockIntertwines Perm.permIdentity slot1 slot1 = refl
regularBlockIntertwines Perm.permIdentity slot1 slot2 = refl
regularBlockIntertwines Perm.permIdentity slot1 slot3 = refl
regularBlockIntertwines Perm.permIdentity slot1 slot4 = refl
regularBlockIntertwines Perm.permIdentity slot1 slot5 = refl
regularBlockIntertwines Perm.permIdentity slot2 slot0 = refl
regularBlockIntertwines Perm.permIdentity slot2 slot1 = refl
regularBlockIntertwines Perm.permIdentity slot2 slot2 = refl
regularBlockIntertwines Perm.permIdentity slot2 slot3 = refl
regularBlockIntertwines Perm.permIdentity slot2 slot4 = refl
regularBlockIntertwines Perm.permIdentity slot2 slot5 = refl
regularBlockIntertwines Perm.permIdentity slot3 slot0 = refl
regularBlockIntertwines Perm.permIdentity slot3 slot1 = refl
regularBlockIntertwines Perm.permIdentity slot3 slot2 = refl
regularBlockIntertwines Perm.permIdentity slot3 slot3 = refl
regularBlockIntertwines Perm.permIdentity slot3 slot4 = refl
regularBlockIntertwines Perm.permIdentity slot3 slot5 = refl
regularBlockIntertwines Perm.permIdentity slot4 slot0 = refl
regularBlockIntertwines Perm.permIdentity slot4 slot1 = refl
regularBlockIntertwines Perm.permIdentity slot4 slot2 = refl
regularBlockIntertwines Perm.permIdentity slot4 slot3 = refl
regularBlockIntertwines Perm.permIdentity slot4 slot4 = refl
regularBlockIntertwines Perm.permIdentity slot4 slot5 = refl
regularBlockIntertwines Perm.permIdentity slot5 slot0 = refl
regularBlockIntertwines Perm.permIdentity slot5 slot1 = refl
regularBlockIntertwines Perm.permIdentity slot5 slot2 = refl
regularBlockIntertwines Perm.permIdentity slot5 slot3 = refl
regularBlockIntertwines Perm.permIdentity slot5 slot4 = refl
regularBlockIntertwines Perm.permIdentity slot5 slot5 = refl
regularBlockIntertwines Perm.permRotate slot0 slot0 = refl
regularBlockIntertwines Perm.permRotate slot0 slot1 = refl
regularBlockIntertwines Perm.permRotate slot0 slot2 = refl
regularBlockIntertwines Perm.permRotate slot0 slot3 = refl
regularBlockIntertwines Perm.permRotate slot0 slot4 = refl
regularBlockIntertwines Perm.permRotate slot0 slot5 = refl
regularBlockIntertwines Perm.permRotate slot1 slot0 = refl
regularBlockIntertwines Perm.permRotate slot1 slot1 = refl
regularBlockIntertwines Perm.permRotate slot1 slot2 = refl
regularBlockIntertwines Perm.permRotate slot1 slot3 = refl
regularBlockIntertwines Perm.permRotate slot1 slot4 = refl
regularBlockIntertwines Perm.permRotate slot1 slot5 = refl
regularBlockIntertwines Perm.permRotate slot2 slot0 = refl
regularBlockIntertwines Perm.permRotate slot2 slot1 = refl
regularBlockIntertwines Perm.permRotate slot2 slot2 = refl
regularBlockIntertwines Perm.permRotate slot2 slot3 = refl
regularBlockIntertwines Perm.permRotate slot2 slot4 = refl
regularBlockIntertwines Perm.permRotate slot2 slot5 = refl
regularBlockIntertwines Perm.permRotate slot3 slot0 = refl
regularBlockIntertwines Perm.permRotate slot3 slot1 = refl
regularBlockIntertwines Perm.permRotate slot3 slot2 = refl
regularBlockIntertwines Perm.permRotate slot3 slot3 = refl
regularBlockIntertwines Perm.permRotate slot3 slot4 = refl
regularBlockIntertwines Perm.permRotate slot3 slot5 = refl
regularBlockIntertwines Perm.permRotate slot4 slot0 = refl
regularBlockIntertwines Perm.permRotate slot4 slot1 = refl
regularBlockIntertwines Perm.permRotate slot4 slot2 = refl
regularBlockIntertwines Perm.permRotate slot4 slot3 = refl
regularBlockIntertwines Perm.permRotate slot4 slot4 = refl
regularBlockIntertwines Perm.permRotate slot4 slot5 = refl
regularBlockIntertwines Perm.permRotate slot5 slot0 = refl
regularBlockIntertwines Perm.permRotate slot5 slot1 = refl
regularBlockIntertwines Perm.permRotate slot5 slot2 = refl
regularBlockIntertwines Perm.permRotate slot5 slot3 = refl
regularBlockIntertwines Perm.permRotate slot5 slot4 = refl
regularBlockIntertwines Perm.permRotate slot5 slot5 = refl
regularBlockIntertwines Perm.permRotate2 slot0 slot0 = refl
regularBlockIntertwines Perm.permRotate2 slot0 slot1 = refl
regularBlockIntertwines Perm.permRotate2 slot0 slot2 = refl
regularBlockIntertwines Perm.permRotate2 slot0 slot3 = refl
regularBlockIntertwines Perm.permRotate2 slot0 slot4 = refl
regularBlockIntertwines Perm.permRotate2 slot0 slot5 = refl
regularBlockIntertwines Perm.permRotate2 slot1 slot0 = refl
regularBlockIntertwines Perm.permRotate2 slot1 slot1 = refl
regularBlockIntertwines Perm.permRotate2 slot1 slot2 = refl
regularBlockIntertwines Perm.permRotate2 slot1 slot3 = refl
regularBlockIntertwines Perm.permRotate2 slot1 slot4 = refl
regularBlockIntertwines Perm.permRotate2 slot1 slot5 = refl
regularBlockIntertwines Perm.permRotate2 slot2 slot0 = refl
regularBlockIntertwines Perm.permRotate2 slot2 slot1 = refl
regularBlockIntertwines Perm.permRotate2 slot2 slot2 = refl
regularBlockIntertwines Perm.permRotate2 slot2 slot3 = refl
regularBlockIntertwines Perm.permRotate2 slot2 slot4 = refl
regularBlockIntertwines Perm.permRotate2 slot2 slot5 = refl
regularBlockIntertwines Perm.permRotate2 slot3 slot0 = refl
regularBlockIntertwines Perm.permRotate2 slot3 slot1 = refl
regularBlockIntertwines Perm.permRotate2 slot3 slot2 = refl
regularBlockIntertwines Perm.permRotate2 slot3 slot3 = refl
regularBlockIntertwines Perm.permRotate2 slot3 slot4 = refl
regularBlockIntertwines Perm.permRotate2 slot3 slot5 = refl
regularBlockIntertwines Perm.permRotate2 slot4 slot0 = refl
regularBlockIntertwines Perm.permRotate2 slot4 slot1 = refl
regularBlockIntertwines Perm.permRotate2 slot4 slot2 = refl
regularBlockIntertwines Perm.permRotate2 slot4 slot3 = refl
regularBlockIntertwines Perm.permRotate2 slot4 slot4 = refl
regularBlockIntertwines Perm.permRotate2 slot4 slot5 = refl
regularBlockIntertwines Perm.permRotate2 slot5 slot0 = refl
regularBlockIntertwines Perm.permRotate2 slot5 slot1 = refl
regularBlockIntertwines Perm.permRotate2 slot5 slot2 = refl
regularBlockIntertwines Perm.permRotate2 slot5 slot3 = refl
regularBlockIntertwines Perm.permRotate2 slot5 slot4 = refl
regularBlockIntertwines Perm.permRotate2 slot5 slot5 = refl
regularBlockIntertwines Perm.permSwapLowMid slot0 slot0 = refl
regularBlockIntertwines Perm.permSwapLowMid slot0 slot1 = refl
regularBlockIntertwines Perm.permSwapLowMid slot0 slot2 = refl
regularBlockIntertwines Perm.permSwapLowMid slot0 slot3 = refl
regularBlockIntertwines Perm.permSwapLowMid slot0 slot4 = refl
regularBlockIntertwines Perm.permSwapLowMid slot0 slot5 = refl
regularBlockIntertwines Perm.permSwapLowMid slot1 slot0 = refl
regularBlockIntertwines Perm.permSwapLowMid slot1 slot1 = refl
regularBlockIntertwines Perm.permSwapLowMid slot1 slot2 = refl
regularBlockIntertwines Perm.permSwapLowMid slot1 slot3 = refl
regularBlockIntertwines Perm.permSwapLowMid slot1 slot4 = refl
regularBlockIntertwines Perm.permSwapLowMid slot1 slot5 = refl
regularBlockIntertwines Perm.permSwapLowMid slot2 slot0 = refl
regularBlockIntertwines Perm.permSwapLowMid slot2 slot1 = refl
regularBlockIntertwines Perm.permSwapLowMid slot2 slot2 = refl
regularBlockIntertwines Perm.permSwapLowMid slot2 slot3 = refl
regularBlockIntertwines Perm.permSwapLowMid slot2 slot4 = refl
regularBlockIntertwines Perm.permSwapLowMid slot2 slot5 = refl
regularBlockIntertwines Perm.permSwapLowMid slot3 slot0 = refl
regularBlockIntertwines Perm.permSwapLowMid slot3 slot1 = refl
regularBlockIntertwines Perm.permSwapLowMid slot3 slot2 = refl
regularBlockIntertwines Perm.permSwapLowMid slot3 slot3 = refl
regularBlockIntertwines Perm.permSwapLowMid slot3 slot4 = refl
regularBlockIntertwines Perm.permSwapLowMid slot3 slot5 = refl
regularBlockIntertwines Perm.permSwapLowMid slot4 slot0 = refl
regularBlockIntertwines Perm.permSwapLowMid slot4 slot1 = refl
regularBlockIntertwines Perm.permSwapLowMid slot4 slot2 = refl
regularBlockIntertwines Perm.permSwapLowMid slot4 slot3 = refl
regularBlockIntertwines Perm.permSwapLowMid slot4 slot4 = refl
regularBlockIntertwines Perm.permSwapLowMid slot4 slot5 = refl
regularBlockIntertwines Perm.permSwapLowMid slot5 slot0 = refl
regularBlockIntertwines Perm.permSwapLowMid slot5 slot1 = refl
regularBlockIntertwines Perm.permSwapLowMid slot5 slot2 = refl
regularBlockIntertwines Perm.permSwapLowMid slot5 slot3 = refl
regularBlockIntertwines Perm.permSwapLowMid slot5 slot4 = refl
regularBlockIntertwines Perm.permSwapLowMid slot5 slot5 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot0 slot0 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot0 slot1 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot0 slot2 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot0 slot3 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot0 slot4 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot0 slot5 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot1 slot0 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot1 slot1 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot1 slot2 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot1 slot3 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot1 slot4 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot1 slot5 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot2 slot0 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot2 slot1 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot2 slot2 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot2 slot3 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot2 slot4 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot2 slot5 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot3 slot0 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot3 slot1 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot3 slot2 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot3 slot3 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot3 slot4 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot3 slot5 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot4 slot0 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot4 slot1 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot4 slot2 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot4 slot3 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot4 slot4 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot4 slot5 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot5 slot0 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot5 slot1 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot5 slot2 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot5 slot3 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot5 slot4 = refl
regularBlockIntertwines Perm.permSwapLowHigh slot5 slot5 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot0 slot0 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot0 slot1 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot0 slot2 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot0 slot3 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot0 slot4 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot0 slot5 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot1 slot0 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot1 slot1 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot1 slot2 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot1 slot3 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot1 slot4 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot1 slot5 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot2 slot0 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot2 slot1 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot2 slot2 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot2 slot3 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot2 slot4 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot2 slot5 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot3 slot0 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot3 slot1 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot3 slot2 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot3 slot3 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot3 slot4 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot3 slot5 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot4 slot0 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot4 slot1 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot4 slot2 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot4 slot3 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot4 slot4 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot4 slot5 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot5 slot0 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot5 slot1 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot5 slot2 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot5 slot3 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot5 slot4 = refl
regularBlockIntertwines Perm.permSwapMidHigh slot5 slot5 = refl

-- The 54-scaled inverse and actual group action make this a
-- rational (not integral) isomorphism; invertibility uses 54≠0
-- over Q, a standard field fact. No char-3 representation splitting
-- is inferred from this characteristic-zero certificate.
