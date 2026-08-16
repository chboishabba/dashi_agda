module DASHI.Foundations.HexTruthS3CarrierBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", Graduate Texts in Mathematics 163,
-- Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- DASHI CONTRIBUTION
--
-- Base369.HexTruth and the six ternary coordinate permutations have the same
-- finite carrier cardinality, so this module gives an explicit two-sided
-- carrier chart between them. It also proves that the chart is NOT a group
-- isomorphism from the existing cyclic Base369.hexXor operation to S3
-- permutation composition. Equal six-state carriers therefore remain distinct
-- algebraic lenses while the S3 chart supplies the exact route into the
-- reversible sector of the 27 ternary endomorphisms.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import Base369 as Base
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3

hexToPermutation : Base.HexTruth → Perm.TriPermutation
hexToPermutation Base.hex-0 = Perm.permIdentity
hexToPermutation Base.hex-1 = Perm.permRotate
hexToPermutation Base.hex-2 = Perm.permRotate2
hexToPermutation Base.hex-3 = Perm.permSwapLowMid
hexToPermutation Base.hex-4 = Perm.permSwapLowHigh
hexToPermutation Base.hex-5 = Perm.permSwapMidHigh

permutationToHex : Perm.TriPermutation → Base.HexTruth
permutationToHex Perm.permIdentity = Base.hex-0
permutationToHex Perm.permRotate = Base.hex-1
permutationToHex Perm.permRotate2 = Base.hex-2
permutationToHex Perm.permSwapLowMid = Base.hex-3
permutationToHex Perm.permSwapLowHigh = Base.hex-4
permutationToHex Perm.permSwapMidHigh = Base.hex-5

hexRoundTrip :
  (hex : Base.HexTruth) →
  permutationToHex (hexToPermutation hex) ≡ hex
hexRoundTrip Base.hex-0 = refl
hexRoundTrip Base.hex-1 = refl
hexRoundTrip Base.hex-2 = refl
hexRoundTrip Base.hex-3 = refl
hexRoundTrip Base.hex-4 = refl
hexRoundTrip Base.hex-5 = refl

permutationRoundTrip :
  (permutation : Perm.TriPermutation) →
  hexToPermutation (permutationToHex permutation) ≡ permutation
permutationRoundTrip Perm.permIdentity = refl
permutationRoundTrip Perm.permRotate = refl
permutationRoundTrip Perm.permRotate2 = refl
permutationRoundTrip Perm.permSwapLowMid = refl
permutationRoundTrip Perm.permSwapLowHigh = refl
permutationRoundTrip Perm.permSwapMidHigh = refl

------------------------------------------------------------------------
-- Concrete failure of operation preservation.
--
-- hex-1 xor hex-3 = hex-4 under the existing cyclic C6 operation, whereas
-- permRotate . permSwapLowMid = permSwapLowHigh for this particular pair; so
-- choose a pair where C6 commutativity and S3 noncommutativity force a split.
------------------------------------------------------------------------

hexPairCommutes :
  Base.hexXor Base.hex-1 Base.hex-3
  ≡ Base.hexXor Base.hex-3 Base.hex-1
hexPairCommutes = refl

s3ImagePairDoesNotCommute :
  S3._∙_
    (hexToPermutation Base.hex-1)
    (hexToPermutation Base.hex-3)
  ≡
  S3._∙_
    (hexToPermutation Base.hex-3)
    (hexToPermutation Base.hex-1)
  → ⊥
s3ImagePairDoesNotCommute = S3.nonCommutativeWitness

hexCarrierChartCannotPreserveBothProducts :
  ((left right : Base.HexTruth) →
    hexToPermutation (Base.hexXor left right)
    ≡ S3._∙_ (hexToPermutation left) (hexToPermutation right)) →
  ⊥
hexCarrierChartCannotPreserveBothProducts hom =
  s3ImagePairDoesNotCommute
    (trans
      (sym (hom Base.hex-1 Base.hex-3))
      (trans
        (cong hexToPermutation hexPairCommutes)
        (hom Base.hex-3 Base.hex-1)))
  where
    open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

record HexTruthS3CarrierBoundary : Set where
  field
    carrierBijectionConstructed : Bool
    carrierBijectionConstructedIsTrue :
      carrierBijectionConstructed ≡ true

    existingHexXorIdentifiedWithS3Product : Bool
    existingHexXorIdentifiedWithS3ProductIsFalse :
      existingHexXorIdentifiedWithS3Product ≡ false

    reversible27SectorReceivesS3Chart : Bool
    reversible27SectorReceivesS3ChartIsTrue :
      reversible27SectorReceivesS3Chart ≡ true

canonicalHexTruthS3CarrierBoundary : HexTruthS3CarrierBoundary
canonicalHexTruthS3CarrierBoundary =
  record
    { carrierBijectionConstructed = true
    ; carrierBijectionConstructedIsTrue = refl
    ; existingHexXorIdentifiedWithS3Product = false
    ; existingHexXorIdentifiedWithS3ProductIsFalse = refl
    ; reversible27SectorReceivesS3Chart = true
    ; reversible27SectorReceivesS3ChartIsTrue = refl
    }
