module DASHI.Moonshine.OggSSP2BFi22d2NaturalTenSourceExact where

------------------------------------------------------------------------
-- FI22:2 NATURAL 2^10 : M22:2 DONOR
--
-- External source: ATLAS lists a maximal subgroup
--
--     2^10 : M22:2 < Fi22:2
--
-- of order 908328960 and index 142155.  The normal elementary-abelian 2^10
-- therefore supplies a source-native ten-dimensional F2 module for M22:2.
--
-- A repository GAP screen now constructs this subgroup, extracts the
-- conjugation action on the normal 2^10, identifies that action against the
-- Atlas M22:2 f2r10 modules, and tests its outer involutions for J2^5.
--
-- Until that runtime receipt is executed, this owner pays only the sourced
-- donor geometry.  It does NOT identify the donor with the Monster 2B Tate
-- head, nor does it pre-assert which Atlas 10d module/J2^5 row is obtained.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

fi22d2Order : Nat
fi22d2Order = 129123503308800

fi22d2Maximal2Pow10M22d2Order : Nat
fi22d2Maximal2Pow10M22d2Order = 908328960

normalKernelOrder : Nat
normalKernelOrder = 1024

normalKernelF2Rank : Nat
normalKernelF2Rank = 10

m22d2QuotientOrder : Nat
m22d2QuotientOrder = 887040

normalKernelOrderIs2Pow10 : normalKernelOrder ≡ 1024
normalKernelOrderIs2Pow10 = refl

normalKernelRankIsTen : normalKernelF2Rank ≡ 10
normalKernelRankIsTen = refl

data Fi22NaturalTenIsActualTwoBTateQ10 : Set where
data SourceDonorAloneDeterminesAtlasTenKind : Set where

fi22NaturalTenDoesNotIdentifyActualTateQ10 :
  Fi22NaturalTenIsActualTwoBTateQ10 → ⊥
fi22NaturalTenDoesNotIdentifyActualTateQ10 ()

sourceDonorAloneDoesNotDetermineAtlasTenKind :
  SourceDonorAloneDeterminesAtlasTenKind → ⊥
sourceDonorAloneDoesNotDetermineAtlasTenKind ()

record Fi22NaturalTenSourceStatus : Set where
  constructor fi22-natural-ten-source-status
  field
    atlasMaximalSubgroupSourced : Bool
    normalElementaryAbelianRankTenSourced : Bool
    quotientIsM22d2Sourced : Bool
    runtimeAtlasTenIdentificationPaid : Bool
    runtimeOuterJ2x5OnNaturalTenPaid : Bool
    actualTwoBTateSameObjectPaid : Bool

canonicalFi22NaturalTenSourceStatus : Fi22NaturalTenSourceStatus
canonicalFi22NaturalTenSourceStatus =
  fi22-natural-ten-source-status true true true false false false
