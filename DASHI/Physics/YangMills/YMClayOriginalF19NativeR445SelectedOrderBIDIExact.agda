module DASHI.Physics.YangMills.YMClayOriginalF19NativeR445SelectedOrderBIDIExact where

------------------------------------------------------------------------
-- P0 source-native F19 ↔ R445 SELECTED LABEL ORDER BIDI.
--
-- The ORIGINAL F19 actual pair/spectator adjacent-sort target and
-- ORIGINAL R445 canonical permutation codec refer to the SAME 64
-- original coarse positive bonds, in the SAME original torus order.
-- Instead of comparing two invented coordinate maps or relying only
-- on "both have 128 labels", prove each pair's two original fine
-- positive bonds equal the R445 native PARITY pair at phases 0 and 1,
-- preserving the source-owned fine bond index and ORDER.
--
-- Original source proof owners on master and #1444:
-- * YMClayNativeSideFourPairDistinctCertificateExact
-- * YMClayNativeSideFourTwoLinkPairSameObjectExact
-- * YMClayR445OriginalNativeParityPairWeldExact
-- * YMClayR445OriginalAxialBondParityInjectiveExact
-- * YMClayR445CanonicalBondPermutationCodecExact
--
-- This closes the SELECTED 128-link label list equality only.
-- The 896 spectator-filter definitions, literal target Vec equality,
-- actual field-vector R445/F19 source identification, actual original
-- E1 all-cutoff analytic bounds and same-H OS are distinct obligations.
-- Source-written, not Agda-kernel checked.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as T
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.YMClayNativeSideFourPairDistinctCertificateExact as F19Pairs
import DASHI.Physics.YangMills.YMClayR445OriginalNativeParityPairWeldExact as OriginalParityWeld
import DASHI.Physics.YangMills.YMClayR445OriginalAxialBondParityInjectiveExact as OriginalParity
import DASHI.Physics.YangMills.YMClayR445CanonicalBondPermutationCodecExact as OriginalR445

-- This is just an induction VIEW of the original native parity codec.
-- It does not create new fine bonds or a new field-theory carrier.
originalParityPairLabels :
  List (T.PositiveBond 2) → List (T.PositiveBond 4)
originalParityPairLabels [] = []
originalParityPairLabels (coarse ∷ rest) =
  OriginalParity.originalR445SelectedFineBond coarse T.zeroᵢ ∷
  OriginalParity.originalR445SelectedFineBond
    coarse (T.sucᵢ T.zeroᵢ) ∷
  originalParityPairLabels rest

-- For each original F19 64-pair source, the original two fine links
-- are EXACTLY the two original R445 native parity-selected fine bonds.
originalF19PairListIsNativeR445Parity :
  ∀ {Value : Set} (group : Bond.ExactLinkGroup Value)
    (bonds : List (T.PositiveBond 2)) →
  F19Pairs.selectedFinePairLabels group bonds ≡
  originalParityPairLabels bonds
originalF19PairListIsNativeR445Parity group [] = refl
originalF19PairListIsNativeR445Parity group
    (T.pair site axis ∷ rest) =
  cong₂ _∷_
    (OriginalParityWeld.originalR445NativeFirstBondIsParity
      group site axis)
    (cong₂ _∷_
      (OriginalParityWeld.originalR445NativeSecondBondIsParity
        group site axis)
      (originalF19PairListIsNativeR445Parity group rest))

-- The *existing* original R445 selected enumeration is exactly
-- the cartesian coarse-bond × two axial-parity coordinates in the
-- existing original torus order. Same order as F19 recursion above.
originalParityPairsAreNativeR445SelectedEnumeration :
  (bonds : List (T.PositiveBond 2)) →
  originalParityPairLabels bonds
    ≡ T.map OriginalR445.originalSelectedEncode
        (T.cartesian bonds (T.allCyclicIndices (suc (suc zero))))
originalParityPairsAreNativeR445SelectedEnumeration [] = refl
originalParityPairsAreNativeR445SelectedEnumeration
    (coarse ∷ rest)
  rewrite originalParityPairsAreNativeR445SelectedEnumeration rest = refl

-- The first 128 fine positive-bond labels of the original FULL F19
-- 64-pair/896-spectator source are IDENTICAL to the native R445
-- canonical-permutation selected 128-link prefix, in ORDER.
originalF19Selected128AreNativeR445Selected128 :
  ∀ {Value : Set} (group : Bond.ExactLinkGroup Value) →
  F19Pairs.selectedFinePairLabels group
    F19Pairs.originalCoarseBondLabels
  ≡ OriginalR445.originalR445SelectedBondEnumeration
originalF19Selected128AreNativeR445Selected128 group =
  trans
    (originalF19PairListIsNativeR445Parity
      group F19Pairs.originalCoarseBondLabels)
    (originalParityPairsAreNativeR445SelectedEnumeration
      F19Pairs.originalCoarseBondLabels)
