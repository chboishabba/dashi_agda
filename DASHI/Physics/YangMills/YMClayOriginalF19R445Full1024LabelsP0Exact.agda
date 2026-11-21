module DASHI.Physics.YangMills.YMClayOriginalF19R445Full1024LabelsP0Exact where

------------------------------------------------------------------------
-- YM P0: original F19 ADJACENT-SORT ↔ original R445 1024-bond codec.
--
-- Original master/#1444 F19 owns the physical adjacent-swap sorting
-- programme, its 64 ordered fine bond pairs and the 896 original
-- canonical-order spectator bonds; R445 owns the original selected
-- 128 + residual 896 bijection. Never reconstruct either permutation.
--
-- Compare F19's NOT-MEMBER Boolean spectator scan with R445's Dec-
-- membership residual filter after the previously proved SAME
-- 128 selected labels. No second physical measure or link carrier.
--
-- The closed equalities below are KERNEL COMPUTATION TARGETS and
-- not postulates or assumptions. The arbitrary-Link vector decoder
-- and all physical analytic estimates remain distinct work.
-- SOURCE-WRITTEN; Agda 2.9 kernel NOT run.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Native
import DASHI.Physics.YangMills.YMClayNativeSideFourPairSpectatorSortProgramExact as F19
import DASHI.Physics.YangMills.YMClayOriginalF19NativeR445SelectedOrderBIDIExact as Selected
import DASHI.Physics.YangMills.YMClayR445CanonicalBondPermutationCodecExact as R445

module _
  {Matrix Complex : Set} {N : Nat}
  (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  where

  originalF19SelectedPrefixMatchesR445 :
    F19.selectedOriginalFineBonds theory
      ≡ R445.originalR445SelectedBondEnumeration
  originalF19SelectedPrefixMatchesR445 =
    Selected.originalF19Selected128AreNativeR445Selected128
      (Native.sunExactSignedLinkGroup theory)

  -- Boolean membership (F19) and Dec membership (R445)
  -- agree on the same original canonical 1024 positive bonds.
  originalF19Original896SpectatorsMatchR445 :
    F19.remainingOriginalFineBonds theory
      ≡ R445.originalR445ResidualBondEnumeration
  originalF19Original896SpectatorsMatchR445
    rewrite originalF19SelectedPrefixMatchesR445 = refl

  -- SAME 1024 source labels (128 + 896), SAME original order.
  originalF19Complete1024LabelOrderMatchesR445 :
    F19.originalPairThenSpectatorLabels theory
      ≡ R445.originalR445PairResidualBondEnumeration
  originalF19Complete1024LabelOrderMatchesR445
    rewrite originalF19SelectedPrefixMatchesR445
          | originalF19Original896SpectatorsMatchR445 = refl

-- No physical E1/D1/D2/N1/G1 completion is inferred.
