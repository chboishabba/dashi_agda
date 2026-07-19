module DASHI.Interop.BodyKeepsScoreParityCompiledInverseAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.BodyMemoryCompiledInverseBridge as Compiled
import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Core.ParityLaneOperatorCore as Parity
import DASHI.Crypto.RSAPlusOneIdentitySection as RSAPlusOne

------------------------------------------------------------------------
-- Body-score parity / compiled-inverse adapter.
--
-- This is a thin indexing surface.  The even/odd receipts live in the
-- parity core, the live self/world and chart-local inverse machinery lives
-- in BodyMemoryCompiledInverseBridge, and the hidden-chart +1 analogy lives
-- in RSAPlusOneIdentitySection.
--
-- Reading:
--
--   even lane : live self/world relation remains separated
--   odd lane  : relation is compiled through a chart-local inverse
--   seam      : old inverse fails against the changed world
--   j+1       : a candidate carry/re-charting obligation
--
-- None of these rows is a diagnosis, treatment prescription, cure claim,
-- empirical result, or clinical authority surface.


data BodyScoreParityRole : Set where
  liveSelfWorldEvenRole : BodyScoreParityRole
  compiledInverseOddRole : BodyScoreParityRole
  residualSeamRole : BodyScoreParityRole
  jPlusOneCarryRole : BodyScoreParityRole

canonicalBodyScoreParityRoles : List BodyScoreParityRole
canonicalBodyScoreParityRoles =
  liveSelfWorldEvenRole
  ∷ compiledInverseOddRole
  ∷ residualSeamRole
  ∷ jPlusOneCarryRole
  ∷ []

record BodyScoreParityCompiledInverseAdapter : Set₁ where
  constructor mkBodyScoreParityCompiledInverseAdapter
  field
    evenLaneReceipt :
      Parity.ParityLaneReceipt

    evenLaneReceiptIsCanonical :
      evenLaneReceipt ≡ Parity.canonicalEvenParityLaneReceipt

    oddLaneReceipt :
      Parity.ParityLaneReceipt

    oddLaneReceiptIsCanonical :
      oddLaneReceipt ≡ Parity.canonicalOddParityLaneReceipt

    compiledInverseGateLedger :
      Compiled.CompiledInverseGateLedger

    compiledInverseGateLedgerIsCanonical :
      compiledInverseGateLedger ≡ Compiled.canonicalCompiledInverseGateLedger

    rsaPlusOneReference :
      RSAPlusOne.RSAPlusOneIdentitySectionReceipt

    parityRoles :
      List BodyScoreParityRole

    parityRolesAreCanonical :
      parityRoles ≡ canonicalBodyScoreParityRoles

    liveQuotientLabel :
      String

    compiledProductLabel :
      String

    inverseValidityLabel :
      String

    residualSeamLabel :
      String

    jPlusOneLabel :
      String

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    clinicalAuthority :
      Bool

    clinicalAuthorityIsFalse :
      clinicalAuthority ≡ false

    authorityBundle :
      Authority.AuthorityNonPromotionBundle

    clinicalAuthorityBundleIsFalse :
      Authority.authorityFlag Authority.clinicalAuthority authorityBundle ≡ false

    empiricalAuthorityBundleIsFalse :
      Authority.authorityFlag Authority.empiricalAuthority authorityBundle ≡ false

open BodyScoreParityCompiledInverseAdapter public

bodyScoreParityAuthorityBundle : Authority.AuthorityNonPromotionBundle
bodyScoreParityAuthorityBundle =
  Authority.mkClosedAuthorityNonPromotionBundle
    "body-score parity/compiled-inverse adapter: candidate-only"

canonicalBodyScoreParityCompiledInverseAdapter :
  BodyScoreParityCompiledInverseAdapter
canonicalBodyScoreParityCompiledInverseAdapter =
  mkBodyScoreParityCompiledInverseAdapter
    Parity.canonicalEvenParityLaneReceipt
    refl
    Parity.canonicalOddParityLaneReceipt
    refl
    Compiled.canonicalCompiledInverseGateLedger
    refl
    RSAPlusOne.rsaPlusOneIdentitySectionReceipt
    canonicalBodyScoreParityRoles
    refl
    "self / world: live separated relation"
    "self * world^-1_j: compiled chart-local relation"
    "world_j * world^-1_j reduces to identity only inside a valid chart"
    "world_now * world^-1_old fails to glue to identity"
    "j+1: candidate carry into a new chart, not a treatment prescription"
    true
    refl
    false
    refl
    bodyScoreParityAuthorityBundle
    (Authority.authorityFlagIsFalse Authority.clinicalAuthority bodyScoreParityAuthorityBundle)
    (Authority.authorityFlagIsFalse Authority.empiricalAuthority bodyScoreParityAuthorityBundle)

canonicalEvenLaneRemainsSeparated :
  Parity.receiptClass
    (evenLaneReceipt canonicalBodyScoreParityCompiledInverseAdapter)
  ≡
  Parity.evenSeparatedLane
canonicalEvenLaneRemainsSeparated =
  Parity.canonicalEvenReceiptClassIsSeparated

canonicalOddLaneIsCompiledCollapsed :
  Parity.receiptClass
    (oddLaneReceipt canonicalBodyScoreParityCompiledInverseAdapter)
  ≡
  Parity.oddCollapsedLane
canonicalOddLaneIsCompiledCollapsed =
  Parity.canonicalOddReceiptClassIsCollapsed

canonicalBodyScoreParityHasNoClinicalAuthority :
  clinicalAuthority canonicalBodyScoreParityCompiledInverseAdapter ≡ false
canonicalBodyScoreParityHasNoClinicalAuthority =
  clinicalAuthorityIsFalse canonicalBodyScoreParityCompiledInverseAdapter
