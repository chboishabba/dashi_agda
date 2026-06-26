module DASHI.Crypto.RSACRTChamberCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Crypto.RSABTResidueBraidHypervoxelBoundary as BT
import DASHI.Physics.Closure.BTBoundaryCrossSectionRows as BTBoundaryRows

------------------------------------------------------------------------
-- RSA CRT / residue chamber core.
--
-- The core stays candidate-only and links residue-pair bookkeeping to the
-- existing BT / residue / braid / hypervoxel boundary surface by storing
-- explicit equality fields.  The soundness theorem is deliberately modest:
-- it only projects the stored equalities, so it remains provable without
-- introducing arithmetic mod-law infrastructure here.

listCount : {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

canonicalResidueChamberCoreLabel : String
canonicalResidueChamberCoreLabel =
  "RSA CRT residue chamber core"

canonicalResiduePairConstraintLabel : String
canonicalResiduePairConstraintLabel =
  "RSA residue-pair constraint linked to the canonical BT residue-braid hypervoxel boundary"

canonicalResidueChamberScan : List String
canonicalResidueChamberScan =
  "residue-pair rows linked to the canonical BT boundary"
  ∷ "CRT fingerprint candidate row reused from the BT residue-braid hypervoxel boundary"
  ∷ "candidate-only equality and projection proofs"
  ∷ []

canonicalResidueChamberPairLabels : List String
canonicalResidueChamberPairLabels =
  "p2 residue pair"
  ∷ "p3 residue pair"
  ∷ "p7 residue pair"
  ∷ []

canonicalResidueChamberPairCount : Nat
canonicalResidueChamberPairCount =
  listCount canonicalResidueChamberPairLabels

data RSACRTChamberCoreStatus : Set where
  rsaCrtChamberCoreRecordedNoPromotion :
    RSACRTChamberCoreStatus

record RSACRTResiduePairRow : Set where
  field
    residuePairLabel :
      String

    leftResidueLabel :
      String

    rightResidueLabel :
      String

    residuePairConstraintLabel :
      String

    residuePairConstraintLabelIsCanonical :
      residuePairConstraintLabel ≡ canonicalResiduePairConstraintLabel

    residuePairBoundarySurface :
      BT.RSABTResidueBraidHypervoxelBoundarySurface

    residuePairBoundarySurfaceIsCanonical :
      residuePairBoundarySurface
      ≡
      BT.canonicalRSABTResidueBraidHypervoxelBoundarySurface

    residuePairBoundaryRows :
      List BTBoundaryRows.BTBoundaryCrossSectionRow

    residuePairBoundaryRowsAreCanonical :
      residuePairBoundaryRows ≡ BTBoundaryRows.canonicalBTBoundaryCrossSectionRows

    residuePairBoundaryRowCount :
      Nat

    residuePairBoundaryRowCountIsCanonical :
      residuePairBoundaryRowCount
      ≡
      BTBoundaryRows.length BTBoundaryRows.canonicalBTBoundaryCrossSectionRows

    residuePairCandidateOnly :
      Bool

    residuePairCandidateOnlyIsTrue :
      residuePairCandidateOnly ≡ true

    residuePairPromoted :
      Bool

    residuePairPromotedIsFalse :
      residuePairPromoted ≡ false

open RSACRTResiduePairRow public

canonicalRSACRTResiduePairRow :
  String →
  String →
  String →
  RSACRTResiduePairRow
canonicalRSACRTResiduePairRow label left right =
  record
    { residuePairLabel =
        label
    ; leftResidueLabel =
        left
    ; rightResidueLabel =
        right
    ; residuePairConstraintLabel =
        canonicalResiduePairConstraintLabel
    ; residuePairConstraintLabelIsCanonical =
        refl
    ; residuePairBoundarySurface =
        BT.canonicalRSABTResidueBraidHypervoxelBoundarySurface
    ; residuePairBoundarySurfaceIsCanonical =
        refl
    ; residuePairBoundaryRows =
        BTBoundaryRows.canonicalBTBoundaryCrossSectionRows
    ; residuePairBoundaryRowsAreCanonical =
        refl
    ; residuePairBoundaryRowCount =
        BTBoundaryRows.length
          BTBoundaryRows.canonicalBTBoundaryCrossSectionRows
    ; residuePairBoundaryRowCountIsCanonical =
        refl
    ; residuePairCandidateOnly =
        true
    ; residuePairCandidateOnlyIsTrue =
        refl
    ; residuePairPromoted =
        false
    ; residuePairPromotedIsFalse =
        refl
    }

canonicalRSACRTResiduePairRowP2 :
  RSACRTResiduePairRow
canonicalRSACRTResiduePairRowP2 =
  canonicalRSACRTResiduePairRow
    "p2 residue pair"
    "p2 left residue lane"
    "p2 right residue lane"

canonicalRSACRTResiduePairRowP3 :
  RSACRTResiduePairRow
canonicalRSACRTResiduePairRowP3 =
  canonicalRSACRTResiduePairRow
    "p3 residue pair"
    "p3 left residue lane"
    "p3 right residue lane"

canonicalRSACRTResiduePairRowP7 :
  RSACRTResiduePairRow
canonicalRSACRTResiduePairRowP7 =
  canonicalRSACRTResiduePairRow
    "p7 residue pair"
    "p7 left residue lane"
    "p7 right residue lane"

canonicalRSACRTResiduePairRows :
  List RSACRTResiduePairRow
canonicalRSACRTResiduePairRows =
  canonicalRSACRTResiduePairRowP2
  ∷ canonicalRSACRTResiduePairRowP3
  ∷ canonicalRSACRTResiduePairRowP7
  ∷ []

canonicalRSACRTResiduePairRowCount :
  Nat
canonicalRSACRTResiduePairRowCount =
  listCount canonicalRSACRTResiduePairRows

record CRTFingerprintCandidateRow : Set where
  field
    crtFingerprintLabel :
      String

    crtFingerprintText :
      String

    crtFingerprintTextIsCanonical :
      crtFingerprintText ≡ BT.canonicalCRTBraidFingerprint

    crtFingerprintBoundarySurface :
      BT.RSABTResidueBraidHypervoxelBoundarySurface

    crtFingerprintBoundarySurfaceIsCanonical :
      crtFingerprintBoundarySurface
      ≡
      BT.canonicalRSABTResidueBraidHypervoxelBoundarySurface

    crtFingerprintBoundaryRows :
      List BTBoundaryRows.BTBoundaryCrossSectionRow

    crtFingerprintBoundaryRowsAreCanonical :
      crtFingerprintBoundaryRows
      ≡
      BTBoundaryRows.canonicalBTBoundaryCrossSectionRows

    crtFingerprintCandidateOnly :
      Bool

    crtFingerprintCandidateOnlyIsTrue :
      crtFingerprintCandidateOnly ≡ true

    crtFingerprintPromoted :
      Bool

    crtFingerprintPromotedIsFalse :
      crtFingerprintPromoted ≡ false

open CRTFingerprintCandidateRow public

canonicalCRTFingerprintCandidateRow :
  CRTFingerprintCandidateRow
canonicalCRTFingerprintCandidateRow =
  record
    { crtFingerprintLabel =
        "CRT fingerprint candidate row"
    ; crtFingerprintText =
        BT.canonicalCRTBraidFingerprint
    ; crtFingerprintTextIsCanonical =
        refl
    ; crtFingerprintBoundarySurface =
        BT.canonicalRSABTResidueBraidHypervoxelBoundarySurface
    ; crtFingerprintBoundarySurfaceIsCanonical =
        refl
    ; crtFingerprintBoundaryRows =
        BTBoundaryRows.canonicalBTBoundaryCrossSectionRows
    ; crtFingerprintBoundaryRowsAreCanonical =
        refl
    ; crtFingerprintCandidateOnly =
        true
    ; crtFingerprintCandidateOnlyIsTrue =
        refl
    ; crtFingerprintPromoted =
        false
    ; crtFingerprintPromotedIsFalse =
        refl
    }

record RSACRTChamberCore : Set where
  field
    status :
      RSACRTChamberCoreStatus

    chamberLabel :
      String

    chamberLabelIsCanonical :
      chamberLabel ≡ canonicalResidueChamberCoreLabel

    residueChamberScan :
      List String

    residueChamberScanIsCanonical :
      residueChamberScan ≡ canonicalResidueChamberScan

    residuePairRows :
      List RSACRTResiduePairRow

    residuePairRowsAreCanonical :
      residuePairRows ≡ canonicalRSACRTResiduePairRows

    residuePairRowCount :
      Nat

    residuePairRowCountIsCanonical :
      residuePairRowCount ≡ canonicalRSACRTResiduePairRowCount

    crtFingerprintCandidateRow :
      CRTFingerprintCandidateRow

    crtFingerprintCandidateRowIsCanonical :
      crtFingerprintCandidateRow ≡ canonicalCRTFingerprintCandidateRow

    linkedBoundarySurface :
      BT.RSABTResidueBraidHypervoxelBoundarySurface

    linkedBoundarySurfaceIsCanonical :
      linkedBoundarySurface
      ≡
      BT.canonicalRSABTResidueBraidHypervoxelBoundarySurface

    linkedBoundaryRows :
      List BTBoundaryRows.BTBoundaryCrossSectionRow

    linkedBoundaryRowsAreCanonical :
      linkedBoundaryRows
      ≡
      BTBoundaryRows.canonicalBTBoundaryCrossSectionRows

    linkedBoundaryRowCount :
      Nat

    linkedBoundaryRowCountIsCanonical :
      linkedBoundaryRowCount
      ≡
      BTBoundaryRows.length BTBoundaryRows.canonicalBTBoundaryCrossSectionRows

    chamberCandidateOnly :
      Bool

    chamberCandidateOnlyIsTrue :
      chamberCandidateOnly ≡ true

    chamberPromoted :
      Bool

    chamberPromotedIsFalse :
      chamberPromoted ≡ false

open RSACRTChamberCore public

canonicalRSACRTChamberCore :
  RSACRTChamberCore
canonicalRSACRTChamberCore =
  record
    { status =
        rsaCrtChamberCoreRecordedNoPromotion
    ; chamberLabel =
        canonicalResidueChamberCoreLabel
    ; chamberLabelIsCanonical =
        refl
    ; residueChamberScan =
        canonicalResidueChamberScan
    ; residueChamberScanIsCanonical =
        refl
    ; residuePairRows =
        canonicalRSACRTResiduePairRows
    ; residuePairRowsAreCanonical =
        refl
    ; residuePairRowCount =
        canonicalRSACRTResiduePairRowCount
    ; residuePairRowCountIsCanonical =
        refl
    ; crtFingerprintCandidateRow =
        canonicalCRTFingerprintCandidateRow
    ; crtFingerprintCandidateRowIsCanonical =
        refl
    ; linkedBoundarySurface =
        BT.canonicalRSABTResidueBraidHypervoxelBoundarySurface
    ; linkedBoundarySurfaceIsCanonical =
        refl
    ; linkedBoundaryRows =
        BTBoundaryRows.canonicalBTBoundaryCrossSectionRows
    ; linkedBoundaryRowsAreCanonical =
        refl
    ; linkedBoundaryRowCount =
        BTBoundaryRows.length
          BTBoundaryRows.canonicalBTBoundaryCrossSectionRows
    ; linkedBoundaryRowCountIsCanonical =
        refl
    ; chamberCandidateOnly =
        true
    ; chamberCandidateOnlyIsTrue =
        refl
    ; chamberPromoted =
        false
    ; chamberPromotedIsFalse =
        refl
    }

record RSACRTChamberCoreSoundness (core : RSACRTChamberCore) : Set where
  field
    residuePairRowsSound :
      residuePairRows core ≡ canonicalRSACRTResiduePairRows

    residuePairRowCountSound :
      residuePairRowCount core ≡ canonicalRSACRTResiduePairRowCount

    fingerprintTextSound :
      CRTFingerprintCandidateRow.crtFingerprintText
        (crtFingerprintCandidateRow core)
      ≡
      BT.canonicalCRTBraidFingerprint

    fingerprintBoundarySurfaceSound :
      CRTFingerprintCandidateRow.crtFingerprintBoundarySurface
        (crtFingerprintCandidateRow core)
      ≡
      BT.canonicalRSABTResidueBraidHypervoxelBoundarySurface

    linkedBoundarySurfaceSound :
      linkedBoundarySurface core
      ≡
      BT.canonicalRSABTResidueBraidHypervoxelBoundarySurface

    linkedBoundaryRowsSound :
      linkedBoundaryRows core
      ≡
      BTBoundaryRows.canonicalBTBoundaryCrossSectionRows

    chamberCandidateOnlySound :
      chamberCandidateOnly core ≡ true

    chamberPromotedSound :
      chamberPromoted core ≡ false

residuePairRowsCanonical :
  (core : RSACRTChamberCore) →
  residuePairRows core ≡ canonicalRSACRTResiduePairRows
residuePairRowsCanonical core =
  residuePairRowsAreCanonical core

residuePairRowCountCanonical :
  (core : RSACRTChamberCore) →
  residuePairRowCount core ≡ canonicalRSACRTResiduePairRowCount
residuePairRowCountCanonical core =
  residuePairRowCountIsCanonical core

fingerprintTextCanonical :
  (core : RSACRTChamberCore) →
  CRTFingerprintCandidateRow.crtFingerprintText
    (crtFingerprintCandidateRow core)
  ≡
  BT.canonicalCRTBraidFingerprint
fingerprintTextCanonical core =
  CRTFingerprintCandidateRow.crtFingerprintTextIsCanonical
    (crtFingerprintCandidateRow core)

fingerprintBoundarySurfaceCanonical :
  (core : RSACRTChamberCore) →
  CRTFingerprintCandidateRow.crtFingerprintBoundarySurface
    (crtFingerprintCandidateRow core)
  ≡
  BT.canonicalRSABTResidueBraidHypervoxelBoundarySurface
fingerprintBoundarySurfaceCanonical core =
  CRTFingerprintCandidateRow.crtFingerprintBoundarySurfaceIsCanonical
    (crtFingerprintCandidateRow core)

linkedBoundarySurfaceCanonical :
  (core : RSACRTChamberCore) →
  linkedBoundarySurface core
  ≡
  BT.canonicalRSABTResidueBraidHypervoxelBoundarySurface
linkedBoundarySurfaceCanonical core =
  linkedBoundarySurfaceIsCanonical core

linkedBoundaryRowsCanonical :
  (core : RSACRTChamberCore) →
  linkedBoundaryRows core
  ≡
  BTBoundaryRows.canonicalBTBoundaryCrossSectionRows
linkedBoundaryRowsCanonical core =
  linkedBoundaryRowsAreCanonical core

coreCandidateOnlyIsTrue :
  (core : RSACRTChamberCore) →
  chamberCandidateOnly core ≡ true
coreCandidateOnlyIsTrue core =
  chamberCandidateOnlyIsTrue core

corePromotedIsFalse :
  (core : RSACRTChamberCore) →
  chamberPromoted core ≡ false
corePromotedIsFalse core =
  chamberPromotedIsFalse core

rsaCrtChamberCoreSoundness :
  (core : RSACRTChamberCore) →
  RSACRTChamberCoreSoundness core
rsaCrtChamberCoreSoundness core =
  record
    { residuePairRowsSound =
        residuePairRowsCanonical core
    ; residuePairRowCountSound =
        residuePairRowCountCanonical core
    ; fingerprintTextSound =
        fingerprintTextCanonical core
    ; fingerprintBoundarySurfaceSound =
        fingerprintBoundarySurfaceCanonical core
    ; linkedBoundarySurfaceSound =
        linkedBoundarySurfaceCanonical core
    ; linkedBoundaryRowsSound =
        linkedBoundaryRowsCanonical core
    ; chamberCandidateOnlySound =
        coreCandidateOnlyIsTrue core
    ; chamberPromotedSound =
        corePromotedIsFalse core
    }

canonicalRSACRTChamberCoreSoundness :
  RSACRTChamberCoreSoundness canonicalRSACRTChamberCore
canonicalRSACRTChamberCoreSoundness =
  rsaCrtChamberCoreSoundness canonicalRSACRTChamberCore
