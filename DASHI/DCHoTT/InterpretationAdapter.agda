module DASHI.DCHoTT.InterpretationAdapter where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Base using (zero)

import DASHI.Geometry.DCHoTTBridgeObligationIndex as B0
import DASHI.Geometry.DCHoTTImportShim as DCHoTT
import DASHI.Geometry.FlatFormalDiskHolonomySurface as B02
import DASHI.Geometry.GStructureLeviCivitaBindingSurface as B03
import DASHI.Geometry.ProObjectSemantics as Sem
import DASHI.Geometry.TransportSmoothFormalDiskSurface as TS

------------------------------------------------------------------------
-- DCHoTT-facing interpretation adapter.
--
-- This namespace is a bridge surface only.  It re-exports receipt-grade
-- evidence already checked in the geometry lane, points it at the real
-- DCHoTT-Agda import shim, and records the remaining incompatibilities.  It
-- does not port DCHoTT-Agda, does not construct a DCHoTT formal D-space from
-- every DASHI carrier, and does not promote B0 / Levi-Civita.

data DCHoTTAdapterStatus : Set where
  interpretationBridgeOnlyNoPromotion :
    DCHoTTAdapterStatus

data DCHoTTAdapterOpenObligation : Set where
  missingCarrierToDCHoTTFormalDSpace :
    DCHoTTAdapterOpenObligation

  missingDCHoTTFormalDiskEquivalence :
    DCHoTTAdapterOpenObligation

  missingImportedImReflection :
    DCHoTTAdapterOpenObligation

  missingDCHoTTFlatFormalDiskTrivialisation :
    DCHoTTAdapterOpenObligation

  missingDCHoTTGStructureBinding :
    DCHoTTAdapterOpenObligation

  missingTorsionFreeLeviCivitaImport :
    DCHoTTAdapterOpenObligation

canonicalDCHoTTAdapterOpenObligations :
  List DCHoTTAdapterOpenObligation
canonicalDCHoTTAdapterOpenObligations =
  missingCarrierToDCHoTTFormalDSpace
  ∷ missingDCHoTTFormalDiskEquivalence
  ∷ missingImportedImReflection
  ∷ missingDCHoTTFlatFormalDiskTrivialisation
  ∷ missingDCHoTTGStructureBinding
  ∷ missingTorsionFreeLeviCivitaImport
  ∷ []

record DCHoTTB01InterpretationAdapter
  (P : B0.ProObjectCarrier) :
  Setω where
  field
    status :
      DCHoTTAdapterStatus

    dchottImportShim :
      DCHoTT.DCHoTTImportShimReceipt

    b01ObligationIndex :
      B0.B01ImFormalDiskSocket P

    proObjectSemantics :
      Sem.ConstructedProObjectLimitSurface P

    depthBallRestriction :
      TS.CanonicalBallRestrictionSurface P

    importedImModalSurface :
      TS.Depth01ImportedImModalEqualitySurface P

    dashiDiskToDCHoTTDepthZeroDisk :
      (x : B0.ProObjectPoint P) →
      B0.FormalDisk x →
      DCHoTT.DCHoTTFormalDisk
        (B0.ProObjectCarrier.depthCarrier P zero)
        (B0.Im x)

    dashiDiskToDCHoTTDepthZeroDisk-v :
      (x : B0.ProObjectPoint P) →
      (disk : B0.FormalDisk x) →
      dashiDiskToDCHoTTDepthZeroDisk x disk
      ≡
      TS.dashiFormalDiskToDCHoTTDepthZeroFormalDisk x disk

    comparisonSocket :
      (x : B0.ProObjectPoint P) →
      TS.DASHIDCHoTTFormalDiskComparisonSocket x

    depthZeroImpliesImportedImModal :
      (x y : B0.ProObjectPoint P) →
      B0.DepthZeroAgreement x y →
      DCHoTT.DCHoTTPathOver
        (DCHoTT.DCHoTTInfinitesimalUnit (B0.Im x))
        (DCHoTT.DCHoTTInfinitesimalUnit (B0.Im y))

    depthOneImpliesImportedImModal :
      (x y : B0.ProObjectPoint P) →
      B0.DepthOneAgreement x y →
      DCHoTT.DCHoTTPathOver
        (DCHoTT.DCHoTTInfinitesimalUnit (B0.Im x))
        (DCHoTT.DCHoTTInfinitesimalUnit (B0.Im y))

    openObligations :
      List DCHoTTAdapterOpenObligation

    openObligationsAreCanonical :
      openObligations
      ≡
      canonicalDCHoTTAdapterOpenObligations

    actualDCHoTTFormalSpaceConstructed :
      Bool

    actualDCHoTTFormalSpaceConstructedIsFalse :
      actualDCHoTTFormalSpaceConstructed ≡ false

    bridgeBoundary :
      List String

open DCHoTTB01InterpretationAdapter public

canonicalDCHoTTB01InterpretationAdapter :
  (P : B0.ProObjectCarrier) →
  DCHoTTB01InterpretationAdapter P
canonicalDCHoTTB01InterpretationAdapter P =
  record
    { status =
        interpretationBridgeOnlyNoPromotion
    ; dchottImportShim =
        DCHoTT.canonicalDCHoTTImportShimReceipt
    ; b01ObligationIndex =
        B0.canonicalB01ImFormalDiskSocket P
    ; proObjectSemantics =
        Sem.canonicalConstructedProObjectLimitSurface P
    ; depthBallRestriction =
        TS.canonicalBallRestrictionSurface P
    ; importedImModalSurface =
        TS.canonicalDepth01ImportedImModalEqualitySurface P
    ; dashiDiskToDCHoTTDepthZeroDisk =
        TS.dashiFormalDiskToDCHoTTDepthZeroFormalDisk
    ; dashiDiskToDCHoTTDepthZeroDisk-v =
        λ _ _ →
          refl
    ; comparisonSocket =
        TS.canonicalDASHIDCHoTTFormalDiskComparisonSocket
    ; depthZeroImpliesImportedImModal =
        TS.dashiDepthZeroAgreementToImportedImModalEquality
    ; depthOneImpliesImportedImModal =
        TS.dashiDepthOneAgreementToImportedImModalEquality
    ; openObligations =
        canonicalDCHoTTAdapterOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; actualDCHoTTFormalSpaceConstructed =
        false
    ; actualDCHoTTFormalSpaceConstructedIsFalse =
        refl
    ; bridgeBoundary =
        "reuses checked DCHoTTImportShim, B01ImFormalDiskSocket, ProObjectSemantics, and TransportSmoothFormalDiskSurface evidence"
        ∷ "DASHI formal disks are forwarded only to DCHoTT formal disks over the depth-zero carrier via the existing checked adapter"
        ∷ "reverse lift is available only when ImportedDiskReverseLiftData supplies the explicit compatible DASHI point"
        ∷ "no imported Im-reflection theorem, no full DCHoTT formal D-space equivalence, and no B0 promotion receipt are constructed"
        ∷ []
    }

record DCHoTTB02B03ReceiptAdapter
  (P : B0.ProObjectCarrier)
  (projection : B0.ProLimitProjectionSurface P) :
  Setω where
  field
    status :
      DCHoTTAdapterStatus

    b02FlatFormalDiskReceipt :
      B02.FlatFormalDiskHolonomyReceiptSurface P

    b03FrameMetricSignatureTower :
      B03.ConstructibleFrameMetricSignatureTowerSurface P projection

    b03BindingReceipt :
      B03.CanonicalGStructureLeviCivitaBindingReceipt

    dchottGStructureImported :
      Bool

    dchottGStructureImportedIsFalse :
      dchottGStructureImported ≡ false

    torsionFreeLeviCivitaImported :
      Bool

    torsionFreeLeviCivitaImportedIsFalse :
      torsionFreeLeviCivitaImported ≡ false

    noB0PromotionReceiptConstructed :
      Bool

    noB0PromotionReceiptConstructedIsTrue :
      noB0PromotionReceiptConstructed ≡ true

    incompatibilityDocumentedInFile :
      String

    incompatibilityDocumentedInFile-v :
      incompatibilityDocumentedInFile
      ≡
      "local DCHoTT clone exposes Im/FormalDisk/Manifolds/G-structure surfaces but no importable torsion-free Levi-Civita theorem or DASHI-to-DCHoTT formal-D-space equivalence"

open DCHoTTB02B03ReceiptAdapter public

canonicalDCHoTTB02B03ReceiptAdapter :
  (P : B0.ProObjectCarrier) →
  (projection : B0.ProLimitProjectionSurface P) →
  DCHoTTB02B03ReceiptAdapter P projection
canonicalDCHoTTB02B03ReceiptAdapter P projection =
  record
    { status =
        interpretationBridgeOnlyNoPromotion
    ; b02FlatFormalDiskReceipt =
        B02.canonicalB02FlatFormalDiskHolonomyReceiptSurface P
    ; b03FrameMetricSignatureTower =
        B03.canonicalConstructibleFrameMetricSignatureTowerSurface P projection
    ; b03BindingReceipt =
        B03.canonicalGStructureLeviCivitaBindingReceipt
    ; dchottGStructureImported =
        false
    ; dchottGStructureImportedIsFalse =
        refl
    ; torsionFreeLeviCivitaImported =
        false
    ; torsionFreeLeviCivitaImportedIsFalse =
        refl
    ; noB0PromotionReceiptConstructed =
        true
    ; noB0PromotionReceiptConstructedIsTrue =
        refl
    ; incompatibilityDocumentedInFile =
        "local DCHoTT clone exposes Im/FormalDisk/Manifolds/G-structure surfaces but no importable torsion-free Levi-Civita theorem or DASHI-to-DCHoTT formal-D-space equivalence"
    ; incompatibilityDocumentedInFile-v =
        refl
    }

record DCHoTTInterpretationAdapterIndex : Setω where
  field
    dependencyShim :
      DCHoTT.DCHoTTImportShimReceipt

    bridgeObligationIndex :
      B0.DCHoTTBridgeObligationIndex

    adapterStatus :
      DCHoTTAdapterStatus

    openObligations :
      List DCHoTTAdapterOpenObligation

    openObligationsAreCanonical :
      openObligations
      ≡
      canonicalDCHoTTAdapterOpenObligations

    noFullRepoPortClaimed :
      Bool

    noFullRepoPortClaimedIsTrue :
      noFullRepoPortClaimed ≡ true

    noPromotionClaimed :
      Bool

    noPromotionClaimedIsTrue :
      noPromotionClaimed ≡ true

    receiptEvidenceSummary :
      List String

open DCHoTTInterpretationAdapterIndex public

canonicalDCHoTTInterpretationAdapterIndex :
  DCHoTTInterpretationAdapterIndex
canonicalDCHoTTInterpretationAdapterIndex =
  record
    { dependencyShim =
        DCHoTT.canonicalDCHoTTImportShimReceipt
    ; bridgeObligationIndex =
        B0.canonicalDCHoTTBridgeObligationIndex
    ; adapterStatus =
        interpretationBridgeOnlyNoPromotion
    ; openObligations =
        canonicalDCHoTTAdapterOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; noFullRepoPortClaimed =
        true
    ; noFullRepoPortClaimedIsTrue =
        refl
    ; noPromotionClaimed =
        true
    ; noPromotionClaimedIsTrue =
        refl
    ; receiptEvidenceSummary =
        "DCHoTTImportShim imports the actual flat DCHoTT-Agda modules Im, FormalDisk, Manifolds, FormalDiskBundle, and G-structure"
        ∷ "DCHoTTB01InterpretationAdapter exposes checked B0.1 pro-object, formal-disk, depth-ball, and imported-Im-path evidence"
        ∷ "DCHoTTB02B03ReceiptAdapter exposes checked B0.2 flat formal-disk receipt and B0.3 frame/metric/G-structure readiness receipts"
        ∷ "remaining DCHoTT equivalence, Im-reflection, flat-trivialisation, G-structure binding, and Levi-Civita imports stay explicit open obligations"
        ∷ []
    }
