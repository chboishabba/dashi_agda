{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13Eq119SourceRouteProvenanceExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119) SOURCE-ROUTE PROVENANCE AUDIT
--
-- The compact route and the radius-native route produce the same downstream
-- Eq. (119) consumer shape but expose different ownership boundaries.
--
-- Compact route:
--   selected background
--   + scalar embedding
--   + Federbush family
--   + one dependent mixed cut/defect weld.
--
-- Radius-native route:
--   selected-background/native-radius same-object fibre
--   + scalar embedding
--   + Federbush family
--   + source-independent standard SU(2) operator representation
--   + selected-chart recognition.
--
-- The second route is not a proof that the radius exists.  Its value is that
-- the physical smallness receipt already used by Path13 coercivity is reused by
-- Eq. (119), while standard representation facts and selected chart authority
-- remain separately attributed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Path13ReducedTwoCarrierSourceFamilyExact as Source
import DASHI.Physics.YangMills.BalabanPath13SelectedBackgroundRadiusFibreExact as Fibre
import DASHI.Physics.YangMills.BalabanPath13RadiusOperatorDefectRouteExact as RadiusOperator
import DASHI.Physics.YangMills.BalabanPath13RadiusPrincipalImageRouteExact as RadiusPrincipal

record Path13Eq119SourceRouteStatus : Set where
  field
    compactFourInputAdapterClosed : Bool
    radiusNativeAdapterClosed : Bool
    selectedBackgroundRadiusSameObjectOwnershipClosed : Bool
    nativeRadiusToOperatorDefectCompilerClosed : Bool
    nativeRadiusRelative74TelescopeClosed : Bool
    radiusPrincipalImageCompilerClosed : Bool

    selectedPath13BackgroundConstructed : Bool
    selectedPath13NativeRadiusConstructed : Bool
    standardRationalSU2OperatorRepresentationConstructed : Bool
    selectedRadiusCutRecognitionConstructed : Bool
    rationalRealRingEmbeddingConstructed : Bool
    federbushConventionFamilyConstructed : Bool
    physicalEq119ClosedByEitherRoute : Bool

    compactFourInputAdapterClosedIsTrue : compactFourInputAdapterClosed ≡ true
    radiusNativeAdapterClosedIsTrue : radiusNativeAdapterClosed ≡ true
    selectedBackgroundRadiusSameObjectOwnershipClosedIsTrue :
      selectedBackgroundRadiusSameObjectOwnershipClosed ≡ true
    nativeRadiusToOperatorDefectCompilerClosedIsTrue :
      nativeRadiusToOperatorDefectCompilerClosed ≡ true
    nativeRadiusRelative74TelescopeClosedIsTrue :
      nativeRadiusRelative74TelescopeClosed ≡ true
    radiusPrincipalImageCompilerClosedIsTrue :
      radiusPrincipalImageCompilerClosed ≡ true

    selectedPath13BackgroundConstructedIsFalse : selectedPath13BackgroundConstructed ≡ false
    selectedPath13NativeRadiusConstructedIsFalse : selectedPath13NativeRadiusConstructed ≡ false
    standardRationalSU2OperatorRepresentationConstructedIsFalse :
      standardRationalSU2OperatorRepresentationConstructed ≡ false
    selectedRadiusCutRecognitionConstructedIsFalse :
      selectedRadiusCutRecognitionConstructed ≡ false
    rationalRealRingEmbeddingConstructedIsFalse : rationalRealRingEmbeddingConstructed ≡ false
    federbushConventionFamilyConstructedIsFalse : federbushConventionFamilyConstructed ≡ false
    physicalEq119ClosedByEitherRouteIsFalse : physicalEq119ClosedByEitherRoute ≡ false

open Path13Eq119SourceRouteStatus public

canonicalPath13Eq119SourceRouteStatus : Path13Eq119SourceRouteStatus
canonicalPath13Eq119SourceRouteStatus = record
  { compactFourInputAdapterClosed = true
  ; radiusNativeAdapterClosed = true
  ; selectedBackgroundRadiusSameObjectOwnershipClosed = true
  ; nativeRadiusToOperatorDefectCompilerClosed = true
  ; nativeRadiusRelative74TelescopeClosed = true
  ; radiusPrincipalImageCompilerClosed = true
  ; selectedPath13BackgroundConstructed = false
  ; selectedPath13NativeRadiusConstructed = false
  ; standardRationalSU2OperatorRepresentationConstructed = false
  ; selectedRadiusCutRecognitionConstructed = false
  ; rationalRealRingEmbeddingConstructed = false
  ; federbushConventionFamilyConstructed = false
  ; physicalEq119ClosedByEitherRoute = false
  ; compactFourInputAdapterClosedIsTrue = refl
  ; radiusNativeAdapterClosedIsTrue = refl
  ; selectedBackgroundRadiusSameObjectOwnershipClosedIsTrue = refl
  ; nativeRadiusToOperatorDefectCompilerClosedIsTrue = refl
  ; nativeRadiusRelative74TelescopeClosedIsTrue = refl
  ; radiusPrincipalImageCompilerClosedIsTrue = refl
  ; selectedPath13BackgroundConstructedIsFalse = refl
  ; selectedPath13NativeRadiusConstructedIsFalse = refl
  ; standardRationalSU2OperatorRepresentationConstructedIsFalse = refl
  ; selectedRadiusCutRecognitionConstructedIsFalse = refl
  ; rationalRealRingEmbeddingConstructedIsFalse = refl
  ; federbushConventionFamilyConstructedIsFalse = refl
  ; physicalEq119ClosedByEitherRouteIsFalse = refl
  }

-- Same-object ownership is closed, existence is not.
ownershipDoesNotConstructRadius :
  selectedBackgroundRadiusSameObjectOwnershipClosed canonicalPath13Eq119SourceRouteStatus ≡ true
ownershipDoesNotConstructRadius = refl

radiusStillUninhabited :
  selectedPath13NativeRadiusConstructed canonicalPath13Eq119SourceRouteStatus ≡ false
radiusStillUninhabited = refl

-- Standard-imported representation authority is not relabelled as a constructed
-- Agda inhabitant merely because R171 now owns the full representation shape.
standardRepresentationStillImported :
  standardRationalSU2OperatorRepresentationConstructed canonicalPath13Eq119SourceRouteStatus ≡ false
standardRepresentationStillImported = refl

cmp98Path13Eq119SourceRouteProvenanceLevel : ProofLevel
cmp98Path13Eq119SourceRouteProvenanceLevel = machineChecked

selectedBackgroundRadiusFibreLevel : ProofLevel
selectedBackgroundRadiusFibreLevel = Fibre.cmp98Path13SelectedBackgroundRadiusFibreLevel

radiusNativeSourceAdapterLevel : ProofLevel
radiusNativeSourceAdapterLevel = Source.cmp98Path13RadiusNativeSourceAdapterLevel

radiusNativeOperatorCompilerLevel : ProofLevel
radiusNativeOperatorCompilerLevel = RadiusOperator.path13NativeRadiusToOperatorDefectLevel

radiusNativePrincipalImageCompilerLevel : ProofLevel
radiusNativePrincipalImageCompilerLevel = RadiusPrincipal.cmp98Path13RadiusPrincipalImageCompilerLevel
