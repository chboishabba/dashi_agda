module DASHI.Interop.ITIRRibbonProjectionAuthorityBridgeExact where

open import DASHI.Core.Prelude
import DASHI.Interop.PortableInteractiveGpuProjectionExact as Interactive

------------------------------------------------------------------------
-- ITIR RIBBON / SENSIBLAW PROJECTION-AUTHORITY BRIDGE
--
-- Source alignment:
--   ITIR-suite: Ribbon is read-only projection authority.
--   SensibLaw: Ribbon is an accounting surface whose observable invariants
--              include conservation, ordering, partition coverage and
--              additivity rather than visual-quality equality.
--
-- This owner records those authority boundaries without claiming the current
-- Streamlit/ITIR implementations themselves are Agda-verified.
------------------------------------------------------------------------

data RibbonInvariant : Set where
  conservation : RibbonInvariant
  ordering : RibbonInvariant
  partitionCoverage : RibbonInvariant
  splitMergeAdditivity : RibbonInvariant
  nonNegativity : RibbonInvariant

data RibbonObservation : Set where
  invariantSatisfied : RibbonInvariant → RibbonObservation
  invariantViolated : RibbonInvariant → RibbonObservation

record RibbonProjectionAuthorityBoundary : Set where
  constructor ribbonProjectionAuthorityBoundary
  field
    ribbonIsReadOnlyProjectionAuthority : Bool
    ribbonIsReadOnlyProjectionAuthorityIsTrue :
      ribbonIsReadOnlyProjectionAuthority ≡ true

    ribbonMayMutateCanonicalSemanticIdentity : Bool
    ribbonMayMutateCanonicalSemanticIdentityIsFalse :
      ribbonMayMutateCanonicalSemanticIdentity ≡ false

    diagnosticCreatesCanonicalMutation : Bool
    diagnosticCreatesCanonicalMutationIsFalse :
      diagnosticCreatesCanonicalMutation ≡ false

    threadAnnotationCarriesConservedMassByDefault : Bool
    threadAnnotationCarriesConservedMassByDefaultIsFalse :
      threadAnnotationCarriesConservedMassByDefault ≡ false

    projectionParityRequiresVisualQualityEquality : Bool
    projectionParityRequiresVisualQualityEqualityIsFalse :
      projectionParityRequiresVisualQualityEquality ≡ false

    projectionParityMayBeInvariantIndexed : Bool
    projectionParityMayBeInvariantIndexedIsTrue :
      projectionParityMayBeInvariantIndexed ≡ true

canonicalRibbonProjectionAuthorityBoundary :
  RibbonProjectionAuthorityBoundary
canonicalRibbonProjectionAuthorityBoundary =
  ribbonProjectionAuthorityBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl

------------------------------------------------------------------------
-- Cross-owner weld: Ribbon's projection-only posture is compatible with the
-- generic shell/GPU rule that visual mechanisms do not create semantic
-- authority.
------------------------------------------------------------------------

InteractiveBoundary : Set
InteractiveBoundary = Interactive.PortableInteractiveGpuProjectionBoundary

interactiveBoundaryPaid : InteractiveBoundary
interactiveBoundaryPaid =
  Interactive.canonicalPortableInteractiveGpuProjectionBoundary
