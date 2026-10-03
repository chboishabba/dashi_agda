{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119ReflectionSupportCarrierMaxCut20261003Exact where

------------------------------------------------------------------------
-- CMP119 REFLECTION-SUPPORT CARRIER MAX-CUT
--
-- The existing Closure.YMEffectiveActionSupportInterface is useful for the
-- spatial-vs-temporal transfer/KP lane, but its `Link` contains only
--
--   linkId : String
--   kind   : temporal | spatial
--
-- and its `PolymerSupport` is only `AllSpatialLinks supportLinks`.
-- Therefore that carrier does not contain a Euclidean-time coordinate and
-- cannot, by itself, state the OS predicates
--
--   support subset Lambda_+
--   support subset Lambda_-
--   support crosses the selected reflection plane.
--
-- The repository already has a coordinate-bearing finite physical carrier:
-- `PeriodicTracePolymer L`, whose support is a literal connected list of
-- `periodicTorus4Definition L` sites.  This is the least-inflated existing
-- carrier on which the missing B/E/R reflection-side audit can be stated.
--
-- This module records that representation correction.  It does NOT infer an
-- OS certificate from spatial support, analyticity, exponential localization,
-- or KP membership.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Weak
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanPeriodicTracePolymerExact as Trace
import DASHI.Physics.YangMills.BalabanCMP119ReflectionMaxCut20261002Exact as RP

------------------------------------------------------------------------
-- The weak support interface has no coordinate projection to audit.
------------------------------------------------------------------------

weakSupportCarriesOnlyLinkKind : Bool
weakSupportCarriesOnlyLinkKind = true

weakPolymerSupportIsSpatialityPredicate :
  Weak.PolymerSupport ≡ Weak.AllSpatialLinks ∘ Weak.supportLinks
weakPolymerSupportIsSpatialityPredicate = refl

-- This is a status firewall, not a metatheoretic impossibility proof about all
-- conceivable encodings into String identifiers.  No source theorem currently
-- identifies those opaque identifiers with literal Euclidean-time coordinates.
weakSupportHasSourceBackedOSTimeCoordinate : Bool
weakSupportHasSourceBackedOSTimeCoordinate = false

weakSupportHasSourceBackedOSTimeCoordinateIsFalse :
  weakSupportHasSourceBackedOSTimeCoordinate ≡ false
weakSupportHasSourceBackedOSTimeCoordinateIsFalse = refl

------------------------------------------------------------------------
-- Existing coordinate-bearing donor.
------------------------------------------------------------------------

LiteralReflectionSupport : Nat → Set
LiteralReflectionSupport L = Torus.periodicTorus4Definition L

LiteralReflectionPolymer : Nat → Set
LiteralReflectionPolymer = Trace.PeriodicTracePolymer

literalReflectionPolymerSupport :
  ∀ {L} → LiteralReflectionPolymer L →
  Agda.Builtin.List.List (LiteralReflectionSupport L)
literalReflectionPolymerSupport = Trace.tracePolymerSupport

literalReflectionPolymerSupportConnected :
  ∀ {L} (polymer : LiteralReflectionPolymer L) →
  Trace.ConnectedTrace (literalReflectionPolymerSupport polymer)
literalReflectionPolymerSupportConnected = Trace.tracePolymerSupportConnected

coordinateBearingTraceCarrierLevel : ProofLevel
coordinateBearingTraceCarrierLevel = Trace.periodicTracePolymerCarrierLevel

coordinateBearingTraceConnectednessLevel : ProofLevel
coordinateBearingTraceConnectednessLevel = Trace.periodicTracePolymerConnectednessLevel

------------------------------------------------------------------------
-- Exact source-facing same-object dictionaries now required sector by sector.
------------------------------------------------------------------------

record CMP119ReflectionSupportDictionary
    (SourcePolymer : Set) (L : Nat) : Set₁ where
  field
    toLiteralTrace : SourcePolymer → LiteralReflectionPolymer L

    -- This is the important physical same-object field: the literal trace must
    -- be the support of the SAME localized source term, not merely a convenient
    -- connected polymer with similar size.
    SameSourceSupport : SourcePolymer → LiteralReflectionPolymer L → Set
    sameSourceSupport : ∀ sourcePolymer →
      SameSourceSupport sourcePolymer (toLiteralTrace sourcePolymer)

open CMP119ReflectionSupportDictionary public

record CMP119SectorReflectionGeometry
    (SourcePolymer : Set) (L : Nat)
    (dictionary : CMP119ReflectionSupportDictionary SourcePolymer L) : Set₁ where
  field
    PositiveHalf : LiteralReflectionSupport L → Set
    NegativeHalf : LiteralReflectionSupport L → Set
    ReflectionBoundary : LiteralReflectionSupport L → Set

    SupportEntirelyPositive : LiteralReflectionPolymer L → Set
    SupportEntirelyNegative : LiteralReflectionPolymer L → Set
    SupportCrossesPlane : LiteralReflectionPolymer L → Set

    classifySourcePolymer : ∀ sourcePolymer →
      SupportEntirelyPositive (toLiteralTrace dictionary sourcePolymer)
      ⊎ SupportEntirelyNegative (toLiteralTrace dictionary sourcePolymer)
      ⊎ SupportCrossesPlane (toLiteralTrace dictionary sourcePolymer)

open CMP119SectorReflectionGeometry public

------------------------------------------------------------------------
-- Sector-specific frontier.
------------------------------------------------------------------------

data ReflectionSupportLeaf : Set where
  boundarySourceToLiteralTrace
  regularESourceToLiteralTrace
  rOperationSourceToLiteralTrace
  literalEvenTimeSiteHalfClassifier
  boundaryCrossingKernelAudit
  regularECrossingKernelAudit
  rOperationCrossingKernelAudit : ReflectionSupportLeaf

-- The source-backed analytic/localization theorem for B remains useful, but it
-- supplies none of the seven reflection-support leaves above.
boundaryAnalyticLocalizationIsNotReflectionGeometry : Bool
boundaryAnalyticLocalizationIsNotReflectionGeometry = true

boundaryAnalyticLocalizationIsNotReflectionGeometryIsTrue :
  boundaryAnalyticLocalizationIsNotReflectionGeometry ≡ true
boundaryAnalyticLocalizationIsNotReflectionGeometryIsTrue = refl

-- Vacuum remains outside this support audit after its constant-source recut.
vacuumStillRemovedFromCrossPlaneCut :
  RP.reflectionAuditStatus RP.vacuumV ≡ RP.reflectedHalfClosed
vacuumStillRemovedFromCrossPlaneCut = RP.vacuumRemovedFromCrossPlaneCut

reflectionSupportCarrierMaxCutLevel : ProofLevel
reflectionSupportCarrierMaxCutLevel = machineChecked

-- These are the actual next physical representation/geometric theorems.
boundarySourceToLiteralTraceLevel : ProofLevel
boundarySourceToLiteralTraceLevel = conditional

regularESourceToLiteralTraceLevel : ProofLevel
regularESourceToLiteralTraceLevel = conditional

rOperationSourceToLiteralTraceLevel : ProofLevel
rOperationSourceToLiteralTraceLevel = conditional

literalEvenTimeSiteHalfClassifierLevel : ProofLevel
literalEvenTimeSiteHalfClassifierLevel = conditional

boundaryCrossingKernelAuditLevel : ProofLevel
boundaryCrossingKernelAuditLevel = conditional

regularECrossingKernelAuditLevel : ProofLevel
regularECrossingKernelAuditLevel = conditional

rOperationCrossingKernelAuditLevel : ProofLevel
rOperationCrossingKernelAuditLevel = conditional
