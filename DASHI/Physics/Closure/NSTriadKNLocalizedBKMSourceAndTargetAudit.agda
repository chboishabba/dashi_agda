module DASHI.Physics.Closure.NSTriadKNLocalizedBKMSourceAndTargetAudit where

------------------------------------------------------------------------
-- PROVENANCE AND SCOPE
--
-- Authors: J. Thomas Beale; Tosio Kato; Andrew J. Majda.
-- Title: "Remarks on the breakdown of smooth solutions for the 3-D Euler
-- equations".
-- Venue/year: Communications in Mathematical Physics 94 (1984), 61--66.
-- DOI: 10.1007/BF01212349.
-- Relationship: source of the classical vorticity-integrability continuation
-- paradigm.  The DASHI Navier--Stokes authority requires its own viscous,
-- periodic solution-class bridge.
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "A unified approach to regularity problems for the 3D
-- Navier-Stokes and Euler equations: the use of Kolmogorov's dissipation
-- range".
-- Venue/year: Journal of Mathematical Fluid Mechanics 16 (2014).
-- DOI: 10.1007/s00021-014-0167-4.
-- Relationship: primary candidate for DASHI because it isolates low modes
-- below a solution-dependent dissipation wavenumber Q(t), while viscosity
-- absorbs the modes above Q(t).
--
-- Authors: Alexey Cheskidov; Mimi Dai.
-- Title: "Regularity criteria for the 3D Navier-Stokes and MHD equations".
-- Preprint/year: arXiv:1507.06611 (2015).
-- Journal/year: Proceedings of the Edinburgh Mathematical Society 68 (2025),
-- 1262--1296.
-- DOI: 10.1017/S0013091525100813.
-- Relationship: sharper terminal-shell criterion using a particular
-- solution-dependent sequence T_q approaching the possible blow-up time.
-- The sequence is not treated here as arbitrary input data.
--
-- Authors: Qionglei Chen; Changxing Miao; Zhifei Zhang.
-- Title: "The Beale-Kato-Majda criterion for the 3D
-- magneto-hydrodynamics equations".
-- Venue/year: Communications in Mathematical Physics 275 (2007), 861--872.
-- DOI: 10.1007/s00220-007-0319-y.
-- Relationship: frequency-localized terminal-window criterion for MHD; its
-- Navier--Stokes use requires an explicit b=0 specialization or a new proof
-- over DASHI's periodic projector interface.
--
-- This module records exact target shapes and route distinctions only.  It
-- imports no external theorem as an axiom and closes no BKM promotion gate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Reusable solution-dependent dissipation-wavenumber interface.
------------------------------------------------------------------------

record DissipationWavenumberInterface : Set₁ where
  field
    Time : Set

    DissipationDominated :
      Time → Nat → Set

    dissipationWavenumber :
      Time → Nat

    aboveThresholdIsDissipationDominated :
      (time : Time) →
      (shell : Nat) →
      dissipationWavenumber time < shell →
      DissipationDominated time shell

    thresholdDefinedByBernsteinViscosityComparison : Set

open DissipationWavenumberInterface public

record SourceDefinedTerminalSequence
    (range : DissipationWavenumberInterface) : Set₁ where
  field
    terminalSequence : Nat → Time range
    terminalTime : Time range
    terminalSequenceApproachesTerminalTime : Set
    sequenceDerivedFromDissipationRange : Set

open SourceDefinedTerminalSequence public

------------------------------------------------------------------------
-- Source-specific theorem target interfaces.
-- A target is inhabited only when all domain, projector, solution-class and
-- continuation obligations have been supplied constructively.
------------------------------------------------------------------------

record ClassicalBKMContinuationTarget : Set₁ where
  field
    periodicNavierStokesSolutionClass : Set
    vorticityL1TimeLInfinityFinite : Set
    continuationPastTerminalTime : Set
    criterionImpliesContinuation : Set

record CheskidovShvydkoyDissipationRangeTarget : Set₁ where
  field
    periodicLittlewoodPaleyProjectors : Set
    dissipationRange : DissipationWavenumberInterface
    highModesAbsorbedAboveQ : Set
    lowModeBesovIntegralFinite : Set
    lowModeCriterionImpliesContinuation : Set

record CheskidovDaiTerminalSequenceTarget : Set₁ where
  field
    periodicLittlewoodPaleyProjectors : Set
    dissipationRange : DissipationWavenumberInterface
    sourceDefinedTerminalSequenceTq :
      SourceDefinedTerminalSequence dissipationRange
    localizedVorticityIntegralSmall : Set
    localizedCriterionImpliesContinuation : Set

record ChenMiaoZhangUniformTerminalTarget : Set₁ where
  field
    periodicLittlewoodPaleyProjectors : Set
    uniformTerminalWindowLocalizedVorticitySmall : Set
    mhdToNavierStokesSpecializationOrPeriodicReproof : Set
    localizedCriterionImpliesContinuation : Set

------------------------------------------------------------------------
-- A final authority may be supplied by any complete route.  This sum type
-- prevents the localized lanes from being silently strengthened into the
-- classical global L1_t L-infinity criterion.
------------------------------------------------------------------------

data BKMContinuationAuthority : Set₁ where
  viaClassicalBKM :
    ClassicalBKMContinuationTarget →
    BKMContinuationAuthority

  viaCheskidovShvydkoy :
    CheskidovShvydkoyDissipationRangeTarget →
    BKMContinuationAuthority

  viaCheskidovDai :
    CheskidovDaiTerminalSequenceTarget →
    BKMContinuationAuthority

  viaChenMiaoZhang :
    ChenMiaoZhangUniformTerminalTarget →
    BKMContinuationAuthority

------------------------------------------------------------------------
-- Route-selection receipt.
------------------------------------------------------------------------

record LocalizedBKMSourceAuditReceipt : Set where
  constructor receipt
  field
    classicalRouteRecorded : Bool
    cheskidovShvydkoyRouteRecorded : Bool
    cheskidovDaiRouteRecorded : Bool
    chenMiaoZhangRouteRecorded : Bool

    cheskidovDaiTerminalSequenceRecognizedAsSolutionDependent : Bool
    chenMiaoZhangRecognizedAsMHDSource : Bool

    preferredFirstLocalizedTargetIsCheskidovShvydkoy : Bool

    classicalRouteConstructedInDASHI : Bool
    cheskidovShvydkoyRouteConstructedInDASHI : Bool
    cheskidovDaiRouteConstructedInDASHI : Bool
    chenMiaoZhangRouteConstructedInDASHI : Bool

open LocalizedBKMSourceAuditReceipt public

localizedBKMSourceAuditReceipt : LocalizedBKMSourceAuditReceipt
localizedBKMSourceAuditReceipt = receipt
  true
  true
  true
  true
  true
  true
  true
  false
  false
  false
  false

localizedBKMSourceTargetsRecorded : Bool
localizedBKMSourceTargetsRecorded = true

localizedBKMSourceTargetsRecordedIsTrue :
  localizedBKMSourceTargetsRecorded ≡ true
localizedBKMSourceTargetsRecordedIsTrue = refl

anyLocalizedContinuationRouteConstructed : Bool
anyLocalizedContinuationRouteConstructed = false

anyLocalizedContinuationRouteConstructedIsFalse :
  anyLocalizedContinuationRouteConstructed ≡ false
anyLocalizedContinuationRouteConstructedIsFalse = refl
