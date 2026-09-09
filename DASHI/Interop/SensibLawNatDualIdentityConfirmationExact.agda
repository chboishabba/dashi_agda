module DASHI.Interop.SensibLawNatDualIdentityConfirmationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Interop.SensibLawWikidataBalancedTernaryAdmissibilityHyperfabricExact as Ternary

------------------------------------------------------------------------
-- DUAL IDENTITY / ROUTING CONFIRMATION
--
-- Nat acquisition can know an exact requested Wikidata QID even when the
-- hosted Zelph nodeOfName partition does not currently locate it. A clean
-- Zelph exhaustion therefore leaves the graph/routing coordinate open. An
-- independent revision-locked Wikidata entity export may still confirm the
-- explicit subject strongly enough to inspect the native Q/property family.
------------------------------------------------------------------------

record DualIdentityConfirmation : Set where
  constructor dualIdentityConfirmation
  field
    zelphRouteConfirmation : Ternary.AdmissibilityState
    wikidataSubjectConfirmation : Ternary.AdmissibilityState
    nativeFamilyCoverage : Ternary.AdmissibilityState
    sourceSupport : Ternary.AdmissibilityState
    authority : Ternary.AdmissibilityState
open DualIdentityConfirmation public

cleanZelphMissWikidataConfirmedCoveragePaid : DualIdentityConfirmation
cleanZelphMissWikidataConfirmedCoveragePaid =
  dualIdentityConfirmation
    Ternary.open
    Ternary.admitted
    Ternary.admitted
    Ternary.open
    Ternary.open

zelphRouteRemainsOpen :
  zelphRouteConfirmation cleanZelphMissWikidataConfirmedCoveragePaid ≡ Ternary.open
zelphRouteRemainsOpen = refl

wikidataSubjectIsAdmitted :
  wikidataSubjectConfirmation cleanZelphMissWikidataConfirmedCoveragePaid ≡ Ternary.admitted
wikidataSubjectIsAdmitted = refl

coverageMayBeAdmittedFromWikidataSubject :
  nativeFamilyCoverage cleanZelphMissWikidataConfirmedCoveragePaid ≡ Ternary.admitted
coverageMayBeAdmittedFromWikidataSubject = refl

sourceSupportRemainsOpen :
  sourceSupport cleanZelphMissWikidataConfirmedCoveragePaid ≡ Ternary.open
sourceSupportRemainsOpen = refl

authorityRemainsOpen :
  authority cleanZelphMissWikidataConfirmedCoveragePaid ≡ Ternary.open
authorityRemainsOpen = refl

record DualIdentityBoundary : Set where
  constructor dualIdentityBoundary
  field
    cleanZelphMissMeansWikidataEntityAbsent : Bool
    wikidataEntityConfirmationPaysZelphRouteResidual : Bool
    wikidataEntityConfirmationMaySupportNativeFamilyInspection : Bool
    nativeFamilyInspectionPaysSourceSupport : Bool
    nativeFamilyInspectionPaysAuthority : Bool
open DualIdentityBoundary public

canonicalDualIdentityBoundary : DualIdentityBoundary
canonicalDualIdentityBoundary =
  dualIdentityBoundary false false true false false
