module DASHI.Moonshine.OggSSPSmallCharacteristicSOTATerminalFourthTermRefinementExact where

------------------------------------------------------------------------
-- SOTA TERMINAL FOURTH-TERM REFINEMENT
--
-- This owner intersects the existing terminal bad-level/inertia authority with
-- the two strongest source-driven refinements now known:
--
--   (1) p=2 inertia-RR needs character/tangent data in addition to centralizer
--       order/depth, and both p=2,p=3 need genuinely wild ramification data;
--
--   (2) small-characteristic Igusa geometry supplies Hasse/osculation and
--       Frobenius-pullback local coordinates which must belong to the SAME
--       bad-level object whose Hauptmodul/q-expansion valuation is computed.
--
-- The resulting authority is deliberately difficult to inhabit.  It is the
-- current fail-closed theorem target; no constructor is supplied from counts,
-- centralizer depths, tame RR, raw ramification, or osculation alone.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPSmallCharacteristicBadLevelIgusaCorrectionCutsetExact as Igusa
import DASHI.Moonshine.OggSSPSmallCharacteristicBadLevelInertiaLocalizedFourthTermCutsetExact as Terminal
import DASHI.Moonshine.OggSSPSmallCharacteristicSOTAInertiaRRRefinementExact as SOTARR
import DASHI.Moonshine.OggSSPSmallCharacteristicIgusaOsculationHasseCutsetExact as Osculation
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Strong terminal authority.
------------------------------------------------------------------------

record SOTATerminalFourthTermAuthority : Set₁ where
  field
    terminal :
      Terminal.BadLevelInertiaLocalizedFourthTermAuthority

    characterAwareWildValuation :
      SOTARR.SOTACharacterAwareWildValuationAuthority

    p2HasseOsculation :
      Osculation.HasseOsculationBadLevelAuthority Igusa.pTwo

    p3HasseOsculation :
      Osculation.HasseOsculationBadLevelAuthority Igusa.pThree

    p2UsesSameIgusaAuthority :
      Osculation.igusaAuthority p2HasseOsculation
      ≡
      Igusa.authority (Terminal.p2IgusaAuthority terminal)

    p3UsesSameIgusaAuthority :
      Osculation.igusaAuthority p3HasseOsculation
      ≡
      Igusa.authority (Terminal.p3IgusaAuthority terminal)

    p2CharacterAwareTermsLocalizeOnTerminalFiveSectors :
      Bool
    p2CharacterAwareTermsLocalizeOnTerminalFiveSectorsIsTrue :
      p2CharacterAwareTermsLocalizeOnTerminalFiveSectors ≡ true

    p3BranchAwareTermsAgreeWithTerminalBranchTransport :
      Bool
    p3BranchAwareTermsAgreeWithTerminalBranchTransportIsTrue :
      p3BranchAwareTermsAgreeWithTerminalBranchTransport ≡ true

    hasseOsculationFeedsSameCorrectedDivisor :
      Bool
    hasseOsculationFeedsSameCorrectedDivisorIsTrue :
      hasseOsculationFeedsSameCorrectedDivisor ≡ true

    oneExceptionalObjectCarriesAllLocalData :
      Bool
    oneExceptionalObjectCarriesAllLocalDataIsTrue :
      oneExceptionalObjectCarriesAllLocalData ≡ true

open SOTATerminalFourthTermAuthority public

------------------------------------------------------------------------
-- 2. Existing terminal theorem adapters remain available.
------------------------------------------------------------------------

asTerminalAuthority :
  SOTATerminalFourthTermAuthority ->
  Terminal.BadLevelInertiaLocalizedFourthTermAuthority
asTerminalAuthority =
  terminal

asMonsterBridgeAuthority =
  Terminal.asMonsterBridgeAuthority ∘ asTerminalAuthority

asJointAuthority =
  Terminal.asJointAuthority ∘ asTerminalAuthority

asLicensedFourTermExtension =
  Terminal.asLicensedFourTermExtension ∘ asTerminalAuthority

------------------------------------------------------------------------
-- 3. No one-sided shortcut can inhabit the intersection.
------------------------------------------------------------------------

data OldTerminalAuthorityAutomaticallyCharacterAware : Set where
data CharacterAwareLocalDataAutomaticallyPaysBadLevelFricke : Set where
data HasseOsculationAutomaticallyPaysInertiaLocalization : Set where
data SeparateAuthoritiesAutomaticallyReferToSameExceptionalObject : Set where

oldTerminalDoesNotAutomaticallySupplyCharacterAwareness :
  OldTerminalAuthorityAutomaticallyCharacterAware -> ⊥
oldTerminalDoesNotAutomaticallySupplyCharacterAwareness ()

characterAwareLocalDataDoesNotAutomaticallyPayBadLevelFricke :
  CharacterAwareLocalDataAutomaticallyPaysBadLevelFricke -> ⊥
characterAwareLocalDataDoesNotAutomaticallyPayBadLevelFricke ()

hasseOsculationDoesNotAutomaticallyPayInertiaLocalization :
  HasseOsculationAutomaticallyPaysInertiaLocalization -> ⊥
hasseOsculationDoesNotAutomaticallyPayInertiaLocalization ()

separateAuthoritiesDoNotAutomaticallyShareExceptionalObject :
  SeparateAuthoritiesAutomaticallyReferToSameExceptionalObject -> ⊥
separateAuthoritiesDoNotAutomaticallyShareExceptionalObject ()

------------------------------------------------------------------------
-- 4. Live theorem wall.
------------------------------------------------------------------------

data SOTATerminalFourthTermAuthorityInhabited : Set where

sotaTerminalAuthorityStillOpen :
  SOTATerminalFourthTermAuthorityInhabited -> ⊥
sotaTerminalAuthorityStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record SOTATerminalFourthTermBoundary : Set where
  constructor sota-terminal-fourth-term-boundary
  field
    oldTerminalBadLevelCutsetRetained : Bool
    p2CharacterAwareWildDataRequired : Bool
    p3BranchAwareWildDataRequired : Bool
    p2HasseOsculationRequired : Bool
    p3HasseOsculationRequired : Bool
    sameIgusaAuthorityEqualityRequired : Bool
    sameExceptionalObjectRequired : Bool
    adapterToMonsterBridgeRetained : Bool
    terminalAuthorityInhabited : Bool
    attributionFirewallPreserved : Bool

canonicalSOTATerminalFourthTermBoundary :
  SOTATerminalFourthTermBoundary
canonicalSOTATerminalFourthTermBoundary =
  sota-terminal-fourth-term-boundary
    true true true true true true true true false true
