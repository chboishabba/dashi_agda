module DASHI.Papers.NavierStokes.CurrentTheoremInterfaceRound26 where

------------------------------------------------------------------------
-- Current normalized paper-facing Navier-Stokes interface after Round 26.
--
-- Round 25 retains the literal physical support theorem.  Round 26 reuses the
-- repository's physical Complex3 triad cancellation, forces the literal
-- five-source output fibre into a signed shell cell, and adds exact finite tax
-- accounting.  The continuum-real ODE, physical time-dependent shell balance,
-- uniform analytic taxes, strict margin, limits and Clay theorem remain open.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Papers.NavierStokes.TheoremInterface as Base
import DASHI.Papers.NavierStokes.CurrentTheoremInterfaceRound24 as R24
import DASHI.Papers.NavierStokes.CurrentTheoremInterfaceRound25 as R25
import DASHI.Papers.NavierStokes.GalerkinCriticalLedgerRound26 as R26

record CurrentNSPaperTheoremInterfaceRound26 : Setω where
  field
    round25Interface : R25.CurrentNSPaperTheoremInterfaceRound25
    round25InterfaceIsCanonical :
      round25Interface ≡ R25.canonicalCurrentNSPaperTheoremInterfaceRound25

    round26Status : R26.GalerkinCriticalLedgerRound26Status
    round26StatusIsCanonical :
      round26Status ≡ R26.canonicalGalerkinCriticalLedgerRound26Status

    physicalTriadEnergyCancellationChecked :
      R26.physicalTriadEnergyCancellation round26Status ≡ true

    signedCriticalLedgerChecked :
      R26.signedCriticalLedger round26Status ≡ true

    physicalFiveSourceSignedShellBridgeChecked :
      R26.physicalFiveSourceSignedShellBridge round26Status ≡ true

    duplicateFreeTaxOwnershipChecked :
      R26.duplicateFreeTaxOwnership round26Status ≡ true

    localODEInstanceStillOpen :
      R26.continuumRealPicardLindelofInstance round26Status ≡ false

    physicalTimeDependentShellBalanceStillOpen :
      R26.physicalTimeDependentShellBalance round26Status ≡ false

    cutoffUniformTaxesStillOpen :
      R26.cutoffUniformFiveClassTaxes round26Status ≡ false

    strictMarginStillOpen :
      R26.strictTotalViscosityMargin round26Status ≡ false

    clayPromotionStillFalse :
      Base.clayTerminalPromotion
        (R24.baseInterface
          (R25.round24Interface round25Interface))
      ≡ false

open CurrentNSPaperTheoremInterfaceRound26 public

canonicalCurrentNSPaperTheoremInterfaceRound26 :
  CurrentNSPaperTheoremInterfaceRound26
canonicalCurrentNSPaperTheoremInterfaceRound26 = record
  { round25Interface =
      R25.canonicalCurrentNSPaperTheoremInterfaceRound25
  ; round25InterfaceIsCanonical = refl
  ; round26Status =
      R26.canonicalGalerkinCriticalLedgerRound26Status
  ; round26StatusIsCanonical = refl
  ; physicalTriadEnergyCancellationChecked = R26.finiteAlgebraAdvanced
  ; signedCriticalLedgerChecked = refl
  ; physicalFiveSourceSignedShellBridgeChecked =
      R26.physicalSignedShellBridgeAdvanced
  ; duplicateFreeTaxOwnershipChecked = R26.taxOwnershipAdvanced
  ; localODEInstanceStillOpen = R26.localODEInstanceRemainsOpen
  ; physicalTimeDependentShellBalanceStillOpen =
      R26.physicalShellBalanceRemainsOpen
  ; cutoffUniformTaxesStillOpen = R26.uniformTaxRemainsOpen
  ; strictMarginStillOpen = R26.strictMarginRemainsOpen
  ; clayPromotionStillFalse = R25.currentRound25ClayPromotionFalse
  }

currentRound26PhysicalShellBridgeChecked :
  R26.physicalFiveSourceSignedShellBridge
    (round26Status canonicalCurrentNSPaperTheoremInterfaceRound26)
  ≡ true
currentRound26PhysicalShellBridgeChecked =
  R26.physicalSignedShellBridgeAdvanced

currentRound26TaxOwnershipChecked :
  R26.duplicateFreeTaxOwnership
    (round26Status canonicalCurrentNSPaperTheoremInterfaceRound26)
  ≡ true
currentRound26TaxOwnershipChecked = R26.taxOwnershipAdvanced

currentRound26ClayPromotionFalse :
  Base.clayTerminalPromotion
    (R24.baseInterface
      (R25.round24Interface
        (round25Interface canonicalCurrentNSPaperTheoremInterfaceRound26)))
  ≡ false
currentRound26ClayPromotionFalse = R25.currentRound25ClayPromotionFalse
