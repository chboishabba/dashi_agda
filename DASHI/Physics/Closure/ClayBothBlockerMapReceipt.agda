module DASHI.Physics.Closure.ClayBothBlockerMapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSCarrierContinuumLimitReceipt as NSLimit
import DASHI.Physics.Closure.OSAxiomsContinuumStatus as OSStatus
import DASHI.Physics.Closure.RGScaleVsCarrierScaleReceipt as RGScale

data YangMillsTerminalBlocker : Set where
  su3GaugeIdentificationOpen : YangMillsTerminalBlocker
  continuumRGConvergenceOpen : YangMillsTerminalBlocker

data NavierStokesTerminalBlocker : Set where
  multibaseRieszWaveletBridgeOpen : NavierStokesTerminalBlocker
  nonlinearTermPassageOpen : NavierStokesTerminalBlocker

canonicalYangMillsTerminalBlockers : List YangMillsTerminalBlocker
canonicalYangMillsTerminalBlockers =
  su3GaugeIdentificationOpen
  ∷ continuumRGConvergenceOpen
  ∷ []

canonicalNavierStokesTerminalBlockers : List NavierStokesTerminalBlocker
canonicalNavierStokesTerminalBlockers =
  multibaseRieszWaveletBridgeOpen
  ∷ nonlinearTermPassageOpen
  ∷ []

ymReductionStatement : String
ymReductionStatement =
  "YM mass-gap closure reduces to SU3/gauge identification plus continuum RG convergence; the scalar OS sub-blocker is dissolved only for the scalar sector."

nsReductionStatement : String
nsReductionStatement =
  "NS regularity closure reduces to the multibase Riesz/wavelet bridge plus the nonlinear term passage."

record ClayBothBlockerMapReceipt : Setω where
  field
    rgScaleReceipt :
      RGScale.RGScaleVsCarrierScaleReceipt

    dimensionfulYMGapsStillOpen :
      RGScale.dimensionfulMassGapFromRG rgScaleReceipt ≡ false

    osAxiomStatusReceipt :
      OSStatus.OSAxiomsContinuumStatusReceipt

    osAxiomsStillOpen :
      OSStatus.wightmanReconstructionApplied osAxiomStatusReceipt ≡ false

    scalarOSSubBlockerDissolved :
      Bool

    scalarOSSubBlockerDissolvedIsTrue :
      scalarOSSubBlockerDissolved ≡ true

    scalarOSDissolvesFullGaugeOS :
      Bool

    scalarOSDissolvesFullGaugeOSIsFalse :
      scalarOSDissolvesFullGaugeOS ≡ false

    nsContinuumLimitReceipt :
      NSLimit.NSCarrierContinuumLimitReceipt

    nsSmoothLimitStillOpen :
      NSLimit.nsSmoothContinuumLimit nsContinuumLimitReceipt ≡ false

    ymMassGapReducesTo :
      String

    ymMassGapReducesToIsCanonical :
      ymMassGapReducesTo ≡ ymReductionStatement

    nsBlockerIs :
      String

    nsBlockerIsCanonical :
      nsBlockerIs ≡ nsReductionStatement

    yangMillsBlockers :
      List YangMillsTerminalBlocker

    yangMillsBlockersAreCanonical :
      yangMillsBlockers ≡ canonicalYangMillsTerminalBlockers

    navierStokesBlockers :
      List NavierStokesTerminalBlocker

    navierStokesBlockersAreCanonical :
      navierStokesBlockers ≡ canonicalNavierStokesTerminalBlockers

    yangMillsMassGapClayPromoted :
      Bool

    yangMillsMassGapClayPromotedIsFalse :
      yangMillsMassGapClayPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    bothClayProblemsClosed :
      Bool

    bothClayProblemsClosedIsFalse :
      bothClayProblemsClosed ≡ false

    receiptBoundary :
      List String

open ClayBothBlockerMapReceipt public

canonicalClayBothBlockerMapReceipt : ClayBothBlockerMapReceipt
canonicalClayBothBlockerMapReceipt =
  record
    { rgScaleReceipt =
        RGScale.canonicalRGScaleVsCarrierScaleReceipt
    ; dimensionfulYMGapsStillOpen =
        refl
    ; osAxiomStatusReceipt =
        OSStatus.canonicalOSAxiomsContinuumStatusReceipt
    ; osAxiomsStillOpen =
        refl
    ; scalarOSSubBlockerDissolved =
        true
    ; scalarOSSubBlockerDissolvedIsTrue =
        refl
    ; scalarOSDissolvesFullGaugeOS =
        false
    ; scalarOSDissolvesFullGaugeOSIsFalse =
        refl
    ; nsContinuumLimitReceipt =
        NSLimit.canonicalNSCarrierContinuumLimitReceipt
    ; nsSmoothLimitStillOpen =
        refl
    ; ymMassGapReducesTo =
        ymReductionStatement
    ; ymMassGapReducesToIsCanonical =
        refl
    ; nsBlockerIs =
        nsReductionStatement
    ; nsBlockerIsCanonical =
        refl
    ; yangMillsBlockers =
        canonicalYangMillsTerminalBlockers
    ; yangMillsBlockersAreCanonical =
        refl
    ; navierStokesBlockers =
        canonicalNavierStokesTerminalBlockers
    ; navierStokesBlockersAreCanonical =
        refl
    ; yangMillsMassGapClayPromoted =
        false
    ; yangMillsMassGapClayPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; bothClayProblemsClosed =
        false
    ; bothClayProblemsClosedIsFalse =
        refl
    ; receiptBoundary =
        "The YM blockers are now stated as SU3/gauge identification plus continuum RG convergence"
        ∷ "The scalar OS sub-blocker is dissolved only for the scalar sector and does not close full gauge OS/Wightman"
        ∷ "The NS blockers are now stated as the multibase Riesz/wavelet bridge plus nonlinear term passage"
        ∷ "Both Clay terminal promotion flags remain false"
        ∷ []
    }

clayBothBlockerMapKeepsPromotionsFalse :
  bothClayProblemsClosed canonicalClayBothBlockerMapReceipt ≡ false
clayBothBlockerMapKeepsPromotionsFalse =
  refl
