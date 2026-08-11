module DASHI.Papers.NavierStokes.CurrentTheoremInterfaceRound25 where

------------------------------------------------------------------------
-- Current normalized paper-facing Navier-Stokes interface after Round 25.
--
-- The Round 24 interface retains the literal Clay contract and claimed-paper
-- audit.  Round 25 adds exact finite-carrier evidence and promotes only L4.
-- The terminal Clay flag and every unresolved analytic producer remain false.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Papers.NavierStokes.TheoremInterface as Base
import DASHI.Papers.NavierStokes.CurrentTheoremInterfaceRound24 as R24
import DASHI.Papers.NavierStokes.PhysicalCarrierSupportRound25 as R25

record CurrentNSPaperTheoremInterfaceRound25 : Setω where
  field
    round24Interface : R24.CurrentNSPaperTheoremInterfaceRound24
    round24InterfaceIsCanonical :
      round24Interface ≡ R24.canonicalCurrentNSPaperTheoremInterfaceRound24

    physicalCarrierSupportStatus :
      R25.PhysicalCarrierSupportRound25Status
    physicalCarrierSupportStatusIsCanonical :
      physicalCarrierSupportStatus
      ≡ R25.canonicalPhysicalCarrierSupportRound25Status

    L4PhysicalSupportCheckedExact :
      R25.L4CheckedExact physicalCarrierSupportStatus ≡ true

    finiteODEInstanceStillOpen :
      R25.finiteDimensionalODEInstanceProduced
        physicalCarrierSupportStatus
      ≡ false

    L7PhysicalTaxesStillOpen :
      R25.L7UniformPhysicalTaxesProduced
        physicalCarrierSupportStatus
      ≡ false

    strictMarginStillOpen :
      R25.L15StrictViscosityMarginProduced
        physicalCarrierSupportStatus
      ≡ false

    clayPromotionStillFalse :
      Base.clayTerminalPromotion
        (R24.baseInterface round24Interface)
      ≡ false

open CurrentNSPaperTheoremInterfaceRound25 public

canonicalCurrentNSPaperTheoremInterfaceRound25 :
  CurrentNSPaperTheoremInterfaceRound25
canonicalCurrentNSPaperTheoremInterfaceRound25 = record
  { round24Interface =
      R24.canonicalCurrentNSPaperTheoremInterfaceRound24
  ; round24InterfaceIsCanonical = refl
  ; physicalCarrierSupportStatus =
      R25.canonicalPhysicalCarrierSupportRound25Status
  ; physicalCarrierSupportStatusIsCanonical = refl
  ; L4PhysicalSupportCheckedExact = R25.l4IsCheckedExact
  ; finiteODEInstanceStillOpen = R25.finiteODEInstanceRemainsOpen
  ; L7PhysicalTaxesStillOpen = R25.physicalTaxesRemainOpen
  ; strictMarginStillOpen = R25.strictMarginRemainsOpen
  ; clayPromotionStillFalse = R24.currentClayPromotionFalse
  }

currentRound25L4Checked :
  R25.L4CheckedExact
    (physicalCarrierSupportStatus
      canonicalCurrentNSPaperTheoremInterfaceRound25)
  ≡ true
currentRound25L4Checked = R25.l4IsCheckedExact

currentRound25ClayPromotionFalse :
  Base.clayTerminalPromotion
    (R24.baseInterface
      (round24Interface canonicalCurrentNSPaperTheoremInterfaceRound25))
  ≡ false
currentRound25ClayPromotionFalse = R24.currentClayPromotionFalse
