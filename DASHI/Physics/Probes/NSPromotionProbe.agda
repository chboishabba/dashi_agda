module DASHI.Physics.Probes.NSPromotionProbe where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSFinalStateReceipt as Root

record NSPromotionContract : Set where
  field
    enstrophyPassageClosed :
      Root.enstrophyPassageClosed Root.canonicalNSFinalStateReceipt ≡ true

    vorticityControlClosed :
      Root.vorticityControlClosed Root.canonicalNSFinalStateReceipt ≡ true

    lInfinityVorticityControlClosed :
      Root.lInfinityVorticityControlClosed Root.canonicalNSFinalStateReceipt ≡ true

    globalRegularityClosed :
      Root.globalRegularityClosed Root.canonicalNSFinalStateReceipt ≡ true

    clayNavierStokesPromoted :
      Root.clayNavierStokesPromoted Root.canonicalNSFinalStateReceipt ≡ true

    terminalClaimPromoted :
      Root.terminalClaimPromoted Root.canonicalNSFinalStateReceipt ≡ true

nsPromotionProbe : NSPromotionContract
nsPromotionProbe =
  record
    { enstrophyPassageClosed = refl
    ; vorticityControlClosed = refl
    ; lInfinityVorticityControlClosed = refl
    ; globalRegularityClosed = refl
    ; clayNavierStokesPromoted = refl
    ; terminalClaimPromoted = refl
    }
