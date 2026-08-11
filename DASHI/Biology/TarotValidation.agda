module DASHI.Biology.TarotValidation where

open import DASHI.Core.Prelude

import DASHI.Everything
import DASHI.Biology.TarotEverything
import DASHI.Biology.TarotCarrierExact as Tarot
import DASHI.Biology.TarotInterpretationPNFExact as PNF

------------------------------------------------------------------------
-- Cumulative validation root: existing repository plus tarot tranche.
------------------------------------------------------------------------

tarotValidationDeckCount : Tarot.listCount Tarot.allCards ≡ 78
tarotValidationDeckCount = Tarot.riderWaiteSmithDeckCountIsSeventyEight

tarotValidationDoesNotClaimFutureCausation :
  PNF.futureCausationProved PNF.canonicalTarotAuthorityFlags ≡ false
tarotValidationDoesNotClaimFutureCausation = refl
