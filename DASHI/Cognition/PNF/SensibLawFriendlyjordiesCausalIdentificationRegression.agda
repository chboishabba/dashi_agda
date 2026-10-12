module DASHI.Cognition.PNF.SensibLawFriendlyjordiesCausalIdentificationRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.SensibLawFriendlyjordiesCausalIdentificationMaxCutExact as MaxCut

cprsDirectFactsDoNotIdentifyEffect :
  MaxCut.cprsDirectFactsDoNotIdentifyEffect ≡ true
cprsDirectFactsDoNotIdentifyEffect = refl

southAustraliaOperationalFactsDoNotIdentifyGovernanceEffect :
  MaxCut.southAustraliaOperationalFactsDoNotIdentifyGovernanceEffect ≡ true
southAustraliaOperationalFactsDoNotIdentifyGovernanceEffect = refl

identificationReceiptRequired :
  MaxCut.identificationReceiptRequired ≡ true
identificationReceiptRequired = refl

sourcePaymentSeparateFromCausalIdentification :
  MaxCut.sourcePaymentSeparateFromCausalIdentification ≡ true
sourcePaymentSeparateFromCausalIdentification = refl

identifiedLocalEffectCreatesUniversalPartyRanking :
  MaxCut.identifiedLocalEffectCreatesUniversalPartyRanking ≡ false
identifiedLocalEffectCreatesUniversalPartyRanking = refl
