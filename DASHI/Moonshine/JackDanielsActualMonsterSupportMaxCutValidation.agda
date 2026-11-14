module DASHI.Moonshine.JackDanielsActualMonsterSupportMaxCutValidation where

open import DASHI.Core.Prelude

import DASHI.Moonshine.JackDanielsActualMonsterSupportMaxCutExact as Capstone

validationBoundary : Capstone.JackDanielsActualMonsterSupportBoundary
validationBoundary = Capstone.canonicalJackDanielsActualMonsterSupportBoundary

allTwentyControlsMatched :
  Capstone.allTwentyActualSupportComparisonsPaid ≡ true
allTwentyControlsMatched = refl

externalOggNotUsedAsProof :
  Capstone.externalOggLabelUsedInCapstone ≡ false
externalOggNotUsedAsProof = refl

monsterPrimeLaneNotUsedAsProof :
  Capstone.monsterPrimeLaneUsedInCapstone ≡ false
monsterPrimeLaneNotUsedAsProof = refl
