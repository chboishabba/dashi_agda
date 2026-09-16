module DASHI.Wikimedia.IbrahimMonster42ClassEtaFamilyOEISAcquisitionValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Wikimedia.IbrahimMonster42ClassEtaFamilyOEISAcquisitionExact as A

familyLocatedRegression :
  A.four42ClassSeriesLocated A.currentMonster42ClassEtaFamilyBoundary ≡ true
familyLocatedRegression = refl

fourteenLevelRegression :
  A.etaLevel14SourceNative A.currentMonster42ClassEtaFamilyBoundary ≡ true
fourteenLevelRegression = refl

fortyTwoLevelRegression :
  A.etaLevel42SourceNative A.currentMonster42ClassEtaFamilyBoundary ≡ true
fortyTwoLevelRegression = refl

fifteenMinusOneFirewallRegression :
  A.fifteenMinusOneExplainsEtaLevel14 A.currentMonster42ClassEtaFamilyBoundary ≡ false
fifteenMinusOneFirewallRegression = refl

carrierSameObjectFirewallRegression :
  A.fortyTwoCarrierCreatesMonster42dSameObject A.currentMonster42ClassEtaFamilyBoundary ≡ false
carrierSameObjectFirewallRegression = refl
