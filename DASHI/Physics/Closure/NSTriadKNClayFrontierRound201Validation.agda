module DASHI.Physics.Closure.NSTriadKNClayFrontierRound201Validation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Closure.NSTriadKNClayFrontierRound200Exact as R200
import DASHI.Physics.Closure.NSTriadKNBlockGramCovarianceTelescopeRound201Exact as R201
import DASHI.Physics.Closure.NSTriadKNClayFrontierRound201Exact as Frontier

quarticCompanionDegreeCorrect :
  R200.round200QuadraticKernelHasRequiredCompanionDegree ≡ true
quarticCompanionDegreeCorrect = refl

lawOfTotalGramClosed : R201.round201LawOfTotalGramClosed ≡ true
lawOfTotalGramClosed = refl

withinBetweenDebtSeparated :
  R201.round201WithinAndBetweenBlockDebtSeparatedExactly ≡ true
withinBetweenDebtSeparated = refl

noPrematureAbsoluteValue :
  R201.round201AbsoluteValueIntroducedBeforeBlockTelescope ≡ false
noPrematureAbsoluteValue = refl

noBlockCountTax : R201.round201ShellOrBonyBlockCountFactorIntroduced ≡ false
noBlockCountTax = refl

packageAStillOpen : Frontier.round201PackageAClosed ≡ false
packageAStillOpen = refl

noClayPromotion : Frontier.round201ClayPromotion ≡ false
noClayPromotion = refl
