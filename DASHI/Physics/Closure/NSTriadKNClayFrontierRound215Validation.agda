module DASHI.Physics.Closure.NSTriadKNClayFrontierRound215Validation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComparableConstantBandGramNoGoRound214Exact as R214
import DASHI.Physics.Closure.NSTriadKNThreeClassPositiveResidualCompilerRound215Exact as R215
import DASHI.Physics.Closure.NSTriadKNClayFrontierRound215Exact as Frontier

constantBandNoGoRegression :
  R214.round214ConstantShellBandAlonePaysGramDebt ≡ false
constantBandNoGoRegression = refl

signedStructureRequiredRegression :
  R214.round214PhysicalSignedStructureStillRequired ≡ true
signedStructureRequiredRegression = refl

positiveResidualCompilerRegression :
  R215.round215ThreeClassPositiveResidualCompilerClosed ≡ true
positiveResidualCompilerRegression = refl

noGramNegativityRegression :
  R215.round215RequiresWithinClassGramNegativity ≡ false
noGramNegativityRegression = refl

farLowStillOpenRegression :
  Frontier.round215FarLowPhysicalResidualBudgetClosed ≡ false
farLowStillOpenRegression = refl

highHighStillOpenRegression :
  Frontier.round215HighHighPhysicalResidualBudgetClosed ≡ false
highHighStillOpenRegression = refl

comparableStillOpenRegression :
  Frontier.round215ComparablePhysicalResidualBudgetClosed ≡ false
comparableStillOpenRegression = refl

packageAStillOpenRegression : Frontier.round215PackageAClosed ≡ false
packageAStillOpenRegression = refl

clayStillFalseRegression : Frontier.round215ClayPromotion ≡ false
clayStillFalseRegression = refl
