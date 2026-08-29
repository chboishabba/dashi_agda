module DASHI.Physics.Closure.NSTriadKNClayFrontierRound216Validation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNPackageASelfExternalSignedProductionCompilerRound216Exact as Compiler
import DASHI.Physics.Closure.NSTriadKNClayFrontierRound216Exact as Frontier

compilerRegression :
  Compiler.round216SelfExternalSignedProductionCompilerClosed ≡ true
compilerRegression = refl

noGramNegativityRegression :
  Compiler.round216RequiresClasswiseGramNegativity ≡ false
noGramNegativityRegression = refl

noCellwiseAbsoluteValueRegression :
  Compiler.round216RequiresCellwiseAbsoluteValues ≡ false
noCellwiseAbsoluteValueRegression = refl

selfPortStillOpenRegression :
  Frontier.round216InternalSelfPaymentAgdaSameObjectPortClosed ≡ false
selfPortStillOpenRegression = refl

externalNovelLeafStillOpenRegression :
  Frontier.round216ExternalSignedNetworkCompanionBudgetClosed ≡ false
externalNovelLeafStillOpenRegression = refl

oneNovelLeafRegression : Frontier.round216NovelMathematicalLeafCount ≡ 1
oneNovelLeafRegression = refl

packageAStillOpenRegression : Frontier.round216PackageAClosed ≡ false
packageAStillOpenRegression = refl

clayStillFalseRegression : Frontier.round216ClayPromotion ≡ false
clayStillFalseRegression = refl
