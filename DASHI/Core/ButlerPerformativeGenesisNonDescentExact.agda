module DASHI.Core.ButlerPerformativeGenesisNonDescentExact where

------------------------------------------------------------------------
-- PERFORMATIVE GENESIS NON-DESCENT
--
-- SOURCE CALIBRATION
-- Judith Butler, Gender Trouble: Feminism and the Subversion of Identity,
-- Routledge, 1990. ISBN 9780415389556 (2006 edition). No DOI asserted.
--
-- Butler motivates the warning that stable identity surfaces may be effects of
-- repeated constitutive acts rather than prior grounds. The finite history
-- witness below is a DASHI construction, not a theorem attributed to Butler.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF

data ConstitutiveHistory : Set where
  repeatedNormativeActs divergentIterativeActs : ConstitutiveHistory

data PresentCategory : Set where samePresentCategory : PresentCategory

data GenesisClass : Set where normativeGenesis divergentGenesis : GenesisClass

presentCategory : ConstitutiveHistory → PresentCategory
presentCategory repeatedNormativeActs = samePresentCategory
presentCategory divergentIterativeActs = samePresentCategory

genesis : ConstitutiveHistory → GenesisClass
genesis repeatedNormativeActs = normativeGenesis
genesis divergentIterativeActs = divergentGenesis

presentCategoryCannotRecoverGenesis :
  INF.FactorsThrough presentCategory genesis → ⊥
presentCategoryCannotRecoverGenesis =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness repeatedNormativeActs divergentIterativeActs refl (λ ()))

record PerformativeGenesisBoundary : Set where
  constructor performative-genesis-boundary
  field
    presentCategoryDeterminesConstitutiveHistory : Bool
    presentCategoryDeterminesConstitutiveHistoryIsFalse :
      presentCategoryDeterminesConstitutiveHistory ≡ false
    performativeGenesisIsBadiouCountAsOne : Bool
    performativeGenesisIsBadiouCountAsOneIsFalse :
      performativeGenesisIsBadiouCountAsOne ≡ false
    performativeGenesisIsBhabhaThirdSpace : Bool
    performativeGenesisIsBhabhaThirdSpaceIsFalse :
      performativeGenesisIsBhabhaThirdSpace ≡ false

canonicalPerformativeGenesisBoundary : PerformativeGenesisBoundary
canonicalPerformativeGenesisBoundary =
  performative-genesis-boundary false refl false refl false refl
