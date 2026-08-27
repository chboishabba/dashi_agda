module DASHI.Core.LacanSexuationTernarySeparationExact where

------------------------------------------------------------------------
-- LACAN SEXUATION / TERNARY COUNT SEPARATION
--
-- SOURCE CONTEXT
--
-- Jacques Lacan, On Feminine Sexuality, the Limits of Love and Knowledge:
-- The Seminar of Jacques Lacan, Book XX, Encore 1972-1973,
-- ed. Jacques-Alain Miller, trans. Bruce Fink, W. W. Norton & Company,
-- English edition 1999. ISBN 9780393319163. No DOI asserted.
--
-- SOURCE SCOPE
--
-- Seminar XX's formulas of sexuation use quantifier/phallic-function structure.
-- This module records only a typed role inventory sufficient to prevent their
-- collapse into the independent Frege-derived 0/1/2 chart.  It does not claim
-- to rederive Lacan's formulas, nor to assert a biological male/female ontology.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.TernaryRoleCarrierExact as Ternary

------------------------------------------------------------------------
-- Formula-role vocabulary, deliberately non-ternary.
------------------------------------------------------------------------

data SexuationFormulaRole : Set where
  masculineUniversalPhallicFunction
  masculineExceptionToPhallicFunction
  feminineNotAllPhallicFunction
  feminineNoExceptionTerm
  : SexuationFormulaRole

------------------------------------------------------------------------
-- Ternary count and sexuation are distinct source/formal surfaces.
------------------------------------------------------------------------

data LacanFormalSurface : Set where
  fregeDerivedCountSurface
  discourseS1S2Surface
  sexuationFormulaSurface
  : LacanFormalSurface

fregeCount≠sexuation : fregeDerivedCountSurface ≡ sexuationFormulaSurface → ⊥
fregeCount≠sexuation ()

discourse≠sexuation : discourseS1S2Surface ≡ sexuationFormulaSurface → ⊥
discourse≠sexuation ()

------------------------------------------------------------------------
-- No total map from the three-code carrier is installed as the sexuation
-- formula system.  A source-justified translation would require its own witness.
------------------------------------------------------------------------

record SexuationTranslationAuthority : Set where
  constructor sexuation-translation-authority
  field
    sourceSurface targetSurface : LacanFormalSurface
    sourceTargetDistinct : sourceSurface ≡ targetSurface → ⊥

canonicalCountSexuationSeparation : SexuationTranslationAuthority
canonicalCountSexuationSeparation =
  sexuation-translation-authority
    fregeDerivedCountSurface sexuationFormulaSurface fregeCount≠sexuation

record LacanSexuationBoundary : Set where
  constructor lacan-sexuation-boundary
  field
    sexuationIsThreeCodeCarrier : Bool
    sexuationIsThreeCodeCarrierIsFalse : sexuationIsThreeCodeCarrier ≡ false
    fregeNumeralTwoIsFeminineNotAll : Bool
    fregeNumeralTwoIsFeminineNotAllIsFalse :
      fregeNumeralTwoIsFeminineNotAll ≡ false
    sexuationFormulaRoleIsBiologicalSexEssence : Bool
    sexuationFormulaRoleIsBiologicalSexEssenceIsFalse :
      sexuationFormulaRoleIsBiologicalSexEssence ≡ false
    finiteRoleInventoryReprovesSeminarXX : Bool
    finiteRoleInventoryReprovesSeminarXXIsFalse :
      finiteRoleInventoryReprovesSeminarXX ≡ false
    translationFromTernaryInstalled : Bool
    translationFromTernaryInstalledIsFalse :
      translationFromTernaryInstalled ≡ false

canonicalLacanSexuationBoundary : LacanSexuationBoundary
canonicalLacanSexuationBoundary =
  lacan-sexuation-boundary false refl false refl false refl false refl false refl
