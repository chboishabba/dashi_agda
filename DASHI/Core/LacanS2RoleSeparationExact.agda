module DASHI.Core.LacanS2RoleSeparationExact where

------------------------------------------------------------------------
-- LACAN S2 ROLE SEPARATION
--
-- SOURCE CONTEXT
--
-- Jacques Lacan, Seminar IX: L'identification (1961-1962), Seminar XVII:
-- L'envers de la psychanalyse (1969-1970), and Seminar XIX: ...ou pire
-- (1971-1972).  No DOI is asserted for these seminars here.
--
-- The repo previously used `retroactiveSecondS2` as a compact label.  This file
-- makes the ambiguity explicit: the Frege/genesis numeral-two role and the
-- discourse-theory S2/knowledge-battery role are related historical symbols but
-- are not definitionally one construction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.TernaryRoleCarrierExact as Ternary

------------------------------------------------------------------------
-- Same printed label, distinct typed uses.
------------------------------------------------------------------------

data LacanS2Use : Set where
  fregeGenesisSecond
  discourseKnowledgeS2
  : LacanS2Use

fregeS2≠discourseS2 : fregeGenesisSecond ≡ discourseKnowledgeS2 → ⊥
fregeS2≠discourseS2 ()

data FregeGenesisRole : Set where
  zeroStart unaryCount secondCount : FregeGenesisRole

data DiscourseRole : Set where
  masterSignifierS1 knowledgeBatteryS2 dividedSubject surplusObject : DiscourseRole

fregeRole : Ternary.TernaryRoleCode → FregeGenesisRole
fregeRole Ternary.code0 = zeroStart
fregeRole Ternary.code1 = unaryCount
fregeRole Ternary.code2 = secondCount

code2IsFregeSecondCount : fregeRole Ternary.code2 ≡ secondCount
code2IsFregeSecondCount = refl

------------------------------------------------------------------------
-- Discourse S2 is deliberately not assigned to code2 by this module.
-- A future crosswalk requires a typed translation witness rather than symbol
-- matching.
------------------------------------------------------------------------

record S2TranslationWitness : Set where
  constructor s2-translation-witness
  field
    sourceUse : LacanS2Use
    targetUse : LacanS2Use
    sourceAndTargetAreDistinct : sourceUse ≡ targetUse → ⊥

canonicalS2Separation : S2TranslationWitness
canonicalS2Separation =
  s2-translation-witness fregeGenesisSecond discourseKnowledgeS2 fregeS2≠discourseS2

record LacanS2Boundary : Set where
  constructor lacan-s2-boundary
  field
    samePrintedS2MeansSameConstruction : Bool
    samePrintedS2MeansSameConstructionIsFalse :
      samePrintedS2MeansSameConstruction ≡ false
    numeralTwoIsDefinitionallyDiscourseS2 : Bool
    numeralTwoIsDefinitionallyDiscourseS2IsFalse :
      numeralTwoIsDefinitionallyDiscourseS2 ≡ false
    fregeCountChartIsFormulaOfSexuation : Bool
    fregeCountChartIsFormulaOfSexuationIsFalse :
      fregeCountChartIsFormulaOfSexuation ≡ false
    discourseS2TranslationInstalled : Bool
    discourseS2TranslationInstalledIsFalse :
      discourseS2TranslationInstalled ≡ false

canonicalLacanS2Boundary : LacanS2Boundary
canonicalLacanS2Boundary =
  lacan-s2-boundary false refl false refl false refl false refl
