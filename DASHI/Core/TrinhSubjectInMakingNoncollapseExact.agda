module DASHI.Core.TrinhSubjectInMakingNoncollapseExact where

------------------------------------------------------------------------
-- TRINH T. MINH-HA: SUBJECT-IN-THE-MAKING / CATEGORY NONCOLLAPSE
--
-- SOURCE CONTEXT
--
-- Trinh T. Minh-ha, Woman, Native, Other: Writing Postcoloniality and Feminism,
-- Indiana University Press, 1989. ISBN 9780253205032.
-- JSTOR stable book identifier: j.ctt16xwccc.
--
-- The source explicitly treats linguistic exclusion, female-identity enclosure,
-- ethnicity/womanhood duality and the subject-in-the-making.  The finite
-- nonfactorability witness below is a DASHI construction; the book title is NOT
-- promoted to an exhaustive three-element ontology.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- Coarse categorical naming can leave a subject-position residual unresolved.
------------------------------------------------------------------------

data TrinhFineState : Set where
  enclosedNamedState subjectMakingState : TrinhFineState

data PublicCategorySurface : Set where
  sameNamedCategory : PublicCategorySurface

data SubjectFormationPosition : Set where
  enclosedPosition becomingPosition : SubjectFormationPosition

publicCategory : TrinhFineState → PublicCategorySurface
publicCategory enclosedNamedState = sameNamedCategory
publicCategory subjectMakingState = sameNamedCategory

subjectFormation : TrinhFineState → SubjectFormationPosition
subjectFormation enclosedNamedState = enclosedPosition
subjectFormation subjectMakingState = becomingPosition

subjectFormationDistinct :
  subjectFormation enclosedNamedState ≡ subjectFormation subjectMakingState → ⊥
subjectFormationDistinct ()

publicCategoryCannotRecoverSubjectFormation :
  INF.FactorsThrough publicCategory subjectFormation → ⊥
publicCategoryCannotRecoverSubjectFormation =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      enclosedNamedState subjectMakingState refl subjectFormationDistinct)

------------------------------------------------------------------------
-- Title terms are source-visible positions, not a closed numeric carrier.
------------------------------------------------------------------------

data TitlePosition : Set where
  womanTitlePosition nativeTitlePosition otherTitlePosition : TitlePosition

record TrinhNoncollapseBoundary : Set where
  constructor trinh-noncollapse-boundary
  field
    womanNativeOtherIsExhaustiveTernaryOntology : Bool
    womanNativeOtherIsExhaustiveTernaryOntologyIsFalse :
      womanNativeOtherIsExhaustiveTernaryOntology ≡ false
    titlePositionDeterminesSubjectFormation : Bool
    titlePositionDeterminesSubjectFormationIsFalse :
      titlePositionDeterminesSubjectFormation ≡ false
    linguisticVisibilityEqualsOriginatingSubjecthood : Bool
    linguisticVisibilityEqualsOriginatingSubjecthoodIsFalse :
      linguisticVisibilityEqualsOriginatingSubjecthood ≡ false
    trinhSubjectMakingEqualsIrigarayNeither : Bool
    trinhSubjectMakingEqualsIrigarayNeitherIsFalse :
      trinhSubjectMakingEqualsIrigarayNeither ≡ false
    finiteNonfactorabilityProvesPostcolonialTheory : Bool
    finiteNonfactorabilityProvesPostcolonialTheoryIsFalse :
      finiteNonfactorabilityProvesPostcolonialTheory ≡ false

canonicalTrinhNoncollapseBoundary : TrinhNoncollapseBoundary
canonicalTrinhNoncollapseBoundary =
  trinh-noncollapse-boundary false refl false refl false refl false refl false refl
