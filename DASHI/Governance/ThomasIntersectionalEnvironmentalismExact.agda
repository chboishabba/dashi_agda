module DASHI.Governance.ThomasIntersectionalEnvironmentalismExact where

open import DASHI.Core.Prelude
import DASHI.Governance.EnvironmentalAuthoritySourceRegistryRound2Exact as Sources

------------------------------------------------------------------------
-- LEAH THOMAS: INTERSECTIONAL ENVIRONMENTALISM
--
-- Source: Leah Thomas, The Intersectional Environmentalist (2022),
-- ISBN-13 9780316279291.
--
-- The book is an authorial primary source for Thomas's own movement vocabulary
-- and programme.  It is not used as a controlled causal study and is not made
-- the historical owner of intersectionality as a scholarly concept.
------------------------------------------------------------------------

data EnvironmentalAxis : Set where
  ecologicalCondition socialJustice racializedExposure representation : EnvironmentalAxis

data ThomasRole : Set where
  movementFraming activistProgramme empiricalCausalLaw intersectionalityGenealogy : ThomasRole

data AuthorizedThomasUse : ThomasRole → Set where
  framingUse : AuthorizedThomasUse movementFraming
  programmeUse : AuthorizedThomasUse activistProgramme

empiricalLawNotPromoted : AuthorizedThomasUse empiricalCausalLaw → ⊥
empiricalLawNotPromoted ()

intersectionalityGenealogyNotTransferred : AuthorizedThomasUse intersectionalityGenealogy → ⊥
intersectionalityGenealogyNotTransferred ()

source : Sources.SourceReference
source = Sources.leahThomas2022

record ThomasIntersectionalEnvironmentalismBoundary : Set where
  constructor thomasIntersectionalEnvironmentalismBoundary
  field
    cleanBibliographicRecordTransfersEmpiricalAuthority : Bool
    cleanBibliographicRecordTransfersEmpiricalAuthorityIsFalse : cleanBibliographicRecordTransfersEmpiricalAuthority ≡ false
    ThomasBookSupersedesCrenshawGenealogy : Bool
    ThomasBookSupersedesCrenshawGenealogyIsFalse : ThomasBookSupersedesCrenshawGenealogy ≡ false
    movementFrameworkMayBeCitedAsThomasFramework : Bool
    movementFrameworkMayBeCitedAsThomasFrameworkIsTrue : movementFrameworkMayBeCitedAsThomasFramework ≡ true

canonicalThomasBoundary : ThomasIntersectionalEnvironmentalismBoundary
canonicalThomasBoundary = thomasIntersectionalEnvironmentalismBoundary false refl false refl true refl
