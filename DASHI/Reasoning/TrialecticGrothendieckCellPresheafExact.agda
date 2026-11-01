module DASHI.Reasoning.TrialecticGrothendieckCellPresheafExact where

------------------------------------------------------------------------
-- STRICTLY TYPED RELATIONAL CELL PRESHEAF ON THE GROTHENDIECK PATCH CATEGORY
--
-- DASHI CONTRIBUTION
--
-- The relational Grothendieck category has objects:
--
--   globalABC
--   edgeAB edgeBC edgeCA
--   vertexA vertexB vertexC
--
-- and arrows vertex -> edge -> global.
--
-- This module assigns the mature structured trialectic carriers:
--
--   F(globalABC) = compatible T^18 boundary
--   F(edge*)     = T^9 CellDialectic
--   F(vertex*)   = T^3 participant cell
--
-- contravariantly along every RelHom.  Identity and composition are proved.
-- The nontrivial composition cases around A/B/C use the boundary's explicit
-- overlap equalities, so this is not merely a constant presheaf.
--
-- This is a Set-valued presheaf-like functor on the concrete relational
-- category.  It is not yet groupoid-valued; chart-transition transport is a
-- separate enrichment layer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell

------------------------------------------------------------------------
-- 1. Object-indexed section carrier.
------------------------------------------------------------------------

Section :
  Site.RelObj →
  Set
Section Site.globalABC =
  Cell.CompatibleThreeCellTrialecticBoundary
Section Site.edgeAB =
  Cell.CellDialectic
Section Site.edgeBC =
  Cell.CellDialectic
Section Site.edgeCA =
  Cell.CellDialectic
Section Site.vertexA =
  Cell.TrialecticBasis3Cell
Section Site.vertexB =
  Cell.TrialecticBasis3Cell
Section Site.vertexC =
  Cell.TrialecticBasis3Cell

------------------------------------------------------------------------
-- 2. Contravariant restriction along every site arrow.
------------------------------------------------------------------------

restrict :
  ∀ {U V : Site.RelObj} →
  Site.RelHom U V →
  Section V →
  Section U
restrict (Site.idR U) section = section

restrict Site.abToGlobal boundary =
  Cell.edgeAB boundary
restrict Site.bcToGlobal boundary =
  Cell.edgeBC boundary
restrict Site.caToGlobal boundary =
  Cell.edgeCA boundary

restrict Site.aToAB dialectic =
  Cell.leftCell dialectic
restrict Site.bToAB dialectic =
  Cell.rightCell dialectic

restrict Site.bToBC dialectic =
  Cell.leftCell dialectic
restrict Site.cToBC dialectic =
  Cell.rightCell dialectic

restrict Site.cToCA dialectic =
  Cell.leftCell dialectic
restrict Site.aToCA dialectic =
  Cell.rightCell dialectic

-- Canonical direct global restrictions choose one representative route.
-- The alternate route is propositionally equal by the matching-family fields.
restrict Site.aToGlobal boundary =
  Cell.leftCell (Cell.edgeAB boundary)
restrict Site.bToGlobal boundary =
  Cell.rightCell (Cell.edgeAB boundary)
restrict Site.cToGlobal boundary =
  Cell.rightCell (Cell.edgeBC boundary)

------------------------------------------------------------------------
-- 3. Identity law.
------------------------------------------------------------------------

restrictIdentity :
  ∀ {U : Site.RelObj} →
  (section : Section U) →
  restrict (Site.idR U) section ≡ section
restrictIdentity section = refl

------------------------------------------------------------------------
-- 4. Composition law.
------------------------------------------------------------------------

restrictComposition :
  ∀ {U V W : Site.RelObj} →
  (g : Site.RelHom V W) →
  (f : Site.RelHom U V) →
  (section : Section W) →
  restrict (Site.composeRel g f) section
  ≡
  restrict f (restrict g section)
restrictComposition (Site.idR _) f section = refl
restrictComposition g (Site.idR _) section = refl

restrictComposition Site.abToGlobal Site.aToAB boundary = refl
restrictComposition Site.abToGlobal Site.bToAB boundary = refl
restrictComposition Site.bcToGlobal Site.bToBC boundary =
  Cell.bShared boundary
restrictComposition Site.bcToGlobal Site.cToBC boundary = refl
restrictComposition Site.caToGlobal Site.cToCA boundary =
  Cell.cShared boundary
restrictComposition Site.caToGlobal Site.aToCA boundary =
  sym (Cell.aShared boundary)

------------------------------------------------------------------------
-- 5. Alternate global routes agree exactly by overlap compatibility.
------------------------------------------------------------------------

globalAThroughAB :
  (boundary : Section Site.globalABC) →
  restrict Site.aToGlobal boundary
  ≡
  restrict Site.aToAB (restrict Site.abToGlobal boundary)
globalAThroughAB boundary = refl

globalAThroughCA :
  (boundary : Section Site.globalABC) →
  restrict Site.aToGlobal boundary
  ≡
  restrict Site.aToCA (restrict Site.caToGlobal boundary)
globalAThroughCA boundary =
  sym (Cell.aShared boundary)

globalBThroughAB :
  (boundary : Section Site.globalABC) →
  restrict Site.bToGlobal boundary
  ≡
  restrict Site.bToAB (restrict Site.abToGlobal boundary)
globalBThroughAB boundary = refl

globalBThroughBC :
  (boundary : Section Site.globalABC) →
  restrict Site.bToGlobal boundary
  ≡
  restrict Site.bToBC (restrict Site.bcToGlobal boundary)
globalBThroughBC boundary =
  Cell.bShared boundary

globalCThroughBC :
  (boundary : Section Site.globalABC) →
  restrict Site.cToGlobal boundary
  ≡
  restrict Site.cToBC (restrict Site.bcToGlobal boundary)
globalCThroughBC boundary = refl

globalCThroughCA :
  (boundary : Section Site.globalABC) →
  restrict Site.cToGlobal boundary
  ≡
  restrict Site.cToCA (restrict Site.caToGlobal boundary)
globalCThroughCA boundary =
  Cell.cShared boundary

------------------------------------------------------------------------
-- 6. Canonical section values.
------------------------------------------------------------------------

canonicalGlobalSection :
  Section Site.globalABC
canonicalGlobalSection =
  Cell.canonicalCompatibleThreeCellBoundary

canonicalABSection :
  Section Site.edgeAB
canonicalABSection =
  restrict Site.abToGlobal canonicalGlobalSection

canonicalBCSection :
  Section Site.edgeBC
canonicalBCSection =
  restrict Site.bcToGlobal canonicalGlobalSection

canonicalCASection :
  Section Site.edgeCA
canonicalCASection =
  restrict Site.caToGlobal canonicalGlobalSection

canonicalASection :
  Section Site.vertexA
canonicalASection =
  restrict Site.aToGlobal canonicalGlobalSection

canonicalBSection :
  Section Site.vertexB
canonicalBSection =
  restrict Site.bToGlobal canonicalGlobalSection

canonicalCSection :
  Section Site.vertexC
canonicalCSection =
  restrict Site.cToGlobal canonicalGlobalSection

canonicalAIsParticipantA :
  canonicalASection ≡ Cell.participantA
canonicalAIsParticipantA = refl

canonicalBIsParticipantB :
  canonicalBSection ≡ Cell.participantB
canonicalBIsParticipantB = refl

canonicalCIsParticipantC :
  canonicalCSection ≡ Cell.participantC
canonicalCIsParticipantC = refl

------------------------------------------------------------------------
-- 7. Boundary.
------------------------------------------------------------------------

data CellPresheafIsGroupoidValued : Set where
data CellPresheafAutomaticallyIncludesFaceTwoCell : Set where

cellPresheafNotYetGroupoidValued :
  CellPresheafIsGroupoidValued → ⊥
cellPresheafNotYetGroupoidValued ()

ordinaryPresheafDoesNotAutomaticallyIncludeFace :
  CellPresheafAutomaticallyIncludesFaceTwoCell → ⊥
ordinaryPresheafDoesNotAutomaticallyIncludeFace ()

record TrialecticGrothendieckCellPresheafBoundary : Set where
  constructor trialectic-grothendieck-cell-presheaf-boundary
  field
    globalObjectCarriesT18Boundary : Bool
    edgeObjectsCarryT9Dialectics : Bool
    vertexObjectsCarryT3Cells : Bool
    everySiteArrowHasRestriction : Bool
    restrictionIdentityLawProved : Bool
    restrictionCompositionLawProved : Bool
    alternateOverlapRoutesAgree : Bool
    nonconstantPresheafConstructed : Bool
    groupoidValuedPresheafConstructed : Bool
    irreducibleFaceIncludedAutomatically : Bool

canonicalTrialecticGrothendieckCellPresheafBoundary :
  TrialecticGrothendieckCellPresheafBoundary
canonicalTrialecticGrothendieckCellPresheafBoundary =
  trialectic-grothendieck-cell-presheaf-boundary
    true
    true
    true
    true
    true
    true
    true
    true
    false
    false
