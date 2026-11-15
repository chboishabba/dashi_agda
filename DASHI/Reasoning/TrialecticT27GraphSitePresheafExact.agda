module DASHI.Reasoning.TrialecticT27GraphSitePresheafExact where

------------------------------------------------------------------------
-- FULL RELATIONAL-SITE PRESHEAF WITH COMPLETED T^27 GLOBAL SECTION
--
-- Transport the mature nonconstant T^18/T^9/T^3 presheaf through the exact
-- T^18 <-> CompletedT27(policy) global equivalence.  Nothing changes locally:
--
--   globalABC : CompletedT27 policy
--   edge*     : CellDialectic = T^9
--   vertex*   : TrialecticBasis3Cell = T^3
--
-- The third T^9 face at global level is policy-determined.  This owner therefore
-- does not replace the old information content by 27 independent coordinates.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Reasoning.TrialecticGrothendieckCellPresheafExact as Old
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower
import DASHI.Reasoning.TrialecticT27GraphGrothendieckSheafExact as GraphSheaf

------------------------------------------------------------------------
-- 1. Object-indexed carrier.
------------------------------------------------------------------------

GraphSection :
  Tower.T27CompletionPolicy →
  Site.RelObj →
  Set
GraphSection policy Site.globalABC = Tower.CompletedT27 policy
GraphSection policy Site.edgeAB = Cell.CellDialectic
GraphSection policy Site.edgeBC = Cell.CellDialectic
GraphSection policy Site.edgeCA = Cell.CellDialectic
GraphSection policy Site.vertexA = Cell.TrialecticBasis3Cell
GraphSection policy Site.vertexB = Cell.TrialecticBasis3Cell
GraphSection policy Site.vertexC = Cell.TrialecticBasis3Cell

------------------------------------------------------------------------
-- 2. Pointwise equivalence with the old section family.  Only globalABC is
--    nontrivial; every edge/vertex carrier is literally unchanged.
------------------------------------------------------------------------

graphSectionToOld :
  (policy : Tower.T27CompletionPolicy) →
  (U : Site.RelObj) →
  GraphSection policy U →
  Old.Section U
graphSectionToOld policy Site.globalABC section =
  GraphSheaf.completedT27ToBoundary policy section
graphSectionToOld policy Site.edgeAB section = section
graphSectionToOld policy Site.edgeBC section = section
graphSectionToOld policy Site.edgeCA section = section
graphSectionToOld policy Site.vertexA section = section
graphSectionToOld policy Site.vertexB section = section
graphSectionToOld policy Site.vertexC section = section

oldSectionToGraph :
  (policy : Tower.T27CompletionPolicy) →
  (U : Site.RelObj) →
  Old.Section U →
  GraphSection policy U
oldSectionToGraph policy Site.globalABC section =
  GraphSheaf.boundaryToCompletedT27 policy section
oldSectionToGraph policy Site.edgeAB section = section
oldSectionToGraph policy Site.edgeBC section = section
oldSectionToGraph policy Site.edgeCA section = section
oldSectionToGraph policy Site.vertexA section = section
oldSectionToGraph policy Site.vertexB section = section
oldSectionToGraph policy Site.vertexC section = section

oldGraphOldGraphRoundTrip :
  (policy : Tower.T27CompletionPolicy) →
  (U : Site.RelObj) →
  (section : GraphSection policy U) →
  oldSectionToGraph policy U (graphSectionToOld policy U section) ≡ section
oldGraphOldGraphRoundTrip policy Site.globalABC section =
  GraphSheaf.completedBoundaryCompletedRoundTrip policy section
oldGraphOldGraphRoundTrip policy Site.edgeAB section = refl
oldGraphOldGraphRoundTrip policy Site.edgeBC section = refl
oldGraphOldGraphRoundTrip policy Site.edgeCA section = refl
oldGraphOldGraphRoundTrip policy Site.vertexA section = refl
oldGraphOldGraphRoundTrip policy Site.vertexB section = refl
oldGraphOldGraphRoundTrip policy Site.vertexC section = refl

graphOldGraphOldRoundTrip :
  (policy : Tower.T27CompletionPolicy) →
  (U : Site.RelObj) →
  (section : Old.Section U) →
  graphSectionToOld policy U (oldSectionToGraph policy U section) ≡ section
graphOldGraphOldRoundTrip policy Site.globalABC section =
  GraphSheaf.boundaryCompletedBoundaryRoundTrip policy section
graphOldGraphOldRoundTrip policy Site.edgeAB section = refl
graphOldGraphOldRoundTrip policy Site.edgeBC section = refl
graphOldGraphOldRoundTrip policy Site.edgeCA section = refl
graphOldGraphOldRoundTrip policy Site.vertexA section = refl
graphOldGraphOldRoundTrip policy Site.vertexB section = refl
graphOldGraphOldRoundTrip policy Site.vertexC section = refl

------------------------------------------------------------------------
-- 3. Contravariant restrictions.  At every arrow we forget to the old exact
--    payload, use the established restriction, and observe that the target is
--    already an unchanged local carrier.
------------------------------------------------------------------------

graphRestrict :
  (policy : Tower.T27CompletionPolicy) →
  ∀ {U V : Site.RelObj} →
  Site.RelHom U V →
  GraphSection policy V →
  GraphSection policy U
graphRestrict policy (Site.idR U) section = section

graphRestrict policy Site.abToGlobal section =
  Old.restrict Site.abToGlobal
    (graphSectionToOld policy Site.globalABC section)
graphRestrict policy Site.bcToGlobal section =
  Old.restrict Site.bcToGlobal
    (graphSectionToOld policy Site.globalABC section)
graphRestrict policy Site.caToGlobal section =
  Old.restrict Site.caToGlobal
    (graphSectionToOld policy Site.globalABC section)

graphRestrict policy Site.aToAB section = Old.restrict Site.aToAB section
graphRestrict policy Site.bToAB section = Old.restrict Site.bToAB section
graphRestrict policy Site.bToBC section = Old.restrict Site.bToBC section
graphRestrict policy Site.cToBC section = Old.restrict Site.cToBC section
graphRestrict policy Site.cToCA section = Old.restrict Site.cToCA section
graphRestrict policy Site.aToCA section = Old.restrict Site.aToCA section

graphRestrict policy Site.aToGlobal section =
  Old.restrict Site.aToGlobal
    (graphSectionToOld policy Site.globalABC section)
graphRestrict policy Site.bToGlobal section =
  Old.restrict Site.bToGlobal
    (graphSectionToOld policy Site.globalABC section)
graphRestrict policy Site.cToGlobal section =
  Old.restrict Site.cToGlobal
    (graphSectionToOld policy Site.globalABC section)

------------------------------------------------------------------------
-- 4. Functor laws.  The only nontrivial composites are vertex -> edge ->
--    global, and they are exactly the already-proved old restriction squares.
------------------------------------------------------------------------

graphRestrictIdentity :
  (policy : Tower.T27CompletionPolicy) →
  ∀ {U : Site.RelObj} →
  (section : GraphSection policy U) →
  graphRestrict policy (Site.idR U) section ≡ section
graphRestrictIdentity policy section = refl

graphRestrictComposition :
  (policy : Tower.T27CompletionPolicy) →
  ∀ {U V W : Site.RelObj} →
  (g : Site.RelHom V W) →
  (f : Site.RelHom U V) →
  (section : GraphSection policy W) →
  graphRestrict policy (Site.composeRel g f) section
  ≡ graphRestrict policy f (graphRestrict policy g section)
graphRestrictComposition policy (Site.idR _) f section = refl
graphRestrictComposition policy g (Site.idR _) section = refl

graphRestrictComposition policy Site.abToGlobal Site.aToAB section =
  Old.restrictComposition Site.abToGlobal Site.aToAB
    (graphSectionToOld policy Site.globalABC section)
graphRestrictComposition policy Site.abToGlobal Site.bToAB section =
  Old.restrictComposition Site.abToGlobal Site.bToAB
    (graphSectionToOld policy Site.globalABC section)
graphRestrictComposition policy Site.bcToGlobal Site.bToBC section =
  Old.restrictComposition Site.bcToGlobal Site.bToBC
    (graphSectionToOld policy Site.globalABC section)
graphRestrictComposition policy Site.bcToGlobal Site.cToBC section =
  Old.restrictComposition Site.bcToGlobal Site.cToBC
    (graphSectionToOld policy Site.globalABC section)
graphRestrictComposition policy Site.caToGlobal Site.cToCA section =
  Old.restrictComposition Site.caToGlobal Site.cToCA
    (graphSectionToOld policy Site.globalABC section)
graphRestrictComposition policy Site.caToGlobal Site.aToCA section =
  Old.restrictComposition Site.caToGlobal Site.aToCA
    (graphSectionToOld policy Site.globalABC section)

------------------------------------------------------------------------
-- 5. Canonical values.
------------------------------------------------------------------------

canonicalGraphGlobalSection :
  (policy : Tower.T27CompletionPolicy) →
  GraphSection policy Site.globalABC
canonicalGraphGlobalSection policy =
  oldSectionToGraph policy Site.globalABC Old.canonicalGlobalSection

canonicalGraphABSection :
  (policy : Tower.T27CompletionPolicy) →
  GraphSection policy Site.edgeAB
canonicalGraphABSection policy =
  graphRestrict policy Site.abToGlobal (canonicalGraphGlobalSection policy)

canonicalGraphBCSection :
  (policy : Tower.T27CompletionPolicy) →
  GraphSection policy Site.edgeBC
canonicalGraphBCSection policy =
  graphRestrict policy Site.bcToGlobal (canonicalGraphGlobalSection policy)

canonicalGraphCASection :
  (policy : Tower.T27CompletionPolicy) →
  GraphSection policy Site.edgeCA
canonicalGraphCASection policy =
  graphRestrict policy Site.caToGlobal (canonicalGraphGlobalSection policy)

------------------------------------------------------------------------
-- 6. Boundary.
------------------------------------------------------------------------

record TrialecticT27GraphSitePresheafBoundary : Set where
  constructor trialectic-t27-graph-site-presheaf-boundary
  field
    allSevenRelObjectsIndexed : Bool
    globalObjectCarriesCompletedT27 : Bool
    edgeObjectsRemainT9 : Bool
    vertexObjectsRemainT3 : Bool
    everySiteArrowHasRestriction : Bool
    restrictionFunctorLawsPaid : Bool
    oldNewSectionEquivalencePaid : Bool
    unconstrainedAmbientT27UsedGlobally : Bool

open TrialecticT27GraphSitePresheafBoundary public

canonicalTrialecticT27GraphSitePresheafBoundary :
  TrialecticT27GraphSitePresheafBoundary
canonicalTrialecticT27GraphSitePresheafBoundary =
  trialectic-t27-graph-site-presheaf-boundary
    true true true true true true true false
