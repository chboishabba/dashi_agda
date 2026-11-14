module DASHI.Reasoning.TrialecticT27Universal369HandoffExact where

------------------------------------------------------------------------
-- GUARDED HANDOFF: COMPLETED T^27 GRAPH <-> CANONICAL PNF/369 SURFACE
--
-- Master already owns PNFHyperfabric369Surface, including a canonical
-- dialecticDiscussionAtom27 with dimension 27 and a hard external-theorem
-- non-promotion boundary.  The local trialectic programme now independently
-- owns an ambient T^27 coordinate carrier and policy-completed T^27 graph.
--
-- This module records the strongest honest handoff between those owners:
-- both exact 27-shape receipts are retained beside one concrete completed
-- graph section.  No coordinate isomorphism between the PNF atom and the
-- trialectic T^27 carrier is fabricated from cardinality, and no physical
-- same-object claim follows.
--
-- Sibling TOE PR #1217 motivates a future SectorRealization consumer with an
-- explicit validation grade and unpaid obligations.  That sibling interface
-- remains sibling formal source/provenance only: it is not copied here and its
-- declarations are not imported as local theorem authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Interop.PNFHyperfabric369 as PNF369
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower

------------------------------------------------------------------------
-- 1. Independent exact 27-shape receipts.
------------------------------------------------------------------------

canonical369Surface : PNF369.PNFHyperfabric369Surface
canonical369Surface = PNF369.canonicalPNFHyperfabric369Surface

canonical369AtomIsTwentySeven :
  PNF369.dialecticAtom canonical369Surface ≡ 27
canonical369AtomIsTwentySeven =
  PNF369.dialecticAtomIsTwentySeven canonical369Surface

trialecticAmbientIsTwentySeven :
  Tower.t27CoordinateCount ≡ 27
trialecticAmbientIsTwentySeven = Tower.t27CoordinateCountIsTwentySeven

canonical369AtomDoesNotPromoteExternalTheorem :
  PNF369.externalTheoremPromotion
    canonical369Surface
    PNF369.dialecticDiscussionAtom27
  ≡ false
canonical369AtomDoesNotPromoteExternalTheorem =
  PNF369.externalTheoremPromotionIsFalse
    canonical369Surface
    PNF369.dialecticDiscussionAtom27

------------------------------------------------------------------------
-- 2. One concrete T^18 source fixture and its policy-completed graph.
------------------------------------------------------------------------

canonicalT18 : Tower.T18Coordinates
canonicalT18 =
  Tower.compatibleBoundaryToT18 Cell.canonicalCompatibleThreeCellBoundary

canonicalCompletedT27 :
  (policy : Tower.T27CompletionPolicy) →
  Tower.CompletedT27 policy
canonicalCompletedT27 policy =
  Tower.completedT27FromT18 policy canonicalT18

------------------------------------------------------------------------
-- 3. Paired handoff receipt.  This is intentionally weaker than an
--    equivalence/isomorphism between the two 27-shaped carriers.
------------------------------------------------------------------------

record Universal369T27Handoff
    (policy : Tower.T27CompletionPolicy) : Set₁ where
  constructor universal-369-t27-handoff
  field
    hyperfabricSurface : PNF369.PNFHyperfabric369Surface
    hyperfabricSurfaceIsCanonical :
      hyperfabricSurface ≡ PNF369.canonicalPNFHyperfabric369Surface

    completedGraph : Tower.CompletedT27 policy
    ambientGraph : Tower.T27Coordinates
    ambientGraphIsCompletedCube :
      ambientGraph ≡ Tower.completedCube completedGraph

    hyperfabricAtomCountIsTwentySeven :
      PNF369.dialecticAtom hyperfabricSurface ≡ 27
    trialecticAmbientCountIsTwentySeven :
      Tower.t27CoordinateCount ≡ 27

    completedGraphProjectsToFreeT18 :
      Tower.projectT18 ambientGraph ≡ Tower.freeT18 completedGraph

    hyperfabricAtomExternalPromotionIsFalse :
      PNF369.externalTheoremPromotion
        hyperfabricSurface
        PNF369.dialecticDiscussionAtom27
      ≡ false

open Universal369T27Handoff public

canonicalUniversal369T27Handoff :
  (policy : Tower.T27CompletionPolicy) →
  Universal369T27Handoff policy
canonicalUniversal369T27Handoff policy =
  universal-369-t27-handoff
    canonical369Surface
    refl
    (canonicalCompletedT27 policy)
    (Tower.completedCube (canonicalCompletedT27 policy))
    refl
    canonical369AtomIsTwentySeven
    trialecticAmbientIsTwentySeven
    (Tower.completedT27ProjectsExactly (canonicalCompletedT27 policy))
    canonical369AtomDoesNotPromoteExternalTheorem

------------------------------------------------------------------------
-- 4. Explicit non-promotion tokens.  A shared count/role surface is useful for
--    routing and future realization adapters, but it is not a same-object map.
------------------------------------------------------------------------

data PNFAtomCoordinateIsomorphismPaid : Set where
data SharedTwentySevenShapePromotesPhysicalSameObject : Set where

noPNFAtomCoordinateIsomorphismFromShapeAlone :
  PNFAtomCoordinateIsomorphismPaid → ⊥
noPNFAtomCoordinateIsomorphismFromShapeAlone ()

noPhysicalSameObjectFromSharedTwentySevenShape :
  SharedTwentySevenShapePromotesPhysicalSameObject → ⊥
noPhysicalSameObjectFromSharedTwentySevenShape ()

------------------------------------------------------------------------
-- 5. Promotion / attribution boundary.
------------------------------------------------------------------------

record TrialecticT27Universal369HandoffBoundary : Set where
  constructor trialectic-t27-universal-369-handoff-boundary
  field
    canonicalPNF369SurfaceReused : Bool
    twentySevenShapeAlignmentPaid : Bool
    completedGraphEmbedsInAmbientT27 : Bool
    completedGraphRetainsT18Projection : Bool
    pnfAtomCoordinateIsomorphismPaid : Bool
    sharedTwentySevenShapePromotesPhysicalSameObject : Bool
    pnfSurfaceExternalTheoremPromotionRemainsFalse : Bool
    toeSiblingSectorRealizationImportedAsLocalAuthority : Bool

open TrialecticT27Universal369HandoffBoundary public

canonicalTrialecticT27Universal369HandoffBoundary :
  TrialecticT27Universal369HandoffBoundary
canonicalTrialecticT27Universal369HandoffBoundary =
  trialectic-t27-universal-369-handoff-boundary
    true true true true false false true false
