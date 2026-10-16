module DASHI.Reasoning.TrialecticT27FiniteTriadicHypersheafExact where

------------------------------------------------------------------------
-- FINITE ONE-TRUNCATED HYPERSHEAF WITH COMPLETED T^27 GLOBAL GRAPH
--
-- The site topology and its strict depth do not change when the global section
-- carrier is transported through T^18 <-> CompletedT27(policy).  This owner
-- therefore combines:
--
--   * the exhaustive RelCover classifier and maximal-pullback theorems;
--   * strict site depth <= 2;
--   * completed-T27 object descent;
--   * completed-T27 wave-phase morphism descent;
--   * the already-general local phase 2-skeleton cocycle.
--
-- The result is a finite one-truncated hypersheaf for the graph-completed T^27
-- global carrier.  It does NOT promote the unconstrained ambient T^27 carrier,
-- nor an arbitrary infinity-hypercover semantics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.Base369TriTruthField as Tri
import DASHI.Foundations.StageTwelveGrothendieckRelationHyperformExact as Stage12
import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Foundations.RelationalStageTwelveSiteExact as RelSheaf
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticGrothendieckThreeCellDescentExact as OldDescent
import DASHI.Reasoning.TrialecticWavePhaseGroupoidPresheafExact as OldPhase
import DASHI.Reasoning.TrialecticWavePhaseEffectiveStackDescentExact as OldStack
import DASHI.Reasoning.TrialecticFiniteTriadicHypersheafExact as OldHyper
import DASHI.Reasoning.TrialecticRelationalSiteDepthTwoExact as Depth
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower
import DASHI.Reasoning.TrialecticT27GraphSitePresheafExact as Graph
import DASHI.Reasoning.TrialecticT27WavePhaseGroupoidPresheafExact as GraphPhase
import DASHI.Reasoning.TrialecticT27EffectiveStackDescentExact as Stack27

------------------------------------------------------------------------
-- 1. Completed-T27 hyperdescent receipt.  The topology is Set1-valued through
--    sieves, hence this receipt belongs in Set2 just like the old one.
------------------------------------------------------------------------

record T27FiniteHyperdescentReceipt
    (policy : Tower.T27CompletionPolicy) : Set₂ where
  field
    classifyCover :
      ∀ {U : Site.RelObj}
        {sieve : Stage12.Sieve Site.relationalPatchCategory U} →
      (cover : Site.RelCover sieve) →
      OldHyper.ExhaustiveCoverCase cover

    pullbackABMaximal :
      Site.RelIsMaximal
        (Stage12.pullbackSieve
          Site.relationalPatchCategory Site.abToGlobal Site.triadicRelationalSieve)
    pullbackBCMaximal :
      Site.RelIsMaximal
        (Stage12.pullbackSieve
          Site.relationalPatchCategory Site.bcToGlobal Site.triadicRelationalSieve)
    pullbackCAMaximal :
      Site.RelIsMaximal
        (Stage12.pullbackSieve
          Site.relationalPatchCategory Site.caToGlobal Site.triadicRelationalSieve)
    pullbackAMaximal :
      Site.RelIsMaximal
        (Stage12.pullbackSieve
          Site.relationalPatchCategory Site.aToGlobal Site.triadicRelationalSieve)
    pullbackBMaximal :
      Site.RelIsMaximal
        (Stage12.pullbackSieve
          Site.relationalPatchCategory Site.bToGlobal Site.triadicRelationalSieve)
    pullbackCMaximal :
      Site.RelIsMaximal
        (Stage12.pullbackSieve
          Site.relationalPatchCategory Site.cToGlobal Site.triadicRelationalSieve)

    maximalPullbackStable :
      ∀ {U V : Site.RelObj} →
      (arrow : Site.RelHom V U) →
      (sieve : Stage12.Sieve Site.relationalPatchCategory U) →
      Site.RelIsMaximal sieve →
      Site.RelIsMaximal
        (Stage12.pullbackSieve Site.relationalPatchCategory arrow sieve)

    objectDescent :
      (locals : RelSheaf.TriadicLocals Cell.CellDialectic) →
      (compatibility :
        RelSheaf.CompatibleOnTriadicCover OldDescent.cellOverlapSystem locals) →
      Stack27.GraphGlobalRealization policy locals

    morphismDescent :
      (source target : RelSheaf.TriadicLocals Cell.CellDialectic) →
      (sourceCompatibility :
        RelSheaf.CompatibleOnTriadicCover OldDescent.cellOverlapSystem source) →
      (targetCompatibility :
        RelSheaf.CompatibleOnTriadicCover OldDescent.cellOverlapSystem target) →
      OldStack.TriadicPhaseMorphisms source target →
      GraphPhase.GraphFibreHom policy
        (Stack27.globalGraph
          (Stack27.realizeCompatibleLocals policy source sourceCompatibility))
        (Stack27.globalGraph
          (Stack27.realizeCompatibleLocals policy target targetCompatibility))

    localTwoSkeletonCocycle :
      ∀ {source target : RelSheaf.TriadicLocals Cell.CellDialectic} →
      (morphisms : OldStack.TriadicPhaseMorphisms source target) →
      Tri.triAdd
        (OldPhase.equalityPhase (OldStack.morphismAB morphisms))
        (Tri.triAdd
          (OldPhase.equalityPhase (OldStack.morphismBC morphisms))
          (OldPhase.equalityPhase (OldStack.morphismCA morphisms)))
      ≡
      Tri.triAdd
        (OldPhase.equalityPhase (OldStack.morphismAB morphisms))
        (Tri.triAdd
          (OldPhase.equalityPhase (OldStack.morphismAB morphisms))
          (OldPhase.equalityPhase (OldStack.morphismAB morphisms)))

    maximalObjectIdentity :
      ∀ {U : Site.RelObj} →
      (section : Graph.GraphSection policy U) →
      Graph.graphRestrict policy (Site.idR U) section ≡ section

    maximalMorphismIdentity :
      ∀ {U : Site.RelObj}
        {x y : Graph.GraphSection policy U} →
      (hom : GraphPhase.GraphFibreHom policy x y) →
      GraphPhase.graphHomEquivalent policy
        (GraphPhase.graphRestrictHom policy (Site.idR U) hom)
        hom

    strictThreeChainsImpossible :
      ∀ {U V W X : Site.RelObj} →
      Depth.StrictRelHom W X →
      Depth.StrictRelHom V W →
      Depth.StrictRelHom U V →
      ⊥

canonicalT27FiniteHyperdescentReceipt :
  (policy : Tower.T27CompletionPolicy) →
  T27FiniteHyperdescentReceipt policy
canonicalT27FiniteHyperdescentReceipt policy = record
  { classifyCover = OldHyper.classifyEveryCover
  ; pullbackABMaximal = OldHyper.abPullbackMaximal
  ; pullbackBCMaximal = OldHyper.bcPullbackMaximal
  ; pullbackCAMaximal = OldHyper.caPullbackMaximal
  ; pullbackAMaximal = OldHyper.aPullbackMaximal
  ; pullbackBMaximal = OldHyper.bPullbackMaximal
  ; pullbackCMaximal = OldHyper.cPullbackMaximal
  ; maximalPullbackStable = OldHyper.maximalPullbacksRemainMaximal
  ; objectDescent = Stack27.realizeCompatibleLocals policy
  ; morphismDescent = Stack27.glueGraphPhaseMorphisms policy
  ; localTwoSkeletonCocycle = OldHyper.triadicTwoSkeletonCocycle
  ; maximalObjectIdentity = Graph.graphRestrictIdentity policy
  ; maximalMorphismIdentity = GraphPhase.graphRestrictIdentityHom policy
  ; strictThreeChainsImpossible = Depth.noStrictThreeArrowChain
  }

------------------------------------------------------------------------
-- 2. One certificate for every covering sieve.
------------------------------------------------------------------------

record T27CoverHyperdescentCertificate
    (policy : Tower.T27CompletionPolicy)
    {U : Site.RelObj}
    {sieve : Stage12.Sieve Site.relationalPatchCategory U}
    (cover : Site.RelCover sieve) : Set₂ where
  field
    coverCase : OldHyper.ExhaustiveCoverCase cover
    hyperdescent : T27FiniteHyperdescentReceipt policy

open T27CoverHyperdescentCertificate public

t27HyperdescentForEveryCover :
  (policy : Tower.T27CompletionPolicy) →
  ∀ {U : Site.RelObj}
    {sieve : Stage12.Sieve Site.relationalPatchCategory U} →
  (cover : Site.RelCover sieve) →
  T27CoverHyperdescentCertificate policy cover
t27HyperdescentForEveryCover policy cover = record
  { coverCase = OldHyper.classifyEveryCover cover
  ; hyperdescent = canonicalT27FiniteHyperdescentReceipt policy
  }

------------------------------------------------------------------------
-- 3. Promotion boundary.
------------------------------------------------------------------------

record TrialecticT27FiniteTriadicHypersheafBoundary : Set where
  constructor trialectic-t27-finite-triadic-hypersheaf-boundary
  field
    relationalCoverTopologyReused : Bool
    strictSiteDepthAtMostTwoReused : Bool
    completedT27ObjectHyperdescentPaid : Bool
    completedT27MorphismHyperdescentPaid : Bool
    localPhaseTwoSkeletonCocyclePaid : Bool
    everyCoverHasCompletedT27Certificate : Bool
    certifiedCompletedT27FiniteHypersheaf : Bool
    unconstrainedAmbientT27HypersheafClaimed : Bool
    certifiedArbitraryInfinityT27Hypersheaf : Bool

open TrialecticT27FiniteTriadicHypersheafBoundary public

canonicalTrialecticT27FiniteTriadicHypersheafBoundary :
  TrialecticT27FiniteTriadicHypersheafBoundary
canonicalTrialecticT27FiniteTriadicHypersheafBoundary =
  trialectic-t27-finite-triadic-hypersheaf-boundary
    true true true true true true true false false
