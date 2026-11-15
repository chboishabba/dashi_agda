module DASHI.Philosophy.NonginCurrentMaxCutT27Exact where

------------------------------------------------------------------------
-- CURRENT NONGIN MAX-CUT: T^27 GRAPH PROMOTION
--
-- This additive status owner supersedes the older T^18-terminal reading without
-- rewriting its compatibility record.  Recent sibling work motivated the cut:
--
--   * torque/right-hand-rule work reuses the nested T^9/T^18 trialectic spine;
--   * IIT cube work later pays a concrete 27-coordinate image-as-two-face-graph
--     theorem.
--
-- Those sibling PRs are archaeology/provenance here, not silently imported
-- theorem authority.  The actual theorem authority below is the generic DASHI
-- graph extension and its independently constructed sheaf/groupoid/descent
-- owners on this branch.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Philosophy.NonginCurrentMaxCutExact as Previous
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower
import DASHI.Reasoning.TrialecticT27GraphGrothendieckSheafExact as GraphSheaf
import DASHI.Reasoning.TrialecticT27GraphSitePresheafExact as GraphPresheaf
import DASHI.Reasoning.TrialecticT27WavePhaseGroupoidPresheafExact as GraphGroupoid
import DASHI.Reasoning.TrialecticT27EffectiveStackDescentExact as GraphStack
import DASHI.Reasoning.TrialecticT27WavePhaseHigherStackExact as GraphHigher
import DASHI.Reasoning.TrialecticT27FiniteTriadicHypersheafExact as GraphHyper

previousBoundary : Previous.NonginCurrentMaxCutBoundary
previousBoundary = Previous.canonicalNonginCurrentMaxCutBoundary

towerBoundary : Tower.TrialecticT9T18T27GraphExtensionBoundary
towerBoundary = Tower.canonicalTrialecticT9T18T27GraphExtensionBoundary

graphSheafBoundary : GraphSheaf.TrialecticT27GraphGrothendieckSheafBoundary
graphSheafBoundary = GraphSheaf.canonicalTrialecticT27GraphGrothendieckSheafBoundary

graphPresheafBoundary : GraphPresheaf.TrialecticT27GraphSitePresheafBoundary
graphPresheafBoundary = GraphPresheaf.canonicalTrialecticT27GraphSitePresheafBoundary

graphGroupoidBoundary : GraphGroupoid.TrialecticT27WavePhaseGroupoidPresheafBoundary
graphGroupoidBoundary = GraphGroupoid.canonicalTrialecticT27WavePhaseGroupoidPresheafBoundary

graphStackBoundary : GraphStack.TrialecticT27EffectiveStackBoundary
graphStackBoundary = GraphStack.canonicalTrialecticT27EffectiveStackBoundary

graphHigherBoundary : GraphHigher.TrialecticT27WavePhaseHigherStackBoundary
graphHigherBoundary = GraphHigher.canonicalTrialecticT27WavePhaseHigherStackBoundary

graphHyperBoundary : GraphHyper.TrialecticT27FiniteTriadicHypersheafBoundary
graphHyperBoundary = GraphHyper.canonicalTrialecticT27FiniteTriadicHypersheafBoundary

------------------------------------------------------------------------
-- Exact receipts from the new carrier ladder.
------------------------------------------------------------------------

t9ToT18ToT27Receipt :
  Tower.t18GraphCompletesToT27GivenPolicy towerBoundary ≡ true
t9ToT18ToT27Receipt = refl

completedGraphHasT18FreeDataReceipt :
  Tower.completedT27HasT18FreeData towerBoundary ≡ true
completedGraphHasT18FreeDataReceipt = refl

bareT18DoesNotChooseThirdFace :
  Tower.t18AloneDeterminesCanonicalT27 towerBoundary ≡ false
bareT18DoesNotChooseThirdFace = refl

completedGlobalEquivalentReceipt :
  GraphSheaf.completedT27GlobalIsomorphicToT18 graphSheafBoundary ≡ true
completedGlobalEquivalentReceipt = refl

completedGlobalSheafReceipt :
  GraphSheaf.triadicSheafDescentTransportedToCompletedT27 graphSheafBoundary ≡ true
completedGlobalSheafReceipt = refl

completedFullSitePresheafReceipt :
  GraphPresheaf.oldNewSectionEquivalencePaid graphPresheafBoundary ≡ true
completedFullSitePresheafReceipt = refl

completedWavePhaseGroupoidReceipt :
  GraphGroupoid.globalCompletedT27CarriesPhaseGroupoid graphGroupoidBoundary ≡ true
completedWavePhaseGroupoidReceipt = refl

completedEffectiveStackReceipt :
  GraphStack.completedT27MorphismDescentPaid graphStackBoundary ≡ true
completedEffectiveStackReceipt = refl

completedHigherStackReceipt :
  GraphHigher.certifiedCompletedT27HigherStack graphHigherBoundary ≡ true
completedHigherStackReceipt = refl

completedFiniteHypersheafReceipt :
  GraphHyper.certifiedCompletedT27FiniteHypersheaf graphHyperBoundary ≡ true
completedFiniteHypersheafReceipt = refl

ambientT27StillNotPromoted :
  GraphHyper.unconstrainedAmbientT27HypersheafClaimed graphHyperBoundary ≡ false
ambientT27StillNotPromoted = refl

arbitraryInfinityT27StillSeparate :
  GraphHyper.certifiedArbitraryInfinityT27Hypersheaf graphHyperBoundary ≡ false
arbitraryInfinityT27StillSeparate = refl

------------------------------------------------------------------------
-- Current status.
------------------------------------------------------------------------

record NonginCurrentMaxCutT27Boundary : Set where
  constructor nongin-current-max-cut-t27-boundary
  field
    previousNonginMaxCutRetained : Bool
    t9T18T27GraphExtensionPaid : Bool
    completedT27GlobalEquivalentToT18 : Bool
    completedT27GrothendieckSheafPaid : Bool
    completedT27FullSitePresheafPaid : Bool
    completedT27WavePhaseGroupoidPaid : Bool
    completedT27EffectiveStackPaid : Bool
    completedT27HigherStackPaid : Bool
    completedT27FiniteHypersheafPaid : Bool
    completedT27FreeDataIsT18 : Bool
    bareT18DeterminesCanonicalT27 : Bool
    unconstrainedAmbientT27Promoted : Bool
    siblingPRTheoremAuthorityImportedByProse : Bool
    arbitraryInfinityT27HypersheafPaid : Bool

open NonginCurrentMaxCutT27Boundary public

canonicalNonginCurrentMaxCutT27Boundary : NonginCurrentMaxCutT27Boundary
canonicalNonginCurrentMaxCutT27Boundary =
  nongin-current-max-cut-t27-boundary
    true
    true
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
    false
    false
