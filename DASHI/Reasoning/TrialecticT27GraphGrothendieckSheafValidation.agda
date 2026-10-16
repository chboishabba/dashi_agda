module DASHI.Reasoning.TrialecticT27GraphGrothendieckSheafValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower
import DASHI.Reasoning.TrialecticT27GraphGrothendieckSheafExact as GraphSheaf
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell

policy : Tower.T27CompletionPolicy
policy = Tower.firstNine

boundary : GraphSheaf.TrialecticT27GraphGrothendieckSheafBoundary
boundary = GraphSheaf.canonicalTrialecticT27GraphGrothendieckSheafBoundary

globalCarrierPromoted : GraphSheaf.globalT18ReplacedByCompletedT27Graph boundary ≡ true
globalCarrierPromoted = refl

edgeCarrierRetained : GraphSheaf.edgeSectionsRemainT9 boundary ≡ true
edgeCarrierRetained = refl

vertexCarrierRetained : GraphSheaf.vertexSectionsRemainT3 boundary ≡ true
vertexCarrierRetained = refl

oldNewGlobalIsoPaid : GraphSheaf.completedT27GlobalIsomorphicToT18 boundary ≡ true
oldNewGlobalIsoPaid = refl

descentTransported : GraphSheaf.triadicSheafDescentTransportedToCompletedT27 boundary ≡ true
descentTransported = refl

bareAmbientT27NotPromoted : GraphSheaf.unconstrainedAmbientT27UsedAsGlobalSection boundary ≡ false
bareAmbientT27NotPromoted = refl

canonicalOldGlobal : Cell.CompatibleThreeCellTrialecticBoundary
canonicalOldGlobal = Cell.canonicalCompatibleThreeCellBoundary

canonicalNewGlobal : Tower.CompletedT27 policy
canonicalNewGlobal = GraphSheaf.boundaryToCompletedT27 policy canonicalOldGlobal

oldNewOldRoundTrip :
  GraphSheaf.completedT27ToBoundary policy canonicalNewGlobal ≡ canonicalOldGlobal
oldNewOldRoundTrip = GraphSheaf.boundaryCompletedBoundaryRoundTrip policy canonicalOldGlobal

newOldNewRoundTrip :
  GraphSheaf.boundaryToCompletedT27 policy
    (GraphSheaf.completedT27ToBoundary policy canonicalNewGlobal)
  ≡ canonicalNewGlobal
newOldNewRoundTrip = GraphSheaf.completedBoundaryCompletedRoundTrip policy canonicalNewGlobal
