module DASHI.Reasoning.TrialecticT27GraphSitePresheafValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Reasoning.TrialecticT9T18T27GraphExtensionExact as Tower
import DASHI.Reasoning.TrialecticT27GraphSitePresheafExact as Graph

policy : Tower.T27CompletionPolicy
policy = Tower.firstNine

boundary : Graph.TrialecticT27GraphSitePresheafBoundary
boundary = Graph.canonicalTrialecticT27GraphSitePresheafBoundary

allSevenObjectsIndexed : Graph.allSevenRelObjectsIndexed boundary ≡ true
allSevenObjectsIndexed = refl

globalIsCompletedT27 : Graph.globalObjectCarriesCompletedT27 boundary ≡ true
globalIsCompletedT27 = refl

edgesRemainT9 : Graph.edgeObjectsRemainT9 boundary ≡ true
edgesRemainT9 = refl

verticesRemainT3 : Graph.vertexObjectsRemainT3 boundary ≡ true
verticesRemainT3 = refl

restrictionLawsPaid : Graph.restrictionFunctorLawsPaid boundary ≡ true
restrictionLawsPaid = refl

oldNewPointwiseEquivalencePaid : Graph.oldNewSectionEquivalencePaid boundary ≡ true
oldNewPointwiseEquivalencePaid = refl

canonicalGlobal : Graph.GraphSection policy Site.globalABC
canonicalGlobal = Graph.canonicalGraphGlobalSection policy

globalForgetRoundTrip :
  Graph.oldSectionToGraph policy Site.globalABC
    (Graph.graphSectionToOld policy Site.globalABC canonicalGlobal)
  ≡ canonicalGlobal
globalForgetRoundTrip = Graph.oldGraphOldGraphRoundTrip policy Site.globalABC canonicalGlobal

restrictionIdentity :
  Graph.graphRestrict policy (Site.idR Site.globalABC) canonicalGlobal
  ≡ canonicalGlobal
restrictionIdentity = Graph.graphRestrictIdentity policy canonicalGlobal
