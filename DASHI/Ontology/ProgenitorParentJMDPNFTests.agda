module DASHI.Ontology.ProgenitorParentJMDPNFTests where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.FibreRestrictionCore as Fibre

open import DASHI.Ontology.ProgenitorParentHyperfabric
open import DASHI.Ontology.ProgenitorParentProjectionFibre
open import DASHI.Ontology.LeanWikidataParentingPullbackBridge
open import DASHI.Ontology.LeanWikidataParentingCardinalityBoundary
open import DASHI.Ontology.LeanWikidataPullbackTopologyBoundary
open import DASHI.Ontology.ProgenitorParentPNFPullbackLattice
open import DASHI.Ontology.ProgenitorParentPredicateBaseChange
open import DASHI.Ontology.ProgenitorParentPredicatePullbackExact

jmdDonorGeneticPreservedRegression :
  jmdIsGenetic jmdDonor ≡ geneticContributor (refineJMDRole jmdDonor)
jmdDonorGeneticPreservedRegression = jmdGeneticPredicatePreserved jmdDonor

jmdAdoptiveLegalPreservedRegression :
  jmdIsLegal jmdAdoptive ≡ legalParent (refineJMDRole jmdAdoptive)
jmdAdoptiveLegalPreservedRegression = jmdLegalPredicatePreserved jmdAdoptive

jmdFlatRoleLossRegression :
  jmdRecordedAsParent jmdDonor ≡ jmdRecordedAsParent jmdAdoptive
  × genealogicalParent (refineJMDRole jmdDonor) ≡ false
  × genealogicalParent (refineJMDRole jmdAdoptive) ≡ true
jmdFlatRoleLossRegression = jmdRecordedParentProjectionIsLossy

jmdCapIsNotExactTwoRegression :
  capMeansExactlyTwo canonicalJMDGeneticCardinalityBoundary ≡ false
jmdCapIsNotExactTwoRegression = jmdCapDoesNotMeanExactlyTwo

jmdCapDoesNotSelectProfileRegression :
  capDeterminesReproductiveProfile canonicalJMDGeneticCardinalityBoundary ≡ false
jmdCapDoesNotSelectProfileRegression = jmdCapDoesNotDetermineReproductiveProfile

parentFibreRestrictionRegression :
  Fibre.doesNotRecoverCarrier parentFibreRestrictionCore ≡ true
parentFibreRestrictionRegression = parentEvidenceRestrictsWithoutRecoveringCarrier

parentPredicateTruthBoundaryRegression :
  Fibre.promotesTruth parentFibreRestrictionCore ≡ false
parentPredicateTruthBoundaryRegression = parentPredicateDoesNotPromoteGlobalTruth

cultivarPredicateFibreRegression :
  progenitorP cultivarCarrier ≡ true
  × genealogicalParentP cultivarCarrier ≡ false
cultivarPredicateFibreRegression = cultivarProgenitorDoesNotCollapseToGenealogicalParent

anonymousDonorFabricRegression :
  geneticP anonymousDonorCarrier ≡ true
  × genealogicalParentP anonymousDonorCarrier ≡ false
anonymousDonorFabricRegression = anonymousDonorSeparatesPredicateCoordinates

jmdParentPredicateFibreRegression :
  jmdRecordedAsParent jmdDonor ≡ jmdRecordedAsParent jmdAdoptive
  × geneticP anonymousDonorCarrier ≡ true
  × geneticP adoptiveCarrier ≡ false
jmdParentPredicateFibreRegression = jmdFlatParentSurfaceRefinesToDistinctFibres

pullbackBoundaryRegression :
  representationDoesNotRecoverCarrier canonicalParentPullbackSynthesis ≡ true
  × predicateDoesNotPromoteTruth canonicalParentPullbackSynthesis ≡ true
pullbackBoundaryRegression = parentPullbackKeepsProjectionBoundary

predicateBaseChangeGeneticRegression :
  geneticP (predicateCarrier (meetFibreToLeft geneticAndParentP8810)) ≡ true
predicateBaseChangeGeneticRegression = geneticAndParentForgetsToGenetic

predicateBaseChangeParentRegression :
  genealogicalParentP (predicateCarrier (meetFibreToRight geneticAndParentP8810)) ≡ true
predicateBaseChangeParentRegression = geneticAndParentForgetsToParent

exactPredicatePullbackGeneticRegression :
  geneticP (pullbackCarrier geneticParentPullbackPair) ≡ true
exactPredicatePullbackGeneticRegression = geneticParentPullbackHasGeneticWitness

exactPredicatePullbackParentRegression :
  genealogicalParentP (pullbackCarrier geneticParentPullbackPair) ≡ true
exactPredicatePullbackParentRegression = geneticParentPullbackHasParentWitness

pullbackTopologyNonCollapseRegression :
  categoricalPullbackAutomaticallyTopologicalEquivalence canonicalPullbackTopologyBoundary ≡ false
pullbackTopologyNonCollapseRegression = pullbackDoesNotCollapseSemanticTopology

pullbackComponentwiseWitnessRegression :
  componentwiseCompatibilityRequiredByPositiveTheorem canonicalPullbackTopologyBoundary ≡ true
pullbackComponentwiseWitnessRegression = componentwiseCompatibilityRemainsExplicit
