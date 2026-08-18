module DASHI.Ontology.ProgenitorParentJMDPNFTests where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Ontology.ProgenitorParentHyperfabric
open import DASHI.Ontology.ProgenitorParentProjectionFibre
open import DASHI.Ontology.LeanWikidataParentingPullbackBridge
open import DASHI.Ontology.ProgenitorParentPNFPullbackLattice

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

parentFibreRestrictionRegression :
  parentEvidenceRestrictsWithoutRecoveringCarrier ≡ refl
parentFibreRestrictionRegression = refl

parentPredicateTruthBoundaryRegression :
  parentPredicateDoesNotPromoteGlobalTruth ≡ refl
parentPredicateTruthBoundaryRegression = refl

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
