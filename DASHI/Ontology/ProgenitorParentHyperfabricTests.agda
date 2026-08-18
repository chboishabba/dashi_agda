module DASHI.Ontology.ProgenitorParentHyperfabricTests where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)

open import DASHI.Ontology.ProgenitorParentHyperfabric
open import DASHI.Ontology.ProgenitorParentProjectionFibre
open import DASHI.Ontology.ProgenitorParentEthicsExamples

causalInputRegression :
  participatesCausally incubatorInput ≡ true
  × lineageBearing incubatorInput ≡ false
causalInputRegression = causalInputDoesNotImplyProgenitor

triparentalRegression :
  progenitorCount triparentalPlantGeneration ≡ suc (suc (suc zero))
triparentalRegression = triparentalPlantHasThreeContributors

anonymousIVFRegression :
  geneticContributor anonymousIVFDonor ≡ true
  × genealogicalParent anonymousIVFDonor ≡ false
anonymousIVFRegression = geneticContributionCannotDetermineParenthood

adoptionRegression :
  genealogicalParent adoptiveParent ≡ true
  × geneticContributor adoptiveParent ≡ false
adoptionRegression = parenthoodCannotDetermineGeneticContribution

surrogacyRegression :
  gestationalContributor gestationalSurrogateOnly ≡ true
  × genealogicalParent gestationalSurrogateOnly ≡ false
surrogacyRegression = gestationCannotDetermineParenthood

mitochondrialRegression :
  mitochondrialContributor mitochondrialDonor ≡ true
  × genealogicalParent mitochondrialDonor ≡ false
mitochondrialRegression = mitochondrialContributionCannotDetermineParenthood

cultivarProjectionRegression :
  recommendedGenericSlot lineageLevel ≡ hybridOfP1531
cultivarProjectionRegression = cultivarConflictIsRepresentationRestriction

cultivarProgenitorNotParentRegression :
  projectParentSlot cultivarCarrier ≡ hybridOfP1531
  × progenitorRelation (carrierRelation cultivarCarrier) ≡ true
  × genealogicalParent (carrierRelation cultivarCarrier) ≡ false
cultivarProgenitorNotParentRegression =
  p1531SpecializationPreservesProgenitorCoordinate

fictionalCellRegression :
  surfaceType fictionalSentientCellParent ≡ surfaceType ordinaryNonParentCell
  × genealogicalParent (relation fictionalSentientCellParent) ≡ true
  × genealogicalParent (relation ordinaryNonParentCell) ≡ false
fictionalCellRegression = entityTypeDoesNotDetermineParentEligibility

slotNonCollapseRegression :
  slot anonymousDonorP8810Surface ≡ slot adoptiveP8810Surface
  × geneticContributor (relation anonymousDonorP8810Surface) ≡ true
  × geneticContributor (relation adoptiveP8810Surface) ≡ false
slotNonCollapseRegression = wikidataParentSlotDoesNotDetermineParentSemantics

oneParentTwoGeneticsRegression :
  familyParentCount singleMotherAnonymousDonorCase ≡ suc zero
  × familyGeneticContributorCount singleMotherAnonymousDonorCase ≡ suc (suc zero)
oneParentTwoGeneticsRegression = oneParentTwoGeneticContributors

ethicalBoundaryRegression :
  geneticContributionConfersParenthood canonicalParentOntologyBoundary ≡ false
ethicalBoundaryRegression = refl
