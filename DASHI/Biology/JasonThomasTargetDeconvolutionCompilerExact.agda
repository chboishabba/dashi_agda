module DASHI.Biology.JasonThomasTargetDeconvolutionCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- Source-shaped target-deconvolution pipeline for the STING high-content screen.

data EvidenceLayer : Set where
  primaryPhenotype miniSAR secondaryPathwayAssay chemicalProteomics geneticPerturbation resistantRescue : EvidenceLayer

data TargetCandidate : Set where MAPKAPK5 MAPKAPK2 unresolvedTarget : TargetCandidate

record TargetEvidence : Set where
  constructor target-evidence
  field
    candidate : TargetCandidate
    layer : EvidenceLayer
    observation : String
    supports : String
    cannotEstablish : String
    sourceReference : String

open TargetEvidence public

record TargetPromotionReceipt : Set where
  constructor target-promotion-receipt
  field
    phenotype : TargetEvidence
    orthogonalEvidence : TargetEvidence
    causalDiscriminator : String
    directTargetPromoted : Bool

open TargetPromotionReceipt public

record FerritinophagyMechanismReceipt : Set where
  constructor ferritinophagy-mechanism-receipt
  field
    perturbation : String
    NCOA4Behaviour : String
    ferritinBehaviour : String
    lysosomalDependence : String
    ironPhenotype : String
    sourceReference : String

open FerritinophagyMechanismReceipt public

record ThomasTargetBoundary : Set where
  constructor thomas-target-boundary
  field
    primaryPhenotypeAlonePromotesDirectTarget : Bool
    primaryPhenotypeAlonePromotesDirectTargetIsFalse : primaryPhenotypeAlonePromotesDirectTarget ≡ false
    chemicalProteomicsBindingAloneProvesEfficacyTarget : Bool
    chemicalProteomicsBindingAloneProvesEfficacyTargetIsFalse : chemicalProteomicsBindingAloneProvesEfficacyTarget ≡ false
    MAPKAPK5EvidenceExcludesMAPKAPK2 : Bool
    MAPKAPK5EvidenceExcludesMAPKAPK2IsFalse : MAPKAPK5EvidenceExcludesMAPKAPK2 ≡ false
    geneticOrRescueDiscriminatorCanPromoteCausality : Bool
    geneticOrRescueDiscriminatorCanPromoteCausalityIsTrue : geneticOrRescueDiscriminatorCanPromoteCausality ≡ true
    VPS34PerturbationMakesNCOA4DirectVPS34Substrate : Bool
    VPS34PerturbationMakesNCOA4DirectVPS34SubstrateIsFalse : VPS34PerturbationMakesNCOA4DirectVPS34Substrate ≡ false

canonicalThomasTargetBoundary : ThomasTargetBoundary
canonicalThomasTargetBoundary =
  thomas-target-boundary false refl false refl false refl true refl false refl
