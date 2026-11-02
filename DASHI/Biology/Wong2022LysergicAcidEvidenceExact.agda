{-# OPTIONS --safe #-}
module DASHI.Biology.Wong2022LysergicAcidEvidenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Sources
import DASHI.Biology.KluverLogPolar5HT2ASourceAtlasExact as KluverSources
import DASHI.Biology.Kluver5HT2AMolecularProteinInstantiationExact as Kluver
import DASHI.Biology.MonoamineBiosynthesisPathSeparationExact as Monoamine
import DASHI.Biology.Cell.OpenMetabolicNetwork as Metabolic
import DASHI.Chemistry.TransitionKernel as Chemistry

------------------------------------------------------------------------
-- WONG ET AL. (2022): ATTRIBUTED EXPERIMENTAL EVIDENCE, NOT A RECIPE
--
-- Primary source:
-- Garrett Wong, Li Rong Lim, Yong Quan Tan, Maybelle Kho Go,
-- David J. Bell, Paul S. Freemont, Wen Shan Yew (2022).
-- "Reconstituting the complete biosynthesis of D-lysergic acid in yeast".
-- Nature Communications 13:712. DOI:10.1038/s41467-022-28386-6.
--
-- Curator's scope:
-- Preserve original authorship and source-reported results; do not copy
-- strain constructs, reaction-order protocols, optimization parameters,
-- or wet-lab instructions. This is an evidence and identity crosswalk.
--
-- Existing theorem/data owners remain separate:
-- Kluver molecular/receptor evidence; Monoamine path separation;
-- generic cellular open metabolic networks; Source attribution core.
------------------------------------------------------------------------

wongEtAl2022 : Sources.AttributedSource
wongEtAl2022 =
  Sources.mkDOISource
    "Garrett Wong; Li Rong Lim; Yong Quan Tan; Maybelle Kho Go; David J. Bell; Paul S. Freemont; Wen Shan Yew"
    "Reconstituting the complete biosynthesis of D-lysergic acid in yeast"
    "Nature Communications 13:712"
    "2022"
    "10.1038/s41467-022-28386-6"
    "https://doi.org/10.1038/s41467-022-28386-6"
    Sources.academicArticleSource
    "Reports an engineered-yeast D-lysergic-acid biosynthesis proof of concept, analytical product evidence, and scale-specific endpoint titres. It does not establish industrial scalability, a quantitative flux model, receptor activation by the product, or therapeutic efficacy."
    Sources.publicAttribution

pubChemLysergicAcid : Sources.AttributedSource
pubChemLysergicAcid =
  Sources.mkNoDOISource
    "PubChem / National Center for Biotechnology Information"
    "Lysergic Acid"
    "PubChem Compound CID 6717; chemical identity record"
    "current database record"
    "https://pubchem.ncbi.nlm.nih.gov/compound/6717"
    Sources.institutionalSource
    "Identifies lysergic acid as CID 6717, formula C16H16N2O2, with a separate registry identity from lysergic acid diethylamide CID 5761. Identity does not establish provenance of an experimental specimen."
    Sources.publicAttribution

primarySourceAtlas : Sources.AttributedSourceAtlas
primarySourceAtlas =
  Sources.mkSourceAtlas
    "Wong 2022 yeast D-lysergic-acid evidence and chemical identity"
    "Wong et al. 2022 for experiment; PubChem for CID; DASHI for typed crosswalk"
    (wongEtAl2022 ∷ pubChemLysergicAcid ∷ KluverSources.pubChemLSD ∷ [])
    "Bounded paper/registry citations and read-only cross-domain evidence; no quantitative biological model, enzyme engineering or receptor-to-phenotype inference."

------------------------------------------------------------------------
-- Chemical identity and claim domain are distinct coordinates.
-- These constructors are DASHI curation tags, not a chemical proof.
------------------------------------------------------------------------

data NamedMolecule : Set where
  dLysergicAcid : NamedMolecule
  lysergicAcidDiethylamide : NamedMolecule

dLaTagDistinctFromLsdTag :
  dLysergicAcid ≡ lysergicAcidDiethylamide → ⊥
dLaTagDistinctFromLsdTag ()

data EvidenceDomain : Set where
  yeastBiosynthesisReport : EvidenceDomain
  humanReceptorStructure : EvidenceDomain
  monoamineBiosynthesis : EvidenceDomain

productionEvidenceNotReceptorEvidence :
  yeastBiosynthesisReport ≡ humanReceptorStructure → ⊥
productionEvidenceNotReceptorEvidence ()

productionEvidenceNotMonoaminePath :
  yeastBiosynthesisReport ≡ monoamineBiosynthesis → ⊥
productionEvidenceNotMonoaminePath ()

------------------------------------------------------------------------
-- Reported endpoint values: not calculated or independently replicated.
-- Strings preserve the publication's decimal representations and units.
-- There is no function that extrapolates to another vessel size.
------------------------------------------------------------------------

data ReportedScale : Set where
  oneLitreBioreactor : ReportedScale
  fourLitreBioreactor : ReportedScale

data ValidationStatus : Set where
  reportedInPrimaryPaper : ValidationStatus
  independentlyValidated : ValidationStatus

record ReportedEndpoint (scale : ReportedScale) : Set where
  constructor reportedEndpoint
  field
    source : Sources.AttributedSource
    molecularSubject : NamedMolecule
    amountAsPublished : String
    unitAsPublished : String
    evidenceStatus : ValidationStatus

oneLitreEndpoint : ReportedEndpoint oneLitreBioreactor
oneLitreEndpoint =
  reportedEndpoint
    wongEtAl2022 dLysergicAcid "1.7" "mg/L"
    reportedInPrimaryPaper

fourLitreEndpoint : ReportedEndpoint fourLitreBioreactor
fourLitreEndpoint =
  reportedEndpoint
    wongEtAl2022 dLysergicAcid "1.4" "mg/L"
    reportedInPrimaryPaper

reportedStatusNotIndependentValidation :
  reportedInPrimaryPaper ≡ independentlyValidated → ⊥
reportedStatusNotIndependentValidation ()

------------------------------------------------------------------------
-- Analytical evidence types are observational provenance, not protocols.
------------------------------------------------------------------------

data PaperEvidenceKind : Set where
  massSpectrometricIdentityComparison : PaperEvidenceKind
  stableIsotopeOriginObservation : PaperEvidenceKind
  nmrIdentityComparison : PaperEvidenceKind
  scaleSpecificEndpointMeasurement : PaperEvidenceKind

record SourceReportedEvidence : Set where
  constructor sourceReportedEvidence
  field
    evidenceKind : PaperEvidenceKind
    source : Sources.AttributedSource
    reading : String
    domain : EvidenceDomain
    status : ValidationStatus

paperIdentityEvidence : SourceReportedEvidence
paperIdentityEvidence =
  sourceReportedEvidence
    massSpectrometricIdentityComparison
    wongEtAl2022
    "Paper reports analytical comparisons supporting the identity of the fermentation product."
    yeastBiosynthesisReport
    reportedInPrimaryPaper

paperOriginEvidence : SourceReportedEvidence
paperOriginEvidence =
  sourceReportedEvidence
    stableIsotopeOriginObservation
    wongEtAl2022
    "Paper reports labelled-substrate evidence consistent with biosynthetic origin."
    yeastBiosynthesisReport
    reportedInPrimaryPaper

paperNmrEvidence : SourceReportedEvidence
paperNmrEvidence =
  sourceReportedEvidence
    nmrIdentityComparison
    wongEtAl2022
    "Paper reports an NMR comparison with the D-lysergic-acid reference."
    yeastBiosynthesisReport
    reportedInPrimaryPaper

------------------------------------------------------------------------
-- Reuse the actual existing molecular-identity and monoamine owners.
-- Linking records does not make DLA equal LSD, nor yeast metabolism
-- identical to animal serotonin synthesis, nor transfer receptor claims.
------------------------------------------------------------------------

record BoundedCrossDomainContext : Set where
  constructor boundedCrossDomainContext
  field
    productionSource : Sources.AttributedSource
    productRegistrySource : Sources.AttributedSource
    relatedLigandIdentityOwner : Kluver.MolecularIdentityReceipt
    sharedTryptophanVocabularyOwner : Monoamine.MonoamineMolecule

    sameProductAsRelatedLigand : Bool
    sameProductAsRelatedLigandIsFalse :
      sameProductAsRelatedLigand ≡ false

    receptorMechanismInferredFromFermentation : Bool
    receptorMechanismInferredFromFermentationIsFalse :
      receptorMechanismInferredFromFermentation ≡ false

    efficacyInferredFromProduction : Bool
    efficacyInferredFromProductionIsFalse :
      efficacyInferredFromProduction ≡ false

boundedCrossDomainContextReceipt : BoundedCrossDomainContext
boundedCrossDomainContextReceipt =
  boundedCrossDomainContext
    wongEtAl2022
    pubChemLysergicAcid
    Kluver.lsdIdentity
    Monoamine.tryptophan
    false refl
    false refl
    false refl

-- A future same-organism/compartment/time/units transport would require a
-- real network and independent evidence. The paper alone cannot supply it.
record UnpaidMetabolicModelBridge
    (network : Metabolic.OpenMetabolicNetwork) : Set₁ where
  field
    empiricalNetworkInstantiationPaid : Bool
    empiricalNetworkInstantiationPaidIsFalse :
      empiricalNetworkInstantiationPaid ≡ false

    absoluteFluxCalibrationPaid : Bool
    absoluteFluxCalibrationPaidIsFalse :
      absoluteFluxCalibrationPaid ≡ false

    compartmentAndTimeTransportPaid : Bool
    compartmentAndTimeTransportPaidIsFalse :
      compartmentAndTimeTransportPaid ≡ false

-- The existing generic chemistry kernel is another possible future consumer.
-- Passing that kernel does not give this paper a measured reaction network.
record UnpaidChemistryKernelBridge
    (kernel : Chemistry.ChemistryTransitionKernel) : Set where
  field
    measuredNetworkParametersPaid : Bool
    measuredNetworkParametersPaidIsFalse :
      measuredNetworkParametersPaid ≡ false

    mechanismAndObservationSameObjectPaid : Bool
    mechanismAndObservationSameObjectPaidIsFalse :
      mechanismAndObservationSameObjectPaid ≡ false

wongCitationImportsNoProof :
  Sources.citationImportsProof wongEtAl2022 ≡ false
wongCitationImportsNoProof = refl

wongAtlasCreatesNoAuthority :
  Sources.atlasCreatesAuthority primarySourceAtlas ≡ false
wongAtlasCreatesNoAuthority = refl
