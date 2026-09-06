module DASHI.Culture.MissingDeceasedFullApplicationTransformationAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- FULL MEMORIAL APPLICATION-TRANSFORMATION ATLAS
--
-- Same rubric across the memorial/investigation set.  This atlas does not infer
-- event causation.  It identifies what transformed public/general science into
-- an operational capability and which evidence leaves remain open.
------------------------------------------------------------------------

data AtlasStatus : Set where
  atlasSourceBacked
  atlasPartial
  atlasNotLocated
  atlasNotApplicable
  : AtlasStatus

record ApplicationAtlasRow : Set where
  constructor application-atlas-row
  field
    person : String
    scientificFoundation : String
    applicationTransformation : String
    publicFoundationStatus : AtlasStatus
    applicationRoleStatus : AtlasStatus
    nonPublicResidualStatus : AtlasStatus
    successionStatus : AtlasStatus
    observerSurfaceStatus : AtlasStatus
    eventLinkStatus : AtlasStatus
    sourceReference : String
    boundedReading : String

open ApplicationAtlasRow public

amyEskridgeRow : ApplicationAtlasRow
amyEskridgeRow = application-atlas-row
  "Amy Eskridge"
  "POAMS-adjacent anomalous-force / gravity-modification theory and experimental claims"
  "apparatus geometry + calibration + operating window + data reduction + validation + Institute-derived maturation"
  atlasSourceBacked atlasPartial atlasPartial atlasNotLocated atlasPartial atlasNotLocated
  "NASA/TM-20205010911; captured September 2020 Eskridge release-review statement; AmyEskridgeApplicationTransformationExact"
  "Public/report-level foundation exists and private maturation was self-reported; the exact Institute derivative, application stack and handover remain unresolved."

nunoLoureiroRow : ApplicationAtlasRow
nunoLoureiroRow = application-atlas-row
  "Nuno F. G. Loureiro"
  "KREHM/KRMHD, tearing/reconnection, Fourier-Hermite reduced kinetic plasma models"
  "target-regime ordering + closure/dissipation + numerical resolution + initial/boundary conditions + validation + implementation workflow"
  atlasSourceBacked atlasSourceBacked atlasPartial atlasPartial atlasSourceBacked atlasNotLocated
  "Loureiro et al. CPC 206 (2016) DOI 10.1016/j.cpc.2016.05.004; existing Loureiro/Viriato owners"
  "Much of the mathematics and numerical architecture is public.  The discriminating residual is application-specific configuration, validation and unpublished workflow, not the governing equations themselves."

frankMaiwaldRow : ApplicationAtlasRow
frankMaiwaldRow = application-atlas-row
  "Frank W. Maiwald"
  "cryogenic ion/action spectroscopy; planetary/instrument engineering and qualification"
  "apparatus calibration + trap/tag configuration + response functions + process qualification + instrument integration + failure history"
  atlasSourceBacked atlasSourceBacked atlasPartial atlasNotLocated atlasPartial atlasNotLocated
  "JPL SURP SP23012p; JPL instrument/qualification memorial records; existing Maiwald spectroscopy owners"
  "The generic spectroscopy protocol is public; apparatus-specific calibration, qualification and integration know-how are the more reconstructive carriers."

williamMcCaslandRow : ApplicationAtlasRow
williamMcCaslandRow = application-atlas-row
  "William Neil McCasland"
  "space systems, GPS, space-based laser, AFRL technology development, flexible-structure/control programme experience"
  "system architecture + technology selection + control/placement design + integration + programme judgement + configuration/failure knowledge"
  atlasSourceBacked atlasPartial atlasPartial atlasNotLocated atlasPartial atlasNotLocated
  "USAF biography; Applied Technology Associates profile; existing McCasland control/Gramian programme owners"
  "The current record supports broad application/programme expertise but not one event-time application carrier with closed possession and succession."

carlGrillmairRow : ApplicationAtlasRow
carlGrillmairRow = application-atlas-row
  "Carl J. Grillmair"
  "stellar-stream matched filtering, orbit inference, infrared survey/NEOWISE data processing and NEO Surveyor validation"
  "survey-pipeline QA + matched-filter tuning + projection/distance scans + instrument-performance validation + anomaly diagnosis"
  atlasSourceBacked atlasSourceBacked atlasPartial atlasNotLocated atlasSourceBacked atlasSourceBacked
  "Grillmair 2017 DOI 10.3847/1538-4357/aa8872; Caltech/IPAC memorial; law-enforcement/DA homicide reporting"
  "Technically deep application work exists, but a charged local suspect/crime sequence is independently established and no scientific-work motive is established; this is an important causal negative-control row."

michaelHicksRow : ApplicationAtlasRow
michaelHicksRow = application-atlas-row
  "Michael David Hicks"
  "small-body photometry/spectroscopy, comet/asteroid characterisation, DART/NEAT mission science"
  "observation geometry + photometric/spectral calibration + forward modelling + mission-specific data reduction + physical-property inference"
  atlasSourceBacked atlasSourceBacked atlasPartial atlasNotLocated atlasPartial atlasNotLocated
  "existing HicksSmallBodyPhotometryBidiExact and HicksCometAsteroidSpecificWorksBidiExact owners"
  "Public scientific methods are substantial; mission-specific calibration/data-reduction and handover state remain the potentially capability-bearing residuals."

jasonThomasRow : ApplicationAtlasRow
jasonThomasRow = application-atlas-row
  "Jason R. Thomas"
  "STING/IRF3/NFkB phenotypic screening, chemical proteomics, VPS34/NCOA4 ferritinophagy"
  "assay thresholds + compound/SAR design + proteomics competition + target-deconvolution workflow + genetic/orthogonal validation"
  atlasSourceBacked atlasSourceBacked atlasPartial atlasNotLocated atlasPartial atlasSourceBacked
  "Koch et al. ACS Chem Biol 2018 DOI 10.1021/acschembio.7b01060; Dowdle et al. Nat Cell Biol 2014 DOI 10.1038/ncb3053; existing Thomas owners"
  "Deep application science is public in large part; no foul play was suspected in the public recovery reporting, so technical importance alone must not be promoted into event causation."

monicaRezaRow : ApplicationAtlasRow
monicaRezaRow = application-atlas-row
  "Monica Jacinto/Reza"
  "burn-resistant high-strength nickel alloy design"
  "heat treatment + gamma-prime/grain-state process window + manufacturing tolerances + failure history + qualification"
  atlasSourceBacked atlasSourceBacked atlasPartial atlasNotLocated atlasPartial atlasNotLocated
  "US20030053926A1 / US20040208777A1; RezaApplicationTransformationPossessionExact"
  "Composition and part of the process are public/shared invention; the validated process window and qualification stack remain the discriminating residual."

joshuaLeBlancRow : ApplicationAtlasRow
joshuaLeBlancRow = application-atlas-row
  "Joshua Kyle LeBlanc"
  "space-fission instrumentation and control"
  "radiation/temperature/lifetime qualification + drift/failure maps + autonomous diagnostics/control + technology maturation"
  atlasSourceBacked atlasSourceBacked atlasPartial atlasNotLocated atlasSourceBacked atlasNotLocated
  "NASA NTRS 20250008475; LeBlancApplicationTransformationPossessionExact"
  "Named TechMat leadership is source-backed inside a distributed executive structure; exact qualification-state ownership and same-carrier handover remain open."

anthonyChavezRow : ApplicationAtlasRow
anthonyChavezRow = application-atlas-row
  "Anthony Chavez"
  "DARHT/Scorpius pulsed accelerator/radiographic instrumentation"
  "component design + beam diagnostics/calibration + configuration + commissioning/failure history + experiment-specific application integration"
  atlasSourceBacked atlasSourceBacked atlasPartial atlasNotLocated atlasSourceBacked atlasNotLocated
  "LANL 2025 engineering profile; Scorpius/DARHT calibration/design publications; ChavezApplicationTransformationPossessionExact"
  "Application engineering/calibration role is supported; programme surface is distributed and unique possession of calibrated inverse-model capability is not established."

record AtlasBoundary : Set where
  constructor atlas-boundary
  field
    sameRubricAppliedAcrossCases : Bool
    sameRubricAppliedAcrossCasesIsTrue : sameRubricAppliedAcrossCases ≡ true
    technicalDepthImpliesCommonMotive : Bool
    technicalDepthImpliesCommonMotiveIsFalse : technicalDepthImpliesCommonMotive ≡ false
    publicFoundationExcludesPrivateApplicationResidual : Bool
    publicFoundationExcludesPrivateApplicationResidualIsFalse : publicFoundationExcludesPrivateApplicationResidual ≡ false
    eventSpecificEvidenceCanOverrideTechnicalPattern : Bool
    eventSpecificEvidenceCanOverrideTechnicalPatternIsTrue : eventSpecificEvidenceCanOverrideTechnicalPattern ≡ true

canonicalAtlasBoundary : AtlasBoundary
canonicalAtlasBoundary = atlas-boundary true refl false refl false refl true refl
