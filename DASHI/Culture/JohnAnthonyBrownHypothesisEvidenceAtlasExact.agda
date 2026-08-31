module DASHI.Culture.JohnAnthonyBrownHypothesisEvidenceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.JohnAnthonyBrownDocumentLineageExact as Lineage
import DASHI.Culture.JohnAnthonyBrownPaperSectionHypothesisManifestExact as Manifest

------------------------------------------------------------------------
-- JOHN ANTHONY BROWN: HYPOTHESIS EVIDENCE ATLAS
--
-- Authorial attribution:
--   John Anthony Brown is the authorial source of the research programme.
--
-- Current hypothesis surface:
--   Childhood Religious Coercion, Trauma, and Long-Term Psychosocial Outcomes
--   — A Comparative Mixed-Methods Research Proposal (2026 Drive surface).
--
-- BIDI discipline:
--   manuscript citation != verified source
--   source construct != target-domain instantiation
--   comparator-domain evidence != religious-childhood effect estimate
--   proposed instrument != validated instrument in the target population
--   adjusted association != unconfounded causal effect
------------------------------------------------------------------------

data EvidenceCoordinate : Set where
  constructCoordinate : EvidenceCoordinate
  instrumentCoordinate : EvidenceCoordinate
  populationCoordinate : EvidenceCoordinate
  designCoordinate : EvidenceCoordinate
  associationCoordinate : EvidenceCoordinate
  causalCoordinate : EvidenceCoordinate
  competingExplanationCoordinate : EvidenceCoordinate
  rightsPolicyCoordinate : EvidenceCoordinate
  qualitativeMeaningCoordinate : EvidenceCoordinate
  recoveryResilienceCoordinate : EvidenceCoordinate


data EvidenceStatus : Set where
  installedFromCurrentProposal : EvidenceStatus
  recoveredFromEarlierBrownDraft : EvidenceStatus
  candidateExternalSource : EvidenceStatus
  independentlyVerifiedExternalSource : EvidenceStatus
  missingExternalReceipt : EvidenceStatus
  notRequiredForThisClaim : EvidenceStatus


data SourceRole : Set where
  constructSource : SourceRole
  measurementSource : SourceRole
  targetPopulationSource : SourceRole
  comparatorPopulationSource : SourceRole
  mechanismSource : SourceRole
  resilienceSource : SourceRole
  designSource : SourceRole
  rightsAuthoritySource : SourceRole
  contextualSource : SourceRole

record SourceAtlasEntry : Set where
  constructor source-atlas-entry
  field
    sourceKey : String
    authorsOrInstitution : String
    title : String
    yearVenue : String
    doiOrIdentifier : String
    recoveredFrom : Lineage.BrownDocumentSnapshot
    role : SourceRole
    verification : EvidenceStatus
    boundedReading : String

open SourceAtlasEntry public

------------------------------------------------------------------------
-- Sources explicitly present in the Brown document lineage.
--
-- These rows preserve the manuscript bibliography as provenance.  They are
-- not promoted to independently verified empirical support merely by being
-- listed in the paper.
------------------------------------------------------------------------

hunsbergerBrown1984 : SourceAtlasEntry
hunsbergerBrown1984 = source-atlas-entry
  "HunsbergerBrown1984"
  "B. Hunsberger; L. B. Brown"
  "Religious socialization, apostasy, and the impact of family background"
  "1984; Journal for the Scientific Study of Religion 23(3):239-251"
  "DOI not asserted in the supplied Brown draft"
  Lineage.draft3Snapshot
  contextualSource
  recoveredFromEarlierBrownDraft
  "Useful for family-background / religious-socialisation context; it does not by citation alone establish John Anthony Brown H1-H5 or coercive-religious exposure effects."

boyatzisJanicki2003 : SourceAtlasEntry
boyatzisJanicki2003 = source-atlas-entry
  "BoyatzisJanicki2003"
  "C. J. Boyatzis; D. L. Janicki"
  "Parent-child communication about religion: Survey and diary data on unilateral transmission and bi-directional reciprocity styles"
  "2003; Review of Religious Research 44(3):252-270"
  "DOI not asserted in the supplied Brown draft"
  Lineage.draft3Snapshot
  contextualSource
  recoveredFromEarlierBrownDraft
  "Useful for parent-child religious communication and reciprocity structure; not by itself a coercion, trauma, prevalence or causal-effect receipt."

granqvistKirkpatrick2016 : SourceAtlasEntry
granqvistKirkpatrick2016 = source-atlas-entry
  "GranqvistKirkpatrick2016"
  "P. Granqvist; L. A. Kirkpatrick"
  "Attachment and religious representations and behavior"
  "2016; in Handbook of Attachment, 3rd ed., pp. 917-940"
  "DOI not asserted in the supplied Brown draft"
  Lineage.draft3Snapshot
  mechanismSource
  recoveredFromEarlierBrownDraft
  "Candidate attachment/religious-development mechanism source; it does not identify coercive religious childhood exposure as the unique cause of later attachment outcomes."

koenigKingCarson2012 : SourceAtlasEntry
koenigKingCarson2012 = source-atlas-entry
  "KoenigKingCarson2012"
  "H. G. Koenig; D. E. King; V. B. Carson"
  "Handbook of Religion and Health, 2nd ed."
  "2012; Oxford University Press"
  "book; no DOI asserted in the supplied Brown draft"
  Lineage.draft3Snapshot
  contextualSource
  recoveredFromEarlierBrownDraft
  "Broad religion/health synthesis context; cannot be used as a single-direction religion-harm receipt and does not substitute for target-population coercion evidence."

betancourtKhan2008 : SourceAtlasEntry
betancourtKhan2008 = source-atlas-entry
  "BetancourtKhan2008"
  "T. S. Betancourt; K. T. Khan"
  "The mental health of children affected by armed conflict: Protective processes and pathways to resilience"
  "2008; International Review of Psychiatry 20(3):317-328"
  "DOI not asserted in the supplied Brown draft"
  Lineage.draft3Snapshot
  resilienceSource
  recoveredFromEarlierBrownDraft
  "Comparator-domain resilience source. It may motivate resilience/support coordinates but does not instantiate religious-childhood exposure or establish equivalence between armed-conflict and religious-coercion harms."

fazelReedPanterBrickStein2012 : SourceAtlasEntry
fazelReedPanterBrickStein2012 = source-atlas-entry
  "FazelEtAl2012"
  "M. Fazel; R. V. Reed; C. Panter-Brick; A. Stein"
  "Mental health of displaced and refugee children resettled in high-income countries: Risk and protective factors"
  "2012; The Lancet 379(9812):266-282"
  "DOI not asserted in the supplied Brown draft"
  Lineage.draft3Snapshot
  comparatorPopulationSource
  recoveredFromEarlierBrownDraft
  "Comparator-domain risk/protection evidence only; no moral, clinical or causal equivalence with coercive religious formation is installed."

mastenNarayan2012 : SourceAtlasEntry
mastenNarayan2012 = source-atlas-entry
  "MastenNarayan2012"
  "A. S. Masten; A. J. Narayan"
  "Child development in the context of disaster, war, and terrorism: Pathways of risk and resilience"
  "2012; Annual Review of Psychology 63:227-257"
  "DOI not asserted in the supplied Brown draft"
  Lineage.draft3Snapshot
  resilienceSource
  recoveredFromEarlierBrownDraft
  "Supports the general risk/resilience architecture in a different exposure domain; does not establish John Anthony Brown's target-domain H1-H5 effects."

smithPerrinYuleRabeHesketh2001 : SourceAtlasEntry
smithPerrinYuleRabeHesketh2001 = source-atlas-entry
  "SmithEtAl2001"
  "P. Smith; S. Perrin; W. Yule; S. Rabe-Hesketh"
  "War exposure and maternal reactions in the psychological adjustment of children from Bosnia-Hercegovina"
  "2001; Journal of Child Psychology and Psychiatry 42(3):395-404"
  "DOI not asserted in the supplied Brown draft"
  Lineage.draft3Snapshot
  comparatorPopulationSource
  recoveredFromEarlierBrownDraft
  "Useful as a comparator example in which family context contributes to post-trauma adjustment; not evidence that the same effect size or mechanism holds for religious exposure."

------------------------------------------------------------------------
-- Hypothesis -> coordinate receipt map.
------------------------------------------------------------------------

record CoordinateReceipt : Set where
  constructor coordinate-receipt
  field
    hypothesis : Manifest.HypothesisKey
    coordinate : EvidenceCoordinate
    status : EvidenceStatus
    installedSource : String
    exactNeed : String
    backwardSafeReading : String

open CoordinateReceipt public

h1ConstructReceipt : CoordinateReceipt
h1ConstructReceipt = coordinate-receipt
  Manifest.H1 constructCoordinate installedFromCurrentProposal
  "John Anthony Brown 2026 conceptual definition of coercive religious practice"
  "operational construct with content validity separating coercive delivery from doctrinal content"
  "The proposal defines the exposure construct; empirical construct validity in the intended population still requires a validated measurement receipt."

h1InstrumentReceipt : CoordinateReceipt
h1InstrumentReceipt = coordinate-receipt
  Manifest.H1 instrumentCoordinate missingExternalReceipt
  "none installed"
  "validated coercive-religious-experience measure plus validated distress and PTSS outcome measures, with licensing/cultural-validity/repeated-measurement receipts"
  "Candidate instruments named in the proposal are not automatically validated for this exposure/population/use."

h1PopulationReceipt : CoordinateReceipt
h1PopulationReceipt = coordinate-receipt
  Manifest.H1 populationCoordinate missingExternalReceipt
  "none installed"
  "direct target-population evidence linking measured childhood coercive religious exposure with adult distress/PTSS under stated population scope"
  "Comparator trauma literature cannot fill the religious-childhood population coordinate."

h1CausalReceipt : CoordinateReceipt
h1CausalReceipt = coordinate-receipt
  Manifest.H1 causalCoordinate notRequiredForThisClaim
  "none"
  "a separate causal-identification design would be required only if the manuscript later promotes H1 beyond association"
  "H1 is an association hypothesis; withholding causation is a feature, not an evidential failure."

h2OutcomeVectorReceipt : CoordinateReceipt
h2OutcomeVectorReceipt = coordinate-receipt
  Manifest.H2 instrumentCoordinate missingExternalReceipt
  "none installed"
  "separate construct-valid measures for autonomy, self-trust, spiritual distress and interpersonal difficulty, including dependence/multiplicity handling"
  "One significant outcome coordinate cannot be promoted to a unitary harm score for all H2 outcomes."

h2MechanismContextReceipt : CoordinateReceipt
h2MechanismContextReceipt = coordinate-receipt
  Manifest.H2 competingExplanationCoordinate candidateExternalSource
  "Boyatzis & Janicki 2003; Granqvist & Kirkpatrick 2016 as manuscript-recovered contextual/mechanism candidates"
  "independent verification plus explicit mapping from family communication/attachment constructs to the H2 target variables"
  "Family communication or attachment theory may inform alternatives/mechanisms but does not establish coercive exposure as the unique route."

h3InstitutionalBetrayalReceipt : CoordinateReceipt
h3InstitutionalBetrayalReceipt = coordinate-receipt
  Manifest.H3 constructCoordinate missingExternalReceipt
  "current proposal defines institutional betrayal but no independently verified target-domain source is installed here"
  "construct-valid institutional-betrayal measure and direct source for disclosure/dissent penalty in the target domain"
  "A definition in John Anthony Brown's proposal is not itself independent construct validation."

h3IncrementalReceipt : CoordinateReceipt
h3IncrementalReceipt = coordinate-receipt
  Manifest.H3 associationCoordinate missingExternalReceipt
  "none installed"
  "nested-model or equivalent incremental-effect estimate beyond the declared religious-exposure measure, with collinearity/confounding/uncertainty audit"
  "Incremental predictive information does not by itself identify a unique causal mediator."

h4ResilienceComparatorReceipt : CoordinateReceipt
h4ResilienceComparatorReceipt = coordinate-receipt
  Manifest.H4 recoveryResilienceCoordinate recoveredFromEarlierBrownDraft
  "Betancourt & Khan 2008; Fazel et al. 2012; Masten & Narayan 2012; Smith et al. 2001"
  "independent verification and explicit separation of comparator-domain resilience from religious-target-domain moderation"
  "These sources motivate risk/resilience variables in other adversity domains; they cannot supply the H4 target-domain interaction coefficient."

h4ModerationReceipt : CoordinateReceipt
h4ModerationReceipt = coordinate-receipt
  Manifest.H4 associationCoordinate missingExternalReceipt
  "none installed"
  "pre-specified exposure x support/care/community interaction with timing, scale validity, multiplicity, effect-size and uncertainty receipts"
  "Observed support is not automatically an intervention effect, and an interaction in one cohort does not establish universal protection."

h5ConfoundingReceipt : CoordinateReceipt
h5ConfoundingReceipt = coordinate-receipt
  Manifest.H5 competingExplanationCoordinate installedFromCurrentProposal
  "John Anthony Brown 2026 limitations and quantitative-analysis sections"
  "declared covariate set, measurement quality, missingness, sensitivity analysis and explicit residual-confounding surface"
  "The proposal already acknowledges that propensity/IPW methods cannot eliminate unmeasured confounding."

h5AdjustedAssociationReceipt : CoordinateReceipt
h5AdjustedAssociationReceipt = coordinate-receipt
  Manifest.H5 associationCoordinate missingExternalReceipt
  "none installed"
  "observed adjusted estimate, confidence interval/effect size and model diagnostics after the pre-specified measured-covariate adjustment set"
  "Statistical detectability after adjustment is an empirical result to be tested, not a premise imported from the hypothesis."

------------------------------------------------------------------------
-- Rights/policy remains downstream of empirical results.
------------------------------------------------------------------------

record RightsPolicyPromotionGate : Set where
  constructor rights-policy-promotion-gate
  field
    empiricalFindingInstalled : Bool
    rightsAuthorityCurrent : Bool
    jurisdictionSpecificLawChecked : Bool
    normativeArgumentSeparated : Bool
    policyEffectivenessEvidenceSeparate : Bool

canonicalRightsPolicyPromotionGate : RightsPolicyPromotionGate
canonicalRightsPolicyPromotionGate =
  rights-policy-promotion-gate false false false true true

------------------------------------------------------------------------
-- BIDI non-promotion boundaries.
------------------------------------------------------------------------

data ComparatorEvidencePromotesTargetPopulation : Set where

data ConstructDefinitionPromotesValidatedMeasure : Set where

data OneOutcomePromotesWholeVector : Set where

data AdjustedAssociationPromotesCausation : Set where

data CitationRecoveredPromotesIndependentVerification : Set where

data ModerationAssociationPromotesUniversalIntervention : Set where

comparatorDoesNotPromoteTargetPopulation :
  ComparatorEvidencePromotesTargetPopulation → ⊥
comparatorDoesNotPromoteTargetPopulation ()

constructDefinitionDoesNotPromoteValidatedMeasure :
  ConstructDefinitionPromotesValidatedMeasure → ⊥
constructDefinitionDoesNotPromoteValidatedMeasure ()

oneOutcomeDoesNotPromoteWholeVector : OneOutcomePromotesWholeVector → ⊥
oneOutcomeDoesNotPromoteWholeVector ()

adjustedAssociationDoesNotPromoteCausation :
  AdjustedAssociationPromotesCausation → ⊥
adjustedAssociationDoesNotPromoteCausation ()

citationRecoveredDoesNotPromoteIndependentVerification :
  CitationRecoveredPromotesIndependentVerification → ⊥
citationRecoveredDoesNotPromoteIndependentVerification ()

moderationDoesNotPromoteUniversalIntervention :
  ModerationAssociationPromotesUniversalIntervention → ⊥
moderationDoesNotPromoteUniversalIntervention ()

record HypothesisEvidenceAtlasBoundary : Set where
  constructor hypothesis-evidence-atlas-boundary
  field
    johnAnthonyBrownExplicitlyAttributed : Bool
    allH1ToH5HaveCoordinateReceipts : Bool
    earlierBibliographyRetainedAsProvenance : Bool
    earlierBibliographyTreatedAsVerifiedAutomatically : Bool
    comparatorEvidenceFillsTargetPopulation : Bool
    proposedInstrumentEqualsValidatedInstrument : Bool
    adjustedAssociationEqualsCausalEffect : Bool
    mixedRiskAndResilienceArchitecturePreserved : Bool
    rightsPolicyPromotionRequiresSeparateGate : Bool

canonicalHypothesisEvidenceAtlasBoundary : HypothesisEvidenceAtlasBoundary
canonicalHypothesisEvidenceAtlasBoundary =
  hypothesis-evidence-atlas-boundary
    true true true false false false false true true
