module DASHI.Environment.YeomansKeylineSourceAttributionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution

------------------------------------------------------------------------
-- YEOMANS / KEYLINE SOURCE + ATTRIBUTION ATLAS
--
-- External sources own only their bounded source readings.  DASHI owns the
-- typed source taxonomy, cross-source synthesis, LES/hydrology adapters and
-- no-go theorems below.
------------------------------------------------------------------------

data KeylineSourceRole : Set where
  primaryDesignLineage
  scholarlyHistoricalReview
  directKeylineFieldStudy
  keylineModelStudy
  methodAdjacentContourFieldStudy : KeylineSourceRole

data KeylineEvidenceRelation : Set where
  sourceDefinesDesignLineage
  directlyStudiesKeyline
  modelsKeyline
  adjacentMethodEvidence : KeylineEvidenceRelation

data KeylineEvidenceForm : Set where
  primaryBook
  peerReviewedReview
  peerReviewedFieldExperiment
  peerReviewedModelStudy : KeylineEvidenceForm

record KeylineSource : Set where
  constructor keyline-source
  field
    authorsOrEditors : String
    title : String
    venueOrPublisher : String
    year : Nat
    identifier : String
    role : KeylineSourceRole
    relation : KeylineEvidenceRelation
    evidenceForm : KeylineEvidenceForm
    boundedReading : String
    excludedPromotion : String
    claimOwner : Attribution.ClaimOwner

open KeylineSource public

yeomans1954 : KeylineSource
yeomans1954 = keyline-source
  "P. A. Yeomans"
  "The Keyline Plan"
  "Sydney, 1954; bibliographic recovery via University of Pennsylvania Online Books / source-preserving digital copy"
  1954
  "The Keyline Plan (1954); no DOI assigned"
  primaryDesignLineage sourceDefinesDesignLineage primaryBook
  "Primary source for the Yeomans Keyline design lineage: landscape/topographic reading, farm water storage and redistribution, soil development, vegetation/trees and integrated farm planning."
  "Does not establish a universal hydrological, erosion, yield, soil-carbon, biodiversity, profitability or causal-effect result for a modern implementation."
  Attribution.externalSourceOwner

yeomans1958 : KeylineSource
yeomans1958 = keyline-source
  "P. A. Yeomans"
  "The Challenge of Landscape: The Development and Practice of Keyline"
  "Keyline Publishing / source-preserving digital edition"
  1958
  "The Challenge of Landscape (1958); no DOI assigned"
  primaryDesignLineage sourceDefinesDesignLineage primaryBook
  "Primary Keyline design-development source; retained for the landscape-planning lineage and the historical Scale of Permanence formulation."
  "The Scale of Permanence is a design ordering, not a proved universal causal priority ordering or an LES optimization theorem."
  Attribution.externalSourceOwner

fergusonLovell2014 : KeylineSource
fergusonLovell2014 = keyline-source
  "Rafter Sass Ferguson; Sarah Taylor Lovell"
  "Permaculture for agroecology: design, movement, practice, and worldview. A review"
  "Agronomy for Sustainable Development 34:251-274"
  2014
  "DOI 10.1007/s13593-013-0181-6"
  scholarlyHistoricalReview sourceDefinesDesignLineage peerReviewedReview
  "Scholarly historical/contextual review linking Yeomans' Keyline work to whole-farm water management, agroforestry and soil-building influences on later permaculture; also records the limited scientific literature then available on Keyline."
  "Historical influence and evidence-gap statements do not validate the full Keyline system or transfer later permaculture claims back to Yeomans."
  Attribution.externalSourceOwner

ponceRodriguezEtAl2021 : KeylineSource
ponceRodriguezEtAl2021 = keyline-source
  "María del Carmen Ponce-Rodríguez; Francisco Oscar Carrete-Carreón; Gerardo Alonso Núñez-Fernández; José de Jesús Muñoz-Ramos; María-Elena Pérez-López"
  "Keyline in Bean Crop (Phaseolus vulgaris L.) for Soil and Water Conservation"
  "Sustainability 13(17):9982"
  2021
  "DOI 10.3390/su13179982"
  directKeylineFieldStudy directlyStudiesKeyline peerReviewedFieldExperiment
  "Direct empirical Keyline-labelled crop/soil-water study under the reported Durango field conditions; useful for site-specific moisture, erosion and crop-response evidence."
  "One crop/site implementation does not prove universal Keyline effectiveness, portability, mechanism identity or whole-system performance."
  Attribution.externalSourceOwner

giambastianiEtAl2023 : KeylineSource
giambastianiEtAl2023 = keyline-source
  "Yamuna Giambastiani; Gherardo Biancofiore; Matteo Mancini; Antonio Di Giorgio; Riccardo Giusti; Stefano Cecchi; Lorenzo Gardin; Alessandro Errico"
  "Modelling the Effect of Keyline Practice on Soil Erosion Control"
  "Land 12(1):100"
  2023
  "DOI 10.3390/land12010100"
  keylineModelStudy modelsKeyline peerReviewedModelStudy
  "GIS/LiDAR/model-based comparison of Keyline practice for erosion-control planning in two small basins; admissible as modelling evidence for geometry/planning hypotheses."
  "Model output is not a field causal-effect receipt, held-out validation of every Keyline implementation, or universal erosion reduction theorem."
  Attribution.externalSourceOwner

mondacaEtAl2024 : KeylineSource
mondacaEtAl2024 = keyline-source
  "Pedro Mondaca; Roxana Lebuy; Sergio Rojas; Javier Aguas; et al."
  "Contour furrowing reduces erosion and enhances soil moisture on semiarid hillslopes"
  "Geoderma Regional 38:e00826"
  2024
  "DOI 10.1016/j.geodrs.2024.e00826"
  methodAdjacentContourFieldStudy adjacentMethodEvidence peerReviewedFieldExperiment
  "Field evidence for contour furrowing on semiarid hillslopes, including soil-moisture and soil-loss outcomes under the reported treatments.  It is method-adjacent to Keyline geometry/water-routing questions."
  "Contour furrowing is not definitionally the full Yeomans Keyline system; this study cannot be laundered into direct validation of dams, keypoints, road/tree layout, gravity irrigation or the Scale of Permanence."
  Attribution.externalSourceOwner

canonicalKeylineSources : List KeylineSource
canonicalKeylineSources =
  yeomans1954 ∷ yeomans1958 ∷ fergusonLovell2014 ∷
  ponceRodriguezEtAl2021 ∷ giambastianiEtAl2023 ∷ mondacaEtAl2024 ∷ []

data PrimaryDesignMeansEmpiricalProofPermission : Set where
data AdjacentContourMeansFullKeylineEvidencePermission : Set where
data ModelStudyMeansFieldEffectPermission : Set where
data KeylineMeansPermacultureIdentityPermission : Set where
data ScaleOfPermanenceMeansCausalPriorityTheoremPermission : Set where

data KeylineLabelMeansSameImplementationPermission : Set where

primaryDesignSourceDoesNotProveEffect : PrimaryDesignMeansEmpiricalProofPermission → ⊥
primaryDesignSourceDoesNotProveEffect ()
adjacentContourEvidenceIsNotFullKeylineEvidence : AdjacentContourMeansFullKeylineEvidencePermission → ⊥
adjacentContourEvidenceIsNotFullKeylineEvidence ()
modelOutputDoesNotBecomeFieldEffect : ModelStudyMeansFieldEffectPermission → ⊥
modelOutputDoesNotBecomeFieldEffect ()
keylineIsNotDefinitionallyPermaculture : KeylineMeansPermacultureIdentityPermission → ⊥
keylineIsNotDefinitionallyPermaculture ()
scaleOfPermanenceDoesNotBecomeCausalPriorityTheorem : ScaleOfPermanenceMeansCausalPriorityTheoremPermission → ⊥
scaleOfPermanenceDoesNotBecomeCausalPriorityTheorem ()
keylineLabelDoesNotIdentifyImplementation : KeylineLabelMeansSameImplementationPermission → ⊥
keylineLabelDoesNotIdentifyImplementation ()

record KeylineAttributionBoundary : Set where
  constructor keyline-attribution-boundary
  field
    yeomansOwnsPrimaryDesignClaimsOnlyWithinSourceScope : Bool
    modernStudiesRetainTheirOwnAuthorsAndConditions : Bool
    dashiHydrologyAndLESReconstructionRemainDashiOwned : Bool
    adjacentContourEvidenceIsDirectWholeKeylineValidation : Bool
    sourceCitationAutomaticallyPromotesRecommendation : Bool

canonicalKeylineAttributionBoundary : KeylineAttributionBoundary
canonicalKeylineAttributionBoundary =
  keyline-attribution-boundary true true true false false
