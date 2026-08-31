module DASHI.DrugPolicyPsychedelicSemanticEpistemicValidation where

------------------------------------------------------------------------
-- Focused validation root for the drug-policy / psychedelic semantic:epistemic
-- BIDI lane.  Import closure is the validation target; no additional theorem
-- authority is introduced here.
------------------------------------------------------------------------

import DASHI.Governance.DrugPolicyPsychedelicSemanticEpistemicEverything

-- Pin several high-value theorem surfaces so accidental API drift is visible at
-- the focused root rather than hidden behind an import-only aggregate.

import DASHI.Governance.ContestedDrugCategoryAtlasBidiExact as Atlas
import DASHI.Governance.DrugCategoryMultiChartTranslationGeometryExact as Translation
import DASHI.Governance.DrugCategoryTranslationSelectiveReopeningExact as TranslationReopen
import DASHI.Governance.DrugCategoryTranslationPathResidueExact as PathResidue
import DASHI.Governance.DrugCategoryTranslationEdgeIndexedReopeningExact as EdgeIndexed
import DASHI.Governance.DrugCategoryPhilosophyOperatorAtlasExact as Philosophy
import DASHI.Governance.DrugCategoryPhilosophySelectiveReopeningExact as PhilosophyReopen

atlasBoundary : Atlas.ContestedDrugCategoryAtlasBoundary
atlasBoundary = Atlas.canonicalContestedDrugCategoryAtlasBoundary

translationBoundary : Translation.DrugCategoryMultiChartTranslationBoundary
translationBoundary = Translation.canonicalDrugCategoryMultiChartTranslationBoundary

translationReopeningBoundary :
  TranslationReopen.DrugCategoryTranslationReopeningBoundary
translationReopeningBoundary =
  TranslationReopen.canonicalDrugCategoryTranslationReopeningBoundary

translationPathBoundary : PathResidue.DrugCategoryTranslationPathResidueBoundary
translationPathBoundary = PathResidue.canonicalDrugCategoryTranslationPathResidueBoundary

edgeIndexedBoundary : EdgeIndexed.DrugCategoryTranslationEdgeIndexedBoundary
edgeIndexedBoundary = EdgeIndexed.canonicalDrugCategoryTranslationEdgeIndexedBoundary

philosophyBoundary : Philosophy.DrugCategoryPhilosophyOperatorBoundary
philosophyBoundary = Philosophy.canonicalDrugCategoryPhilosophyOperatorBoundary

philosophyReopeningBoundary : PhilosophyReopen.PhilosophySeededReopeningBoundary
philosophyReopeningBoundary = PhilosophyReopen.canonicalPhilosophySeededReopeningBoundary

stateClinicalRevisionStillReopensClinicalSafety :
  EdgeIndexed.Affected.ReopeningObligation
    EdgeIndexed.Depends
    (EdgeIndexed.edgeArtifact EdgeIndexed.stateToClinicalEdge)
    (EdgeIndexed.consumerArtifact EdgeIndexed.clinicalSafetyConsequence)
stateClinicalRevisionStillReopensClinicalSafety =
  EdgeIndexed.stateClinicalRevisionReopensClinicalSafety
