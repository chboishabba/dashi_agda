module DASHI.Culture.LopezRiosCriticalTheoryPsychologyCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Culture.LopezRiosPsychologisationDialecticNonDescentExact as Lopez
import DASHI.Culture.LopezRiosMarxistPsychologySourceAtlasExact as LopezSources
import DASHI.Culture.MarxLabourUnionSourceBoundaryExact as Marx
import DASHI.Culture.HistoricalTotalityCriticalTheoryCrossPollinationExact as Totality
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.FeministRechartingSourceBridgeExact as Feminist
import DASHI.Core.CriticalRelationalGrammarCapstoneExact as Critical
import DASHI.Core.TrinhSubjectInMakingNoncollapseExact as Trinh
import DASHI.Reasoning.LacanZizekIdeologyBridge as Ideology
import DASHI.Reasoning.LacanCapitalistDiscourseMutation as Capitalist
import DASHI.Philosophy.MentalHealthWorkedExample as Mental
import DASHI.Promotion.SystemicDistressReframingBoundary as Distress

------------------------------------------------------------------------
-- LOPEZ-RIOS x EXISTING CRITICAL-THEORY / PSYCHOLOGY GRAPH
--
-- This is an integration owner, not a synthesis of Marx, Lacan, Zizek,
-- Irigaray, Crenshaw, Trinh, or Lopez-Rios into one doctrine.
--
-- Source attribution remains owned by each imported source atlas/boundary.
-- The finite factorisation/non-descent theorems below are DASHI constructions.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Psychologisation is an instance of the repository's generic
--    non-factorability pattern.
------------------------------------------------------------------------

lopezPsychologisationIsIntersectionalShape :
  INF.NonFactorabilityWitness
    (λ state → Lopez.individualObservation state Lopez.samePerson)
    (λ state → Lopez.structuralDependency state Lopez.samePerson)
lopezPsychologisationIsIntersectionalShape =
  INF.nonFactorabilityWitness
    Lopez.exploitativeLabourFrame
    Lopez.nonExploitativeLabourFrame
    Lopez.sameIndividualObservation
    Lopez.structuralDependenciesDiffer

individualRechartingStillCannotRecoverStructuralDependency :
  ∀ {Recharted : Set} →
  (rechart : Lopez.IndividualObservation → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (Lopez.individualObservation state Lopez.samePerson))
    (λ state → Lopez.structuralDependency state Lopez.samePerson) →
  ⊥
individualRechartingStillCannotRecoverStructuralDependency rechart =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart lopezPsychologisationIsIntersectionalShape

------------------------------------------------------------------------
-- 2. Feminist recharting supplies the generic positive repair pattern:
--    information erased by an inherited chart requires a genuine residual
--    coordinate, not a sign flip or relabelling of the old quotient.
------------------------------------------------------------------------

feministRechartingBoundaryRetained : Feminist.FeministRechartingBoundary
feministRechartingBoundaryRetained = Feminist.canonicalFeministRechartingBoundary

intersectionalNonFactorabilityRetained :
  INF.NonFactorabilityWitness INF.flatProjection INF.relationalOutcome
intersectionalNonFactorabilityRetained = INF.canonicalIntersectionalNonFactorability

------------------------------------------------------------------------
-- 3. Subject formation is not recovered from a public category.  This is an
--    independent feminist/postcolonial anti-reification theorem that has the
--    same mathematical shape without being attributed to Lopez-Rios.
------------------------------------------------------------------------

publicCategoryStillCannotRecoverSubjectFormation :
  INF.FactorsThrough Trinh.publicCategory Trinh.subjectFormation → ⊥
publicCategoryStillCannotRecoverSubjectFormation =
  Trinh.publicCategoryCannotRecoverSubjectFormation

------------------------------------------------------------------------
-- 4. Lacanian / Zizekian ideology and capitalist-discourse bridges remain
--    candidate structural readings.  They do not diagnose individuals or prove
--    a political economy from discourse placement alone.
------------------------------------------------------------------------

ideologyBoundaryRetained : Ideology.LacanZizekIdeologyBoundary
ideologyBoundaryRetained = Ideology.canonicalLacanZizekIdeologyBoundary

capitalistDiscourseBoundaryRetained :
  Capitalist.CapitalistDiscourseAuthorityBoundary
capitalistDiscourseBoundaryRetained =
  Capitalist.canonicalCapitalistDiscourseAuthorityBoundary

------------------------------------------------------------------------
-- 5. Marx supplies bounded labour/capital source context, not a proof that
--    every distress state is caused by capitalism or that DASHI's finite
--    non-factorability theorem is Marx's theorem.
------------------------------------------------------------------------

marxLabourBoundaryRetained : Marx.MarxLabourUnionSourceBoundary
marxLabourBoundaryRetained = Marx.canonicalMarxLabourUnionSourceBoundary

------------------------------------------------------------------------
-- 6. Existing mental-health pluralism remains authoritative for the psychology
--    carrier: bodily, developmental, relational, material, symbolic and
--    existential explanations stay live; systemic critique does not promote
--    diagnosis or causal closure.
------------------------------------------------------------------------

mentalHealthCaseRetained : Mental.MentalHealthCase
mentalHealthCaseRetained = Mental.canonicalMentalHealthCase

systemicDistressBoundaryRetained : Distress.SystemicDistressBoundary
systemicDistressBoundaryRetained = Distress.canonicalSystemicDistressBoundary

------------------------------------------------------------------------
-- 7. Critical-relational and historical-totality boundaries prevent us from
--    collapsing shared formal patterns into shared doctrines or empirical laws.
------------------------------------------------------------------------

criticalGrammarBoundaryRetained : Critical.CriticalRelationalGrammarBoundary
criticalGrammarBoundaryRetained = Critical.canonicalCriticalRelationalGrammarBoundary

historicalTotalityBoundaryRetained :
  Totality.HistoricalTotalityCriticalTheoryBoundary
historicalTotalityBoundaryRetained =
  Totality.canonicalHistoricalTotalityCriticalTheoryBoundary

------------------------------------------------------------------------
-- No-promotion / anti-construction boundary.
------------------------------------------------------------------------

data LopezRiosEqualsIntersectionality : Set where

data LopezRiosEqualsLacanianTheory : Set where

data LopezRiosEqualsFeministTheory : Set where

data MarxLabourSourceProvesPsychologicalCause : Set where

data IdeologyBridgeDiagnosesPerson : Set where

data CriticalFormalSimilarityMergesSources : Set where

data SystemicCritiqueErasesBodilyOrClinicalAxes : Set where

lopezRiosNotIdentifiedWithIntersectionality : LopezRiosEqualsIntersectionality → ⊥
lopezRiosNotIdentifiedWithIntersectionality ()

lopezRiosNotIdentifiedWithLacanianTheory : LopezRiosEqualsLacanianTheory → ⊥
lopezRiosNotIdentifiedWithLacanianTheory ()

lopezRiosNotIdentifiedWithFeministTheory : LopezRiosEqualsFeministTheory → ⊥
lopezRiosNotIdentifiedWithFeministTheory ()

marxLabourSourceDoesNotProvePsychologicalCause :
  MarxLabourSourceProvesPsychologicalCause → ⊥
marxLabourSourceDoesNotProvePsychologicalCause ()

ideologyBridgeDoesNotDiagnosePerson : IdeologyBridgeDiagnosesPerson → ⊥
ideologyBridgeDoesNotDiagnosePerson ()

formalSimilarityDoesNotMergeSources : CriticalFormalSimilarityMergesSources → ⊥
formalSimilarityDoesNotMergeSources ()

systemicCritiqueDoesNotEraseOtherAxes : SystemicCritiqueErasesBodilyOrClinicalAxes → ⊥
systemicCritiqueDoesNotEraseOtherAxes ()

record LopezRiosCriticalTheoryPsychologyBoundary : Set where
  constructor lopez-rios-critical-theory-psychology-boundary
  field
    psychologisationReusesGenericNonfactorabilityShape : Bool
    inheritedIndividualChartCanBeRepairedByRelabellingAlone : Bool
    feministPositiveRechartingRequiresAddedResidual : Bool
    publicCategoryDeterminesSubjectFormation : Bool
    ideologyBridgeDiagnosesIndividual : Bool
    capitalistDiscourseGraphProvesAllCapitalistSystems : Bool
    marxSourceProvesDASHIPsychologyTheorem : Bool
    systemicCritiqueErasesOtherPsychologyAxes : Bool
    sharedFormalPatternMergesHistoricalDoctrines : Bool
    sourceAttributionRemainsPerOwner : Bool

canonicalLopezRiosCriticalTheoryPsychologyBoundary :
  LopezRiosCriticalTheoryPsychologyBoundary
canonicalLopezRiosCriticalTheoryPsychologyBoundary =
  lopez-rios-critical-theory-psychology-boundary
    true false true false false false false false false true
