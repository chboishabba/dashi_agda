module DASHI.Law.SensibLawPabaiDefeaterRefinementRerunExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawLegalGraphRefinementReopeningExact as Refinement
import DASHI.Cognition.PNF.SensibLawLegalObserverResidualRefinementBidiExact as Residual
import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawFiniteLegalCutGuardExact as CutGuard
import DASHI.Cognition.PNF.SensibLawFiniteLegalSearchRegressionExact as Regression
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence

pabaiFactsBeforeDefeater : Algebra.FactSet
pabaiFactsBeforeDefeater = Algebra.fact-set
  (Regression.pabaiForeseeability ∷
   Regression.pabaiKnowledge ∷
   Regression.pabaiControl ∷ [])

pabaiFactsAfterDefeater : Algebra.FactSet
pabaiFactsAfterDefeater = Algebra.fact-set
  (Regression.pabaiCorePolicy ∷
   Regression.pabaiForeseeability ∷
   Regression.pabaiKnowledge ∷
   Regression.pabaiControl ∷ [])

samePabaiGraphPreserved :
  Refinement.GraphRefinement Regression.pabaiGraph Regression.pabaiGraph
samePabaiGraphPreserved = Refinement.graph-refinement
  (λ membership → membership)
  (λ membership → membership)
  "same existing Pabai candidate-duty rule retained"
  "same existing Pabai source carrier retained"

preserveOldPabaiFacts :
  ∀ {p} →
  Algebra._∈_ p (Algebra.facts pabaiFactsBeforeDefeater) →
  Algebra._∈_ p (Algebra.facts pabaiFactsAfterDefeater)
preserveOldPabaiFacts Algebra.here = Algebra.there Algebra.here
preserveOldPabaiFacts (Algebra.there Algebra.here) =
  Algebra.there (Algebra.there Algebra.here)
preserveOldPabaiFacts (Algebra.there (Algebra.there Algebra.here)) =
  Algebra.there (Algebra.there (Algebra.there Algebra.here))
preserveOldPabaiFacts (Algebra.there (Algebra.there (Algebra.there ())))

pabaiDefeaterFactRefinement :
  Refinement.FactRefinement pabaiFactsBeforeDefeater pabaiFactsAfterDefeater
pabaiDefeaterFactRefinement = Refinement.fact-refinement
  preserveOldPabaiFacts
  "append existing typed core-government-policy defeater proposition"

pabaiDefeaterRefinementReceipt :
  Refinement.LegalRefinementReceipt
    Regression.pabaiGraph Regression.pabaiGraph
    pabaiFactsBeforeDefeater pabaiFactsAfterDefeater
pabaiDefeaterRefinementReceipt = Refinement.legal-refinement-receipt
  samePabaiGraphPreserved
  pabaiDefeaterFactRefinement
  Residual.missingExceptionOrDefeater
  Residual.inspectExceptionOrDefeater
  Refinement.factCarrier
  true refl
  true refl

------------------------------------------------------------------------
-- Actual executable rerun on the same non-empty graph.
------------------------------------------------------------------------

pabaiReachableBeforeDefeater :
  Search.reachable 1 Regression.pabaiGraph pabaiFactsBeforeDefeater
    Negligence.dutyProposition ≡ true
pabaiReachableBeforeDefeater = refl

pabaiUnreachableAfterDefeater :
  Search.reachable 1 Regression.pabaiGraph pabaiFactsAfterDefeater
    Negligence.dutyProposition ≡ false
pabaiUnreachableAfterDefeater = refl

pabaiCutBeforeDefeater :
  CutGuard.searchReachableMinimalCut 1 Regression.pabaiGraph
    pabaiFactsBeforeDefeater Negligence.dutyProposition
  ≡ Search.found (Search.ruleKey Regression.pabaiDutyRule ∷ [])
pabaiCutBeforeDefeater = refl

pabaiCutAfterDefeaterRoutesToRepair :
  CutGuard.searchReachableMinimalCut 1 Regression.pabaiGraph
    pabaiFactsAfterDefeater Negligence.dutyProposition
  ≡ Search.notFound
pabaiCutAfterDefeaterRoutesToRepair = refl

pabaiExistingRepairCandidateStillReopens :
  Search.firstReopeningTransformation 1 Negligence.dutyProposition
    (Regression.pabaiReformulationCandidate ∷ [])
  ≡ Search.found Regression.pabaiReformulationCandidate
pabaiExistingRepairCandidateStillReopens = Regression.pabaiTransformationSearch

------------------------------------------------------------------------
-- Proof-relevant rerun. Before refinement the three premises are facts and the
-- core-policy defeater is underivable. After refinement the defeater is itself a
-- fact, so the rule's required defeater-absence witness is contradictory.
------------------------------------------------------------------------

foreseeabilityBeforeProof :
  Algebra.Reachable Regression.pabaiGraph pabaiFactsBeforeDefeater
    Regression.pabaiForeseeability
foreseeabilityBeforeProof = Algebra.fromFact Algebra.here

knowledgeBeforeProof :
  Algebra.Reachable Regression.pabaiGraph pabaiFactsBeforeDefeater
    Regression.pabaiKnowledge
knowledgeBeforeProof = Algebra.fromFact (Algebra.there Algebra.here)

controlBeforeProof :
  Algebra.Reachable Regression.pabaiGraph pabaiFactsBeforeDefeater
    Regression.pabaiControl
controlBeforeProof = Algebra.fromFact (Algebra.there (Algebra.there Algebra.here))

corePolicyAbsentBefore :
  Algebra.Reachable Regression.pabaiGraph pabaiFactsBeforeDefeater
    Regression.pabaiCorePolicy → ⊥
corePolicyAbsentBefore (Algebra.fromFact ())
corePolicyAbsentBefore (Algebra.byRule () enabled premises exceptions defeaters)

pabaiDutyProofBeforeDefeater :
  Algebra.Reachable Regression.pabaiGraph pabaiFactsBeforeDefeater
    Negligence.dutyProposition
pabaiDutyProofBeforeDefeater = Algebra.byRule
  Algebra.here
  tt
  (Algebra._∷_ foreseeabilityBeforeProof
    (Algebra._∷_ knowledgeBeforeProof
      (Algebra._∷_ controlBeforeProof Algebra.[])))
  Algebra.[]
  (Algebra._∷_ corePolicyAbsentBefore Algebra.[])

corePolicyAfterProof :
  Algebra.Reachable Regression.pabaiGraph pabaiFactsAfterDefeater
    Regression.pabaiCorePolicy
corePolicyAfterProof = Algebra.fromFact Algebra.here

pabaiDutyImpossibleAfterDefeater :
  Algebra.Reachable Regression.pabaiGraph pabaiFactsAfterDefeater
    Negligence.dutyProposition → ⊥
pabaiDutyImpossibleAfterDefeater (Algebra.fromFact ())
pabaiDutyImpossibleAfterDefeater
  (Algebra.byRule Algebra.here enabled premises exceptions
    (Algebra._∷_ defeaterAbsent Algebra.[])) =
  defeaterAbsent corePolicyAfterProof
pabaiDutyImpossibleAfterDefeater
  (Algebra.byRule (Algebra.there ()) enabled premises exceptions defeaters)

record PabaiDefeaterRerun : Set where
  constructor pabai-defeater-rerun
  field
    refinement :
      Refinement.LegalRefinementReceipt
        Regression.pabaiGraph Regression.pabaiGraph
        pabaiFactsBeforeDefeater pabaiFactsAfterDefeater
    beforeReachable :
      Search.reachable 1 Regression.pabaiGraph pabaiFactsBeforeDefeater
        Negligence.dutyProposition ≡ true
    beforeProofRelevant :
      Algebra.Reachable Regression.pabaiGraph pabaiFactsBeforeDefeater
        Negligence.dutyProposition
    afterUnreachable :
      Search.reachable 1 Regression.pabaiGraph pabaiFactsAfterDefeater
        Negligence.dutyProposition ≡ false
    afterProofRelevantImpossible :
      Algebra.Reachable Regression.pabaiGraph pabaiFactsAfterDefeater
        Negligence.dutyProposition → ⊥
    oldReachableRouteHasCut :
      CutGuard.searchReachableMinimalCut 1 Regression.pabaiGraph
        pabaiFactsBeforeDefeater Negligence.dutyProposition
      ≡ Search.found (Search.ruleKey Regression.pabaiDutyRule ∷ [])
    newUnreachableRouteHasNoMeaningfulCut :
      CutGuard.searchReachableMinimalCut 1 Regression.pabaiGraph
        pabaiFactsAfterDefeater Negligence.dutyProposition
      ≡ Search.notFound
    repairSearchReopensCounterfactual :
      Search.firstReopeningTransformation 1 Negligence.dutyProposition
        (Regression.pabaiReformulationCandidate ∷ [])
      ≡ Search.found Regression.pabaiReformulationCandidate

open PabaiDefeaterRerun public

pabaiDefeaterRerun : PabaiDefeaterRerun
pabaiDefeaterRerun = pabai-defeater-rerun
  pabaiDefeaterRefinementReceipt
  pabaiReachableBeforeDefeater
  pabaiDutyProofBeforeDefeater
  pabaiUnreachableAfterDefeater
  pabaiDutyImpossibleAfterDefeater
  pabaiCutBeforeDefeater
  pabaiCutAfterDefeaterRoutesToRepair
  pabaiExistingRepairCandidateStillReopens

data AppendedDefeaterDeletesOldFacts : Set where
data DefeaterFixtureMakesCorePolicyUniversallyDecisive : Set where
data CounterfactualRepairIsCurrentLaw : Set where

appendOnlyDefeaterDoesNotDeleteHistory : AppendedDefeaterDeletesOldFacts → ⊥
appendOnlyDefeaterDoesNotDeleteHistory ()

fixtureDoesNotUniversaliseCorePolicy :
  DefeaterFixtureMakesCorePolicyUniversallyDecisive → ⊥
fixtureDoesNotUniversaliseCorePolicy ()

repairCandidateStillDoesNotBecomeCurrentLaw : CounterfactualRepairIsCurrentLaw → ⊥
repairCandidateStillDoesNotBecomeCurrentLaw ()
