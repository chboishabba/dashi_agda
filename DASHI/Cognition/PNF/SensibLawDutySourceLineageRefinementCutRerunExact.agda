module DASHI.Cognition.PNF.SensibLawDutySourceLineageRefinementCutRerunExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawFiniteLegalCutGuardExact as CutGuard
import DASHI.Cognition.PNF.SensibLawLegalGraphRefinementReopeningExact as Refinement
import DASHI.Cognition.PNF.SensibLawLegalObserverResidualRefinementBidiExact as Residual
import DASHI.Cognition.PNF.SensibLawCullenPublicAuthorityDutyCalibrationExact as Cullen
import DASHI.Cognition.PNF.SensibLawDutyPublicAuthoritySourceLineageGraphExact as Lineage

------------------------------------------------------------------------
-- SOURCE-LINEAGE REFINEMENT / CUT RERUN
--
-- On the richer Mallonland/Cullen/Pabai graph, hold Cullen's foreseeable-risk
-- and statutory-function features fixed while withholding the positive
-- operational act. Then append only that already source-owned material feature.
-- The specific Cullen duty route changes from unreachable to reachable and a
-- meaningful guarded cut appears. No rule/source is added or rewritten.
------------------------------------------------------------------------

beforePositiveActFacts : Algebra.FactSet
beforePositiveActFacts = Algebra.fact-set
  (Cullen.foreseeablePhysicalInjuryRisk ∷
   Cullen.statutoryPoliceFunction ∷ [])

afterPositiveActFacts : Algebra.FactSet
afterPositiveActFacts = Lineage.cullenHoldingFacts

sameLineageGraphPreserved :
  Refinement.GraphRefinement
    Lineage.dutyPublicAuthoritySourceLineageGraph
    Lineage.dutyPublicAuthoritySourceLineageGraph
sameLineageGraphPreserved = Refinement.graph-refinement
  (λ membership → membership)
  (λ membership → membership)
  "no rule added: same Mallonland/Cullen/Pabai source-lineage graph"
  "no source added: same three source carriers"

preserveBeforeFacts :
  ∀ {p} →
  Algebra._∈_ p (Algebra.facts beforePositiveActFacts) →
  Algebra._∈_ p (Algebra.facts afterPositiveActFacts)
preserveBeforeFacts Algebra.here = Algebra.there Algebra.here
preserveBeforeFacts (Algebra.there Algebra.here) =
  Algebra.there (Algebra.there Algebra.here)
preserveBeforeFacts (Algebra.there (Algebra.there ()))

positiveActFactRefinement :
  Refinement.FactRefinement beforePositiveActFacts afterPositiveActFacts
positiveActFactRefinement = Refinement.fact-refinement
  preserveBeforeFacts
  "append Cullen positive-operational-act material feature"

positiveActRefinementReceipt :
  Refinement.LegalRefinementReceipt
    Lineage.dutyPublicAuthoritySourceLineageGraph
    Lineage.dutyPublicAuthoritySourceLineageGraph
    beforePositiveActFacts afterPositiveActFacts
positiveActRefinementReceipt = Refinement.legal-refinement-receipt
  sameLineageGraphPreserved
  positiveActFactRefinement
  Residual.missingFactualFeature
  Residual.obtainFactualEvidence
  Refinement.factCarrier
  true refl
  true refl

positiveActPresentAfterRefinement :
  Algebra._∈_ Cullen.positiveOperationalAct (Algebra.facts afterPositiveActFacts)
positiveActPresentAfterRefinement = Algebra.here

------------------------------------------------------------------------
-- Exact executable rerun on the same richer graph.
------------------------------------------------------------------------

cullenDutyUnreachableBeforePositiveAct :
  Search.reachable 1 Lineage.dutyPublicAuthoritySourceLineageGraph
    beforePositiveActFacts Cullen.cullenDutyProposition ≡ false
cullenDutyUnreachableBeforePositiveAct = refl

cullenDutyReachableAfterPositiveAct :
  Search.reachable 1 Lineage.dutyPublicAuthoritySourceLineageGraph
    afterPositiveActFacts Cullen.cullenDutyProposition ≡ true
cullenDutyReachableAfterPositiveAct = Lineage.cullenSpecificDutyReachable

cullenDutyProofAfterPositiveAct :
  Algebra.Reachable Lineage.dutyPublicAuthoritySourceLineageGraph
    afterPositiveActFacts Cullen.cullenDutyProposition
cullenDutyProofAfterPositiveAct = Lineage.cullenSpecificDutyProof

------------------------------------------------------------------------
-- Before refinement no meaningful cut exists because the route is unreachable.
-- After refinement the source-specific Cullen ratio rule is the first
-- inclusion-minimal guarded cut on the richer graph.
------------------------------------------------------------------------

noGuardedCutBeforePositiveAct :
  CutGuard.searchReachableMinimalCut 1
    Lineage.dutyPublicAuthoritySourceLineageGraph
    beforePositiveActFacts Cullen.cullenDutyProposition
  ≡ Search.notFound
noGuardedCutBeforePositiveAct = refl

cullenRatioCutAfterPositiveAct :
  CutGuard.searchReachableMinimalCut 1
    Lineage.dutyPublicAuthoritySourceLineageGraph
    afterPositiveActFacts Cullen.cullenDutyProposition
  ≡ Search.found (Search.ruleKey Lineage.cullenPositiveOperationalDutyRule ∷ [])
cullenRatioCutAfterPositiveAct = refl

------------------------------------------------------------------------
-- Bundle the same-object refinement and recomputation.
------------------------------------------------------------------------

record SourceLineagePositiveActRerun : Set where
  constructor source-lineage-positive-act-rerun
  field
    refinement :
      Refinement.LegalRefinementReceipt
        Lineage.dutyPublicAuthoritySourceLineageGraph
        Lineage.dutyPublicAuthoritySourceLineageGraph
        beforePositiveActFacts afterPositiveActFacts
    beforeRouteClosed :
      Search.reachable 1 Lineage.dutyPublicAuthoritySourceLineageGraph
        beforePositiveActFacts Cullen.cullenDutyProposition ≡ false
    afterRouteOpen :
      Search.reachable 1 Lineage.dutyPublicAuthoritySourceLineageGraph
        afterPositiveActFacts Cullen.cullenDutyProposition ≡ true
    proofRelevantAfterRoute :
      Algebra.Reachable Lineage.dutyPublicAuthoritySourceLineageGraph
        afterPositiveActFacts Cullen.cullenDutyProposition
    beforeCutAbsent :
      CutGuard.searchReachableMinimalCut 1
        Lineage.dutyPublicAuthoritySourceLineageGraph
        beforePositiveActFacts Cullen.cullenDutyProposition
      ≡ Search.notFound
    afterCutIsCullenRatio :
      CutGuard.searchReachableMinimalCut 1
        Lineage.dutyPublicAuthoritySourceLineageGraph
        afterPositiveActFacts Cullen.cullenDutyProposition
      ≡ Search.found
        (Search.ruleKey Lineage.cullenPositiveOperationalDutyRule ∷ [])

open SourceLineagePositiveActRerun public

sourceLineagePositiveActRerun : SourceLineagePositiveActRerun
sourceLineagePositiveActRerun = source-lineage-positive-act-rerun
  positiveActRefinementReceipt
  cullenDutyUnreachableBeforePositiveAct
  cullenDutyReachableAfterPositiveAct
  cullenDutyProofAfterPositiveAct
  noGuardedCutBeforePositiveAct
  cullenRatioCutAfterPositiveAct

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PositiveOperationalActAloneCreatesDuty : Set where
data OpenCullenRouteTransfersToClimate : Set where
data MinimalCutMakesRuleNormativelyDesirable : Set where

positiveActStillNeedsOtherMaterialFeatures :
  PositiveOperationalActAloneCreatesDuty → ⊥
positiveActStillNeedsOtherMaterialFeatures ()

specificOpenRouteStillDoesNotTransfer : OpenCullenRouteTransfersToClimate → ⊥
specificOpenRouteStillDoesNotTransfer ()

cutDoesNotCreateNormativeEndorsement : MinimalCutMakesRuleNormativelyDesirable → ⊥
cutDoesNotCreateNormativeEndorsement ()
