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
import DASHI.Cognition.PNF.SensibLawCullenSourceCorrectDutyRoutesExact as Cullen
import DASHI.Cognition.PNF.SensibLawDutyPublicAuthoritySourceLineageGraphExact as Lineage

------------------------------------------------------------------------
-- SOURCE-LINEAGE REFINEMENT / CUT RERUN
--
-- On the source-correct Joint-reasons fibre, hold foreseeable-risk and
-- police-function context fixed while withholding the positive operational act.
-- Then append only that source-owned factual feature.  The graph is unchanged;
-- reachability and the guarded cut are recomputed.
--
-- No statutory-power premise is used here.
------------------------------------------------------------------------

beforePositiveActFacts : Algebra.FactSet
beforePositiveActFacts = Algebra.fact-set
  (Cullen.foreseeablePhysicalInjuryRisk ∷
   Cullen.policeFunctionContext ∷ [])

afterPositiveActFacts : Algebra.FactSet
afterPositiveActFacts = Lineage.cullenHoldingFacts

sameLineageGraphPreserved :
  Refinement.GraphRefinement
    Lineage.dutyPublicAuthoritySourceLineageGraph
    Lineage.dutyPublicAuthoritySourceLineageGraph
sameLineageGraphPreserved = Refinement.graph-refinement
  (λ membership → membership)
  (λ membership → membership)
  "no rule added: same Mallonland / Cullen-Joint / Cullen-Edelman / Pabai graph"
  "no source added: same source carriers"

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
  "append Cullen positive-operational-act material feature on Joint-reasons fibre"

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
-- After refinement the source-correct Joint-reasons reconstruction edge is the
-- first inclusion-minimal guarded cut on this fact fibre.
------------------------------------------------------------------------

noGuardedCutBeforePositiveAct :
  CutGuard.searchReachableMinimalCut 1
    Lineage.dutyPublicAuthoritySourceLineageGraph
    beforePositiveActFacts Cullen.cullenDutyProposition
  ≡ Search.notFound
noGuardedCutBeforePositiveAct = refl

cullenJointRouteCutAfterPositiveAct :
  CutGuard.searchReachableMinimalCut 1
    Lineage.dutyPublicAuthoritySourceLineageGraph
    afterPositiveActFacts Cullen.cullenDutyProposition
  ≡ Search.found (Search.ruleKey Lineage.cullenPositiveOperationalDutyRule ∷ [])
cullenJointRouteCutAfterPositiveAct = refl

-- Compatibility theorem name for existing aggregate consumers.  The rule is no
-- longer asserted here to be a binding-ratio edge; it is the source-correct
-- Joint-reasons DASHI reconstruction.
cullenRatioCutAfterPositiveAct :
  CutGuard.searchReachableMinimalCut 1
    Lineage.dutyPublicAuthoritySourceLineageGraph
    afterPositiveActFacts Cullen.cullenDutyProposition
  ≡ Search.found (Search.ruleKey Lineage.cullenPositiveOperationalDutyRule ∷ [])
cullenRatioCutAfterPositiveAct = cullenJointRouteCutAfterPositiveAct

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
    afterCutIsJointRoute :
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
  cullenJointRouteCutAfterPositiveAct

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PositiveOperationalActAloneCreatesDuty : Set where
data OpenCullenRouteTransfersToClimate : Set where
data MinimalCutMakesRuleNormativelyDesirable : Set where
data GuardedCutPromotesReconstructionToRatio : Set where

positiveActStillNeedsOtherMaterialFeatures :
  PositiveOperationalActAloneCreatesDuty → ⊥
positiveActStillNeedsOtherMaterialFeatures ()

specificOpenRouteStillDoesNotTransfer : OpenCullenRouteTransfersToClimate → ⊥
specificOpenRouteStillDoesNotTransfer ()

cutDoesNotCreateNormativeEndorsement : MinimalCutMakesRuleNormativelyDesirable → ⊥
cutDoesNotCreateNormativeEndorsement ()

cutDoesNotChangeAuthorityRole : GuardedCutPromotesReconstructionToRatio → ⊥
cutDoesNotChangeAuthorityRole ()
