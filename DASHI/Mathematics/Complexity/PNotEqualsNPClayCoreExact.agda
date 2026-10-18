module DASHI.Mathematics.Complexity.PNotEqualsNPClayCoreExact where

------------------------------------------------------------------------
-- P != NP: CLAY-CORE / ESTABLISHED-BACKGROUND SPLIT
--
-- On the existing literal BooleanFormula/Satisfiable carrier:
--
--   SATNotInP := InP(SAT) -> bottom
--
-- This is a clean Clay-facing negative core.  Given standard background:
--
--   * SAT is in NP;
--   * SAT is NP-complete;
--   * P is included in NP;
--
-- SATNotInP is equivalent to P != NP.
--
-- No lower bound is manufactured here.  The new content is the exact compiler
-- between the standard SAT lower-bound statement and the repository's P=NP
-- record, so observer/collision machinery can only discharge the core if it
-- actually proves SATNotInP.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool)
open import Data.Empty using (⊥)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR

SATLanguage : PR.Language Cook.BooleanFormula
SATLanguage = record
  { PR.accepts = Cook.Satisfiable
  }

SATNotInP :
  (cost : PR.PolynomialCostModel Cook.BooleanFormula) →
  Set₁
SATNotInP cost =
  PR.InP cost SATLanguage → ⊥

PNotEqualsNP :
  (cost : PR.PolynomialCostModel Cook.BooleanFormula) →
  Setω
PNotEqualsNP cost =
  PR.PEqualsNP cost → ⊥

record PNotEqualsNPEstablishedBackground
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Setω where
  field
    satInNP : PR.InNP cost SATLanguage
    satNPComplete : PR.NPComplete cost SATLanguage
    pIncludedInNP : PR.PIncludedInNP cost

open PNotEqualsNPEstablishedBackground public

satNotInPImpliesPNotEqualsNP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  PR.InNP cost SATLanguage →
  SATNotInP cost →
  PNotEqualsNP cost
satNotInPImpliesPNotEqualsNP satNP satNotP pEqNP =
  satNotP
    (PR.npToP pEqNP SATLanguage satNP)

pNotEqualsNPImpliesSATNotInP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  PR.PIncludedInNP cost →
  PR.NPComplete cost SATLanguage →
  PNotEqualsNP cost →
  SATNotInP cost
pNotEqualsNPImpliesSATNotInP pSubsetNP completeSAT pNeNP satP =
  pNeNP
    (PR.npCompleteInPImpliesPEqualsNP
      pSubsetNP SATLanguage completeSAT satP)

record PNotEqualsNPClayCoreEquivalence
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Setω where
  constructor p-not-equals-np-clay-core-equivalence
  field
    satLowerBoundToSeparation :
      SATNotInP cost → PNotEqualsNP cost
    separationToSATLowerBound :
      PNotEqualsNP cost → SATNotInP cost

pNotEqualsNPClayCoreIsExactlySATNotInP :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  PNotEqualsNPEstablishedBackground cost →
  PNotEqualsNPClayCoreEquivalence cost
pNotEqualsNPClayCoreIsExactlySATNotInP background =
  p-not-equals-np-clay-core-equivalence
    (satNotInPImpliesPNotEqualsNP
      (satInNP background))
    (pNotEqualsNPImpliesSATNotInP
      (pIncludedInNP background)
      (satNPComplete background))

------------------------------------------------------------------------
-- Candidate-proof boundary.
------------------------------------------------------------------------

record SATLowerBoundProducer
    (cost : PR.PolynomialCostModel Cook.BooleanFormula) : Set₁ where
  field
    satNotPolynomialTime : SATNotInP cost

open SATLowerBoundProducer public

satLowerBoundProducerClosesClayCore :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  PNotEqualsNPEstablishedBackground cost →
  SATLowerBoundProducer cost →
  PNotEqualsNP cost
satLowerBoundProducerClosesClayCore background producer =
  satLowerBoundToSeparation
    (pNotEqualsNPClayCoreIsExactlySATNotInP background)
    (satNotPolynomialTime producer)
