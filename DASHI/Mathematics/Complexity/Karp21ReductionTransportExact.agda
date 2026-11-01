module DASHI.Mathematics.Complexity.Karp21ReductionTransportExact where

------------------------------------------------------------------------
-- PRIMARY-SOURCE ROOTS
-- Stephen A. Cook (1971), "The Complexity of Theorem-Proving Procedures",
-- DOI: 10.1145/800157.805047.
-- Richard M. Karp (1972), "Reducibility Among Combinatorial Problems",
-- in Complexity of Computer Computations, pp. 85-103,
-- DOI: 10.1007/978-1-4684-2001-2_9.
--
-- DASHI PROOF OWNERSHIP
-- This module reuses PolynomialReductionExact, proving transport of
-- NP-hardness/NP-completeness along supplied polynomial many-one reductions.
-- It does not claim to have constructed Karp's 21 instance transformations,
-- their concrete polynomial clocks, or the Cook-Levin theorem.
------------------------------------------------------------------------

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR

-- NP-hardness is a reduction from every language already known to be in NP.
record NPHard
    {Word : Set}
    (cost : PR.PolynomialCostModel Word)
    (target : PR.Language Word) : Setω where
  field
    everyNPReduces : ∀ language →
      PR.InNP cost language →
      PR.PolynomialManyOneReduction cost language target

open NPHard public

npCompleteIsHard :
  ∀ {Word} {cost : PR.PolynomialCostModel Word} {target} →
  PR.NPComplete cost target → NPHard cost target
npCompleteIsHard complete = record
  { everyNPReduces = PR.everyNPLanguageReduces complete }

transportNPHard :
  ∀ {Word} {cost : PR.PolynomialCostModel Word}
    (composition : PR.PolynomialMapComposition cost)
    {source target} →
  NPHard cost source →
  PR.PolynomialManyOneReduction cost source target →
  NPHard cost target
transportNPHard composition hard reduction = record
  { everyNPReduces = λ language languageNP →
      PR.composeReduction composition
        (everyNPReduces hard language languageNP)
        reduction
  }

transportNPComplete :
  ∀ {Word} {cost : PR.PolynomialCostModel Word}
    (composition : PR.PolynomialMapComposition cost)
    {source target} →
  PR.NPComplete cost source →
  PR.PolynomialManyOneReduction cost source target →
  PR.InNP cost target →
  PR.NPComplete cost target
transportNPComplete composition complete reduction targetNP = record
  { PR.targetInNP = targetNP
  ; PR.everyNPLanguageReduces = λ language languageNP →
      PR.composeReduction composition
        (PR.everyNPLanguageReduces complete language languageNP)
        reduction
  }
