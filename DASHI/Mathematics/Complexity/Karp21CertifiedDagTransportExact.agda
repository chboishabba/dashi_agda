module DASHI.Mathematics.Complexity.Karp21CertifiedDagTransportExact where

------------------------------------------------------------------------
-- ORIGINAL AUTHORITIES
-- Stephen A. Cook (1971), DOI: 10.1145/800157.805047.
-- Richard M. Karp (1972), DOI: 10.1007/978-1-4684-2001-2_9.
--
-- DASHI contribution:
--   one generic *proof compiler* for all 21 historical targets, consuming
--   the 20 actual costed source-to-target reductions, NP-membership
--   certificates, and the SAT NP-completeness root.
-- The historical DAG's source-written edges are *names*, not witnesses.
-- THIS THEOREM IS CONDITIONAL ON THE ABOVE REAL RECORDS. No vacuous
-- Boolean success flags, solver oracles, or claimed P != NP conclusion.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21HistoricalDagExact as Dag
import DASHI.Mathematics.Complexity.Karp21ReductionTransportExact as Transfer

record CertifiedKarpNetwork
    {Word : Set}
    (cost : PR.PolynomialCostModel Word)
    (language : Dag.Problem → PR.Language Word) : Setω where
  field
    polynomialComposition :
      PR.PolynomialMapComposition cost

    satRootIsNPComplete :
      PR.NPComplete cost (language Dag.sat)

    membershipForEachNode :
      (p : Dag.Problem) →
      PR.InNP cost (language p)

    certifiedReductionForEachEdge :
      (edge : Dag.Edge) →
      PR.PolynomialManyOneReduction
        cost
        (language (Dag.source edge))
        (language (Dag.target edge))

open CertifiedKarpNetwork public

-- Structural recursion occurs on the *reachability proof*, not on an
-- unrelated problem identifier. Every recursive step consumes the
-- actual polynomial reduction and the target's NP-membership witness.
npCompleteAlongReachability :
  ∀ {Word} {cost : PR.PolynomialCostModel Word}
    {language : Dag.Problem → PR.Language Word} →
  (network : CertifiedKarpNetwork cost language) →
  ∀ {p} → Dag.Reachable p → PR.NPComplete cost (language p)
npCompleteAlongReachability network Dag.satRoot =
  satRootIsNPComplete network
npCompleteAlongReachability network (Dag.useEdge edge reachSource) =
  Transfer.transportNPComplete
    (polynomialComposition network)
    (npCompleteAlongReachability network reachSource)
    (certifiedReductionForEachEdge network edge)
    (membershipForEachNode network (Dag.target edge))

allTwentyOneNPCompleteIfCertified :
  ∀ {Word} {cost : PR.PolynomialCostModel Word}
    {language : Dag.Problem → PR.Language Word} →
  (network : CertifiedKarpNetwork cost language) →
  (p : Dag.Problem) → PR.NPComplete cost (language p)
allTwentyOneNPCompleteIfCertified network p =
  npCompleteAlongReachability network
    (Dag.allNodesHistoricallyReachable p)

anyKarpTargetInPImpliesPEqualsNP :
  ∀ {Word} {cost : PR.PolynomialCostModel Word}
    {language : Dag.Problem → PR.Language Word} →
  (network : CertifiedKarpNetwork cost language) →
  PR.PIncludedInNP cost →
  (p : Dag.Problem) →
  PR.InP cost (language p) →
  PR.PEqualsNP cost
anyKarpTargetInPImpliesPEqualsNP
  {language = language} network pSubsetNP p targetP =
  PR.npCompleteInPImpliesPEqualsNP
    pSubsetNP
    (language p)
    (allTwentyOneNPCompleteIfCertified network p)
    targetP
