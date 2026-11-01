module DASHI.Philosophy.ContextValuation where

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false)

------------------------------------------------------------------------
-- Multiple coherent valuations can inhabit one carrier.
--
-- This does not imply that all perspectives or claims are equally true.

record RelevanceValuation (X Value : Set) : Set₁ where
  field
    compare :
      X →
      X →
      Value

    valuationContext :
      Set

    admissibilityWitness :
      Set

open RelevanceValuation public

record ValuationIndexedClaim
       (Claim Context Evidence Authority X Value : Set) : Set₁ where
  field
    claim :
      Claim

    context :
      Context

    valuation :
      RelevanceValuation X Value

    evidence :
      Evidence

    authority :
      Authority

    valuationDependenceVisible :
      Set

    allValuationsEquivalent :
      Bool

open ValuationIndexedClaim public

record PluralValuationBoundary
       (X V₁ V₂ : Set)
       (first : RelevanceValuation X V₁)
       (second : RelevanceValuation X V₂) : Set₁ where
  field
    firstIsCoherent :
      Set

    secondIsCoherent :
      Set

    sameCarrier :
      Set

    comparisonsNeedNotAgree :
      Set

    noArbitraryEquivalence :
      Set

open PluralValuationBoundary public
