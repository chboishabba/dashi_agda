module DASHI.Philosophy.PowerAndGrammar where

open import Agda.Primitive using (Set₁)

------------------------------------------------------------------------
-- Power is second-order when it controls the grammar, quotient, evidence
-- policy, or promotion rule through which first-order claims become legible.

record ClaimGrammar (Claim : Set) : Set₁ where
  field
    expressible :
      Claim →
      Set

    admissible :
      Claim →
      Set

    quotientedTogether :
      Claim →
      Claim →
      Set

open ClaimGrammar public

record PromotionPolicy (Claim : Set) : Set₁ where
  field
    evidenceLegible :
      Claim →
      Set

    promotable :
      Claim →
      Set

    residualIgnored :
      Claim →
      Set

open PromotionPolicy public

record SecondOrderPower
       (Claim GrammarCode PolicyCode : Set) : Set₁ where
  field
    grammar :
      ClaimGrammar Claim

    promotion :
      PromotionPolicy Claim

    transformGrammarCode :
      GrammarCode →
      GrammarCode

    transformPolicyCode :
      PolicyCode →
      PolicyCode

    controlsWhichDistinctionsCount :
      Set

    controlsWhichEvidenceIsLegible :
      Set

    controlsWhichClaimsPromote :
      Set

    accountabilityWitness :
      Set

open SecondOrderPower public
