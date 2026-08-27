module DASHI.Core.CriticalGrammarRelabellingBoundaryExact where

------------------------------------------------------------------------
-- GRAMMAR RELABELLING != SEMANTIC / HISTORICAL IDENTITY
--
-- INTERNAL THEOREM-PATTERN PROVENANCE
--
-- Draft PR #617 proves that equal-cardinality carriers can fail equivariance
-- because orbit/action structure differs.  Here we use the complementary case:
-- two source-calibrated finite graphs can be exactly relabelled while their role
-- semantics and historical genealogy remain intentionally distinct.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.TernaryRoleCarrierExact as Ternary
import DASHI.Core.LacanFregeTernaryRoleChartExact as Lacan
import DASHI.Core.CriticalThirdnessRoleGrammarExact as Thirdness

------------------------------------------------------------------------
-- Lacan comparison-star and Bhabha generative-star are graph-isomorphic under
-- swap01.  This is a finite DASHI graph fact only.
------------------------------------------------------------------------

lacanBhabhaSwap01 :
  (left right : Ternary.TernaryRoleCode) →
  Lacan.lacanOneCentredEdge left right
  ≡ Thirdness.bhabhaGenerativeEdge
      (Ternary.permute Ternary.swap01Permutation left)
      (Ternary.permute Ternary.swap01Permutation right)
lacanBhabhaSwap01 Ternary.code0 Ternary.code0 = refl
lacanBhabhaSwap01 Ternary.code0 Ternary.code1 = refl
lacanBhabhaSwap01 Ternary.code0 Ternary.code2 = refl
lacanBhabhaSwap01 Ternary.code1 Ternary.code0 = refl
lacanBhabhaSwap01 Ternary.code1 Ternary.code1 = refl
lacanBhabhaSwap01 Ternary.code1 Ternary.code2 = refl
lacanBhabhaSwap01 Ternary.code2 Ternary.code0 = refl
lacanBhabhaSwap01 Ternary.code2 Ternary.code1 = refl
lacanBhabhaSwap01 Ternary.code2 Ternary.code2 = refl

------------------------------------------------------------------------
-- Anzaldua's bidirectional border relation is not relabelled into Bhabha's
-- outward-only generative relation by any closed ternary permutation.
------------------------------------------------------------------------

AnzalduaBhabhaPreserving : Ternary.TernaryPermutation → Set
AnzalduaBhabhaPreserving permutation =
  (left right : Ternary.TernaryRoleCode) →
  Thirdness.anzalduaPluralEdge left right
  ≡ Thirdness.bhabhaGenerativeEdge
      (Ternary.permute permutation left)
      (Ternary.permute permutation right)

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

identityFails : AnzalduaBhabhaPreserving Ternary.identityPermutation → ⊥
identityFails preservation =
  trueNotFalse (preservation Ternary.code1 Ternary.code0)

swap01Fails : AnzalduaBhabhaPreserving Ternary.swap01Permutation → ⊥
swap01Fails preservation =
  trueNotFalse (preservation Ternary.code0 Ternary.code1)

swap02Fails : AnzalduaBhabhaPreserving Ternary.swap02Permutation → ⊥
swap02Fails preservation =
  trueNotFalse (preservation Ternary.code0 Ternary.code2)

swap12Fails : AnzalduaBhabhaPreserving Ternary.swap12Permutation → ⊥
swap12Fails preservation =
  trueNotFalse (preservation Ternary.code1 Ternary.code0)

cycle012Fails : AnzalduaBhabhaPreserving Ternary.cycle012Permutation → ⊥
cycle012Fails preservation =
  trueNotFalse (preservation Ternary.code0 Ternary.code1)

cycle021Fails : AnzalduaBhabhaPreserving Ternary.cycle021Permutation → ⊥
cycle021Fails preservation =
  trueNotFalse (preservation Ternary.code0 Ternary.code2)

noAnzalduaBhabhaTernaryRelabelling :
  (permutation : Ternary.TernaryPermutation) →
  AnzalduaBhabhaPreserving permutation → ⊥
noAnzalduaBhabhaTernaryRelabelling Ternary.identityPermutation = identityFails
noAnzalduaBhabhaTernaryRelabelling Ternary.swap01Permutation = swap01Fails
noAnzalduaBhabhaTernaryRelabelling Ternary.swap02Permutation = swap02Fails
noAnzalduaBhabhaTernaryRelabelling Ternary.swap12Permutation = swap12Fails
noAnzalduaBhabhaTernaryRelabelling Ternary.cycle012Permutation = cycle012Fails
noAnzalduaBhabhaTernaryRelabelling Ternary.cycle021Permutation = cycle021Fails

record CriticalGrammarRelabellingBoundary : Set where
  constructor critical-grammar-relabelling-boundary
  field
    graphIsomorphismImpliesSameHistoricalTheory : Bool
    graphIsomorphismImpliesSameHistoricalTheoryIsFalse :
      graphIsomorphismImpliesSameHistoricalTheory ≡ false
    graphIsomorphismImpliesSameRoleSemantics : Bool
    graphIsomorphismImpliesSameRoleSemanticsIsFalse :
      graphIsomorphismImpliesSameRoleSemantics ≡ false
    sameCarrierImpliesGraphIsomorphism : Bool
    sameCarrierImpliesGraphIsomorphismIsFalse :
      sameCarrierImpliesGraphIsomorphism ≡ false
    graphNonisomorphismImpliesEmpiricalConflict : Bool
    graphNonisomorphismImpliesEmpiricalConflictIsFalse :
      graphNonisomorphismImpliesEmpiricalConflict ≡ false

canonicalCriticalGrammarRelabellingBoundary : CriticalGrammarRelabellingBoundary
canonicalCriticalGrammarRelabellingBoundary =
  critical-grammar-relabelling-boundary false refl false refl false refl false refl
