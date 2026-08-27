module DASHI.Core.LacanIrigarayTernaryGrammarBridgeExact where

------------------------------------------------------------------------
-- LACAN / IRIGARAY SHARED-CARRIER, DIFFERENT-GRAMMAR BRIDGE
--
-- This module proves the repository-level distinction requested in the DASHI
-- discussion:
--
--   same 0/1/2 carrier != same relational grammar.
--
-- Lacan's finite comparison graph is One-centred:
--
--   0 <- 1 -> 2
--
-- Irigaray's finite labial graph is reciprocal-contact-centred:
--
--   1 <-> 2
--
-- with 0 typed as a neither-one-nor-two classification-refusal role rather
-- than as a master center.
--
-- The proof below checks all six explicit relabellings of the shared ternary
-- carrier.  Thus the two finite directed graphs are not made identical by any
-- inhabitant of the closed TernaryPermutation enumeration.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.TernaryRoleCarrierExact as Ternary
import DASHI.Core.LacanFregeTernaryRoleChartExact as Lacan
import DASHI.Core.IrigarayLabialRelationalCarrierExact as Irigaray

------------------------------------------------------------------------
-- Grammar preservation under a candidate ternary relabelling.
------------------------------------------------------------------------

GrammarPreserving : Ternary.TernaryPermutation → Set
GrammarPreserving permutation =
  (left right : Ternary.TernaryRoleCode) →
  Lacan.lacanOneCentredEdge left right
  ≡ Irigaray.irigarayReciprocalEdge
      (Ternary.permute permutation left)
      (Ternary.permute permutation right)

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

identityFails :
  GrammarPreserving Ternary.identityPermutation → ⊥
identityFails preservation =
  trueNotFalse (preservation Ternary.code1 Ternary.code0)

swap01Fails :
  GrammarPreserving Ternary.swap01Permutation → ⊥
swap01Fails preservation =
  falseNotTrue (preservation Ternary.code0 Ternary.code2)

swap02Fails :
  GrammarPreserving Ternary.swap02Permutation → ⊥
swap02Fails preservation =
  falseNotTrue (preservation Ternary.code0 Ternary.code1)

swap12Fails :
  GrammarPreserving Ternary.swap12Permutation → ⊥
swap12Fails preservation =
  trueNotFalse (preservation Ternary.code1 Ternary.code0)

cycle012Fails :
  GrammarPreserving Ternary.cycle012Permutation → ⊥
cycle012Fails preservation =
  falseNotTrue (preservation Ternary.code0 Ternary.code1)

cycle021Fails :
  GrammarPreserving Ternary.cycle021Permutation → ⊥
cycle021Fails preservation =
  falseNotTrue (preservation Ternary.code0 Ternary.code2)

noTernaryRelabellingPreservesGrammar :
  (permutation : Ternary.TernaryPermutation) →
  GrammarPreserving permutation → ⊥
noTernaryRelabellingPreservesGrammar Ternary.identityPermutation = identityFails
noTernaryRelabellingPreservesGrammar Ternary.swap01Permutation = swap01Fails
noTernaryRelabellingPreservesGrammar Ternary.swap02Permutation = swap02Fails
noTernaryRelabellingPreservesGrammar Ternary.swap12Permutation = swap12Fails
noTernaryRelabellingPreservesGrammar Ternary.cycle012Permutation = cycle012Fails
noTernaryRelabellingPreservesGrammar Ternary.cycle021Permutation = cycle021Fails

------------------------------------------------------------------------
-- The useful theorem is not a cross-type equality test between Lacanian and
-- Irigarayan roles.  Their role codomains are intentionally distinct.  The
-- structural comparison is the exact grammar obstruction above.
------------------------------------------------------------------------

record LacanIrigarayGrammarBoundary : Set where
  constructor lacan-irigaray-grammar-boundary
  field
    sameTernaryCarrierImpliesSameRoleSemantics : Bool
    sameTernaryCarrierImpliesSameRoleSemanticsIsFalse :
      sameTernaryCarrierImpliesSameRoleSemantics ≡ false
    irigarayIsSignFlipOfLacan : Bool
    irigarayIsSignFlipOfLacanIsFalse : irigarayIsSignFlipOfLacan ≡ false
    irigarayIsPermutationOfLacanGraph : Bool
    irigarayIsPermutationOfLacanGraphIsFalse :
      irigarayIsPermutationOfLacanGraph ≡ false
    finiteGraphExhaustsEitherTheory : Bool
    finiteGraphExhaustsEitherTheoryIsFalse :
      finiteGraphExhaustsEitherTheory ≡ false
    zeroHasSameMeaningInBothCharts : Bool
    zeroHasSameMeaningInBothChartsIsFalse :
      zeroHasSameMeaningInBothCharts ≡ false

canonicalLacanIrigarayGrammarBoundary : LacanIrigarayGrammarBoundary
canonicalLacanIrigarayGrammarBoundary =
  lacan-irigaray-grammar-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
