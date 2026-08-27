module DASHI.Core.TernaryRoleCarrierExact where

------------------------------------------------------------------------
-- TERNARY ROLE CARRIER
--
-- A three-symbol carrier is deliberately separated from every interpretation
-- placed on it.  The printed/numeric shape 0/1/2 therefore does not by itself
-- imply cardinality, order, anatomy, psychoanalytic meaning, Base369 meaning,
-- or any other semantic law.
--
-- This is the small common carrier used by the Lacan/Frege and Irigaray
-- source-bridge modules.  It does not identify those projects with Base369;
-- cross-domain carrier coincidence is weaker than semantic/operator identity.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Closed three-code carrier.
------------------------------------------------------------------------

data TernaryRoleCode : Set where
  code0 code1 code2 : TernaryRoleCode

------------------------------------------------------------------------
-- The six explicit permutations of a three-element carrier.
--
-- Keeping these typed lets downstream modules ask whether two relational laws
-- agree up to a relabelling, rather than merely comparing constructor names.
------------------------------------------------------------------------

data TernaryPermutation : Set where
  identityPermutation
  swap01Permutation
  swap02Permutation
  swap12Permutation
  cycle012Permutation
  cycle021Permutation
  : TernaryPermutation

permute : TernaryPermutation → TernaryRoleCode → TernaryRoleCode
permute identityPermutation code0 = code0
permute identityPermutation code1 = code1
permute identityPermutation code2 = code2
permute swap01Permutation code0 = code1
permute swap01Permutation code1 = code0
permute swap01Permutation code2 = code2
permute swap02Permutation code0 = code2
permute swap02Permutation code1 = code1
permute swap02Permutation code2 = code0
permute swap12Permutation code0 = code0
permute swap12Permutation code1 = code2
permute swap12Permutation code2 = code1
permute cycle012Permutation code0 = code1
permute cycle012Permutation code1 = code2
permute cycle012Permutation code2 = code0
permute cycle021Permutation code0 = code2
permute cycle021Permutation code1 = code0
permute cycle021Permutation code2 = code1

------------------------------------------------------------------------
-- Interpretation is data over the carrier, never the carrier itself.
------------------------------------------------------------------------

record RoleChart (Role : Set) : Set where
  constructor role-chart
  field
    interpret : TernaryRoleCode → Role

open RoleChart public

record TernaryRoleCarrierBoundary : Set where
  constructor ternary-role-carrier-boundary
  field
    zeroCodeMeansCardinalityZero : Bool
    zeroCodeMeansCardinalityZeroIsFalse :
      zeroCodeMeansCardinalityZero ≡ false
    codeOrderIsSemanticOrder : Bool
    codeOrderIsSemanticOrderIsFalse : codeOrderIsSemanticOrder ≡ false
    sharedThreeCodeCarrierImpliesSharedSemantics : Bool
    sharedThreeCodeCarrierImpliesSharedSemanticsIsFalse :
      sharedThreeCodeCarrierImpliesSharedSemantics ≡ false
    sharedThreeCodeCarrierImpliesBase369Identity : Bool
    sharedThreeCodeCarrierImpliesBase369IdentityIsFalse :
      sharedThreeCodeCarrierImpliesBase369Identity ≡ false

canonicalTernaryRoleCarrierBoundary : TernaryRoleCarrierBoundary
canonicalTernaryRoleCarrierBoundary =
  ternary-role-carrier-boundary
    false refl
    false refl
    false refl
    false refl
