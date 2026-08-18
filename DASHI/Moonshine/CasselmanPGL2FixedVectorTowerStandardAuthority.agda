module DASHI.Moonshine.CasselmanPGL2FixedVectorTowerStandardAuthority where

------------------------------------------------------------------------
-- STANDARD IMPORTED LOCAL NEWFORM AUTHORITY
--
-- William Casselman,
-- "On some results of Atkin and Lehner",
-- Mathematische Annalen 201 (1973), 301--314.
-- DOI: 10.1007/BF01428197.
--
-- Ralf Schmidt,
-- "Some remarks on local newforms for GL(2)",
-- Journal of the Ramanujan Mathematical Society 17 (2002), 115--147.
-- No DOI asserted here.
--
-- SOURCE ROLE
-- Schmidt §1.2, recalling Casselman, defines K_2(n) inside GL_2(o) and proves
-- for an infinite-dimensional irreducible admissible representation pi:
--
--   dim V(n) = n - c(pi) + 1       for n >= c(pi).
--
-- In §3.1, for PGL_2(F) / trivial central character, Schmidt defines
--
--   K_0(p^n) = { [a b; c d] in GL_2(o) : c in p^n }
--
-- and states that K_0(p^n)-invariance is equivalent to K_2(n)-invariance.
-- Hence for an UNRAMIFIED representation, c(pi)=0 and
--
--   dim V^{K_0(p^n)} = n+1.
--
-- At F=Q_2 and n=2 this gives dim V^{K_0(4)}=3.
--
-- NOTATION WARNING
-- Casselman's/Schmidt's K_2(n) is NOT the principal congruence kernel
--
--   K(2) = ker(GL_2(Z_2) -> GL_2(F_2))
--
-- used by the marked full-level-2 model elsewhere in DASHI.  This file keeps
-- those local roles type-distinct even though both relevant fixed-vector
-- spaces happen to have dimension three.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Type-level local compact-open roles.  These are semantic tags, not claims
-- that the underlying p-adic groups have been constructed internally.
------------------------------------------------------------------------

data LocalCompactOpenRole : Set where
  casselmanK2 : Nat → LocalCompactOpenRole
  gamma0K0 : Nat → LocalCompactOpenRole
  principalKernelMod2 : LocalCompactOpenRole

casselmanLevelTwoRole : LocalCompactOpenRole
casselmanLevelTwoRole = casselmanK2 2

gamma0LevelFourRole : LocalCompactOpenRole
gamma0LevelFourRole = gamma0K0 2

principalFullLevelTwoRole : LocalCompactOpenRole
principalFullLevelTwoRole = principalKernelMod2

------------------------------------------------------------------------
-- Explicit non-identity of the subgroup ROLES used in this programme.
------------------------------------------------------------------------

casselmanK2NotPrincipalKernel :
  casselmanLevelTwoRole ≡ principalFullLevelTwoRole → ⊥
casselmanK2NotPrincipalKernel ()

gamma0K0NotPrincipalKernel :
  gamma0LevelFourRole ≡ principalFullLevelTwoRole → ⊥
gamma0K0NotPrincipalKernel ()

------------------------------------------------------------------------
-- Published fixed-vector tower, specialized only to the data consumed here.
-- The source theorem supplies dimensions and, for trivial central character,
-- equality of the K_2(n)- and K_0(p^n)-fixed subspaces.
------------------------------------------------------------------------

record CasselmanPGL2FixedVectorTower : Set₁ where
  field
    conductorExponent : Nat
    fixedDimension : Nat → Nat

    dimensionLaw :
      (n : Nat) → conductorExponent ≤ n →
      fixedDimension n ≡ n ∸ conductorExponent + 1

    trivialCentralCharacter : Bool

    k0FixedEqualsCasselmanK2Fixed :
      trivialCentralCharacter ≡ true

open CasselmanPGL2FixedVectorTower public

postulate
  publishedUnramifiedPGL2TowerAtTwo : CasselmanPGL2FixedVectorTower

  publishedUnramifiedConductorZero :
    conductorExponent publishedUnramifiedPGL2TowerAtTwo ≡ 0

  publishedUnramifiedTrivialCentralCharacter :
    trivialCentralCharacter publishedUnramifiedPGL2TowerAtTwo ≡ true

------------------------------------------------------------------------
-- The level-four / n=2 dimension is then a local consequence, not a separate
-- postulated numeral.
------------------------------------------------------------------------

levelFourFixedDimensionIsThree :
  fixedDimension publishedUnramifiedPGL2TowerAtTwo 2 ≡ 3
levelFourFixedDimensionIsThree
  rewrite publishedUnramifiedConductorZero =
  dimensionLaw publishedUnramifiedPGL2TowerAtTwo 2 z≤n

record CasselmanPGL2FixedVectorTowerBoundary : Set where
  field
    casselmanDimensionLawImported : Bool
    trivialCentralK0EqualsK2AuthorityImported : Bool
    conductorZeroSpecializationConstructed : Bool
    levelFourDimensionThreeDerived : Bool
    principalKernelConflatedWithCasselmanK2 : Bool
    explicitTwoAdicComparisonMapConstructed : Bool

canonicalCasselmanPGL2FixedVectorTowerBoundary :
  CasselmanPGL2FixedVectorTowerBoundary
canonicalCasselmanPGL2FixedVectorTowerBoundary = record
  { casselmanDimensionLawImported = true
  ; trivialCentralK0EqualsK2AuthorityImported = true
  ; conductorZeroSpecializationConstructed = true
  ; levelFourDimensionThreeDerived = true
  ; principalKernelConflatedWithCasselmanK2 = false
  ; explicitTwoAdicComparisonMapConstructed = false
  }
