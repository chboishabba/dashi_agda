module DASHI.Moonshine.CasselmanUnramifiedPGL2FixedVectorTowerExact where

------------------------------------------------------------------------
-- STANDARD IMPORTED LOCAL NEWFORM AUTHORITY, SPECIALIZED TO CONDUCTOR ZERO
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
-- Schmidt Theorem 1.2.1 gives, for conductor c(pi),
--
--   dim V(n) = n - c(pi) + 1.
--
-- In §3.1 he further states that for PGL_2(F), i.e. trivial central character,
-- K_0(p^n)-invariance is equivalent to Casselman's K_2(n)-invariance.
-- Therefore for the UNRAMIFIED local component at 2, c(pi)=0 and
--
--   dim V^{K_0(2^n)} = n+1.
--
-- In particular n=2 gives the three-dimensional K_0(4)-fixed oldspace.
--
-- IMPORTANT NOTATION / CARRIER BOUNDARY
-- Casselman's K_2(2) is not the principal congruence kernel
-- ker(GL_2(Z_2)->GL_2(F_2)) used for full level-2 marking.  Both produce a
-- three-dimensional object in this programme, but dimension equality is not a
-- same-object theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Local subgroup roles remain type-distinct.
------------------------------------------------------------------------

data TwoAdicFixedVectorRole : Set where
  casselmanK2Level : Nat → TwoAdicFixedVectorRole
  gamma0K0Level : Nat → TwoAdicFixedVectorRole
  principalFullLevel2Kernel : TwoAdicFixedVectorRole

casselmanLevel2 : TwoAdicFixedVectorRole
casselmanLevel2 = casselmanK2Level 2

gamma0Level4 : TwoAdicFixedVectorRole
gamma0Level4 = gamma0K0Level 2

principalLevel2 : TwoAdicFixedVectorRole
principalLevel2 = principalFullLevel2Kernel

casselmanLevel2NotPrincipalLevel2 :
  casselmanLevel2 ≡ principalLevel2 → ⊥
casselmanLevel2NotPrincipalLevel2 ()

gamma0Level4NotPrincipalLevel2 :
  gamma0Level4 ≡ principalLevel2 → ⊥
gamma0Level4NotPrincipalLevel2 ()

------------------------------------------------------------------------
-- Exact conductor-zero specialization of the published dimension theorem.
------------------------------------------------------------------------

record UnramifiedPGL2FixedVectorTower : Set where
  field
    fixedDimension : Nat → Nat
    dimensionLaw : (n : Nat) → fixedDimension n ≡ suc n
    trivialCentralCharacter : Bool
    trivialCentralCharacterIsTrue : trivialCentralCharacter ≡ true
    k0AndCasselmanK2FixedSpacesAgree : Bool
    k0AndCasselmanK2FixedSpacesAgreeIsTrue :
      k0AndCasselmanK2FixedSpacesAgree ≡ true

open UnramifiedPGL2FixedVectorTower public

postulate
  publishedP11LocalUnramifiedTower : UnramifiedPGL2FixedVectorTower

level4FixedDimensionIsThree :
  fixedDimension publishedP11LocalUnramifiedTower 2 ≡ 3
level4FixedDimensionIsThree =
  dimensionLaw publishedP11LocalUnramifiedTower 2

record CasselmanUnramifiedTowerBoundary : Set where
  field
    conductorZeroDimensionLawImported : Bool
    pgl2K0EqualsCasselmanK2Imported : Bool
    level4DimensionThreeDerived : Bool
    principalFullLevel2KernelIdentifiedWithK0Level4 : Bool
    explicitLocalComparisonMapConstructed : Bool

canonicalCasselmanUnramifiedTowerBoundary : CasselmanUnramifiedTowerBoundary
canonicalCasselmanUnramifiedTowerBoundary = record
  { conductorZeroDimensionLawImported = true
  ; pgl2K0EqualsCasselmanK2Imported = true
  ; level4DimensionThreeDerived = true
  ; principalFullLevel2KernelIdentifiedWithK0Level4 = false
  ; explicitLocalComparisonMapConstructed = false
  }
