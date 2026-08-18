module DASHI.Moonshine.P11JacquetLanglandsRepresentationStandardAuthorityExact where

------------------------------------------------------------------------
-- STANDARD IMPORTED REPRESENTATION-LEVEL JACQUET--LANGLANDS AUTHORITY
--
-- Hervé Jacquet and Robert P. Langlands,
-- "Automorphic Forms on GL(2), Part 1",
-- Lecture Notes in Mathematics 114, Springer, 1970.
-- DOI: 10.1007/BFb0058988.
--
-- Kimball Martin,
-- "The basis problem revisited",
-- Transactions of the American Mathematical Society 373 (2020), 4523--4559.
-- DOI: 10.1090/tran/8077.
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- SOURCE ROLE
--
-- The definite quaternion algebra of discriminant 11 and the unique weight-2
-- level-11 cuspidal eigenform determine corresponding automorphic
-- representations under Jacquet--Langlands.  At every place away from the
-- quaternion discriminant, in particular at 2, the local component is a
-- GL_2(Q_2) representation.  Because the classical level is 11, the local
-- component at 2 is unramified.
--
-- Martin explicitly emphasizes that the modular-form-level JL map is
-- non-canonical.  Accordingly this module imports SAME REPRESENTATION data,
-- not a canonical map between invariant spaces for different compact opens.
--
-- DASHI DISCIPLINE
--
-- The exact Brandt calculations a_2=-2, a_3=-1, a_5=1 already present in the
-- repository identify the concrete p=11 eigenpacket consumed here.  They are
-- regressions for the chosen packet, not a replacement proof of the classical
-- Jacquet--Langlands theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])

import DASHI.Moonshine.P11BrandtPrimeGeneratorsExact as Brandt

------------------------------------------------------------------------
-- Abstract representation carriers exist ONLY at the standard source boundary.
------------------------------------------------------------------------

postulate
  AutomorphicRepresentation : Set
  LocalGL2Q2Representation : Set

  localAtTwo : AutomorphicRepresentation → LocalGL2Q2Representation

  p11ClassicalNewformRepresentation : AutomorphicRepresentation
  p11QuaternionBrandtRepresentation : AutomorphicRepresentation

  -- Classical Jacquet--Langlands same-representation authority.
  p11JacquetLanglandsSameGlobalRepresentation :
    p11QuaternionBrandtRepresentation ≡ p11ClassicalNewformRepresentation

  -- Standard local-newform fact for this representation at the good prime 2.
  UnramifiedAtTwo : LocalGL2Q2Representation → Set

  p11ClassicalLocalAtTwoUnramified :
    UnramifiedAtTwo (localAtTwo p11ClassicalNewformRepresentation)

------------------------------------------------------------------------
-- Local sameness is derived; it is not a second imported identification.
------------------------------------------------------------------------

p11JacquetLanglandsSameLocalAtTwo :
  localAtTwo p11QuaternionBrandtRepresentation
  ≡ localAtTwo p11ClassicalNewformRepresentation
p11JacquetLanglandsSameLocalAtTwo =
  cong localAtTwo p11JacquetLanglandsSameGlobalRepresentation

p11QuaternionLocalAtTwoUnramified :
  UnramifiedAtTwo (localAtTwo p11QuaternionBrandtRepresentation)
p11QuaternionLocalAtTwoUnramified
  rewrite p11JacquetLanglandsSameLocalAtTwo =
  p11ClassicalLocalAtTwoUnramified

------------------------------------------------------------------------
-- Exact finite packet regressions already constructed on the Brandt side.
------------------------------------------------------------------------

p11BrandtA2 : ℤ
p11BrandtA2 = Brandt.level11a2

p11BrandtA3 : ℤ
p11BrandtA3 = Brandt.level11a3

p11BrandtA5 : ℤ
p11BrandtA5 = Brandt.level11a5

p11BrandtA2IsMinusTwo : p11BrandtA2 ≡ -[1+ 1 ]
p11BrandtA2IsMinusTwo = refl

p11BrandtA3IsMinusOne : p11BrandtA3 ≡ -[1+ 0 ]
p11BrandtA3IsMinusOne = refl

p11BrandtA5IsOne : p11BrandtA5 ≡ + 1
p11BrandtA5IsOne = refl

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record P11JacquetLanglandsRepresentationAuthorityBoundary : Set where
  field
    representationLevelJLImported : Bool
    localAtTwoSamenessDerived : Bool
    localAtTwoUnramified : Bool
    finiteBrandtPacketRegressed : Bool
    canonicalK2ToK0FixedSpaceMapImported : Bool
    noncanonicalModularFormMapRespected : Bool

canonicalP11JacquetLanglandsRepresentationAuthorityBoundary :
  P11JacquetLanglandsRepresentationAuthorityBoundary
canonicalP11JacquetLanglandsRepresentationAuthorityBoundary = record
  { representationLevelJLImported = true
  ; localAtTwoSamenessDerived = true
  ; localAtTwoUnramified = true
  ; finiteBrandtPacketRegressed = true
  ; canonicalK2ToK0FixedSpaceMapImported = false
  ; noncanonicalModularFormMapRespected = true
  }
