module DASHI.Biology.MoonshineMonsterLieStringBigradingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Richard E. Borcherds,
-- "The Monster Lie Algebra".
-- DOI: 10.1016/0001-8708(90)90067-W.
--
-- Richard E. Borcherds,
-- "Monstrous Moonshine and Monstrous Lie Superalgebras".
-- DOI: 10.1007/BF01232032.
--
-- Reinhold W. Gebert,
-- "Introduction to Vertex Algebras, Borcherds Algebras and the Monster Lie
-- Algebra".
-- DOI: 10.1142/S0217751X93002162.
--
-- Jeffrey A. Harvey and Gregory W. Moore,
-- "Algebras, BPS States, and Strings".
-- DOI: 10.1016/0550-3213(95)00605-2.
--
-- DASHI CONTRIBUTION
--
-- Make the finite beginning of the Monster-Lie bigrading rule explicit.  In
-- Borcherds' construction the root-space multiplicity at bidegree (m,n) is
-- controlled by the normalized-J coefficient c(mn).  The full theorem uses
-- the no-ghost/BRST physical-state construction on the Moonshine module tensored
-- with the Lorentzian lattice VOA.  Here we check the first multiplicities and
-- the product-index degeneracy exactly, without claiming that construction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Biology.MoonshineModularFormCoefficientExact as Modular

data JCoefficientIndex : Set where
  indexMinusOne : JCoefficientIndex
  indexZero : JCoefficientIndex
  indexOne : JCoefficientIndex
  indexTwo : JCoefficientIndex

jCoefficient : JCoefficientIndex → Nat
jCoefficient indexMinusOne = 1
jCoefficient indexZero = 0
jCoefficient indexOne = Modular.jCoefficientOne
jCoefficient indexTwo = Modular.jCoefficientTwo

data SampleRootBidegree : Set where
  degreeOneMinusOne : SampleRootBidegree
  degreeOneZero : SampleRootBidegree
  degreeOneOne : SampleRootBidegree
  degreeOneTwo : SampleRootBidegree
  degreeTwoOne : SampleRootBidegree

productIndex : SampleRootBidegree → JCoefficientIndex
productIndex degreeOneMinusOne = indexMinusOne
productIndex degreeOneZero = indexZero
productIndex degreeOneOne = indexOne
productIndex degreeOneTwo = indexTwo
productIndex degreeTwoOne = indexTwo

rootMultiplicity : SampleRootBidegree → Nat
rootMultiplicity degree = jCoefficient (productIndex degree)

realSimpleRootMultiplicityExact :
  rootMultiplicity degreeOneMinusOne ≡ 1
realSimpleRootMultiplicityExact = refl

zeroProductMultiplicityExact :
  rootMultiplicity degreeOneZero ≡ 0
zeroProductMultiplicityExact = refl

oneOneRootMultiplicityExact :
  rootMultiplicity degreeOneOne ≡ 196884
oneOneRootMultiplicityExact = Modular.jCoefficientOneExact

oneTwoRootMultiplicityExact :
  rootMultiplicity degreeOneTwo ≡ 21493760
oneTwoRootMultiplicityExact = Modular.jCoefficientTwoExact

twoOneRootMultiplicityExact :
  rootMultiplicity degreeTwoOne ≡ 21493760
twoOneRootMultiplicityExact = Modular.jCoefficientTwoExact

sameProductGivesSameSampleMultiplicity :
  rootMultiplicity degreeOneTwo ≡ rootMultiplicity degreeTwoOne
sameProductGivesSameSampleMultiplicity = refl

data StringLieConstructionStage : Set where
  moonshineChiralStateSpace : StringLieConstructionStage
  lorentzianLatticeTensor : StringLieConstructionStage
  physicalStateBRSTQuotient : StringLieConstructionStage
  generalizedKacMoodyBracket : StringLieConstructionStage
  denominatorIdentity : StringLieConstructionStage

nextStage : StringLieConstructionStage → StringLieConstructionStage
nextStage moonshineChiralStateSpace = lorentzianLatticeTensor
nextStage lorentzianLatticeTensor = physicalStateBRSTQuotient
nextStage physicalStateBRSTQuotient = generalizedKacMoodyBracket
nextStage generalizedKacMoodyBracket = denominatorIdentity
nextStage denominatorIdentity = denominatorIdentity

record MonsterLieStringAuthorityBoundary : Set where
  constructor monsterLieStringAuthorityBoundary
  field
    finiteMultiplicityPrefixConstructsBRSTCohomology : Set
    finiteMultiplicityPrefixDoesNotConstructBRSTCohomology :
      finiteMultiplicityPrefixConstructsBRSTCohomology → Set

    rootMultiplicityPrefixProvesDenominatorIdentity : Set
    rootMultiplicityPrefixDoesNotProveDenominatorIdentity :
      rootMultiplicityPrefixProvesDenominatorIdentity → Set

canonicalMonsterLieStringAuthorityBoundary : MonsterLieStringAuthorityBoundary
canonicalMonsterLieStringAuthorityBoundary =
  monsterLieStringAuthorityBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Empty using (⊥)
