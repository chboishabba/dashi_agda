module DASHI.Moonshine.Monster3BFiniteStoneVonNeumannFrontierExact where

------------------------------------------------------------------------
-- FINITE STONE-VON NEUMANN FRONTIER FOR THE MONSTER 3B HEISENBERG FACTOR
--
-- The repo now owns an explicit X6 + X6* + F3 central-extension carrier,
-- the generator/Weyl commutator law, and a constructive proof that every
-- nonzero quotient vector has an explicit dual vector with nonzero pairing.
-- The remaining structural prerequisite before irreducibility is the full
-- finite Heisenberg group law (associativity/identity/inverses).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Moonshine.Monster3BHeisenbergMultiplicityExact as Multiplicity
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as Generators
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as Central
import DASHI.Moonshine.Monster3BFiniteHeisenbergNondegeneracyExact as Nondegenerate
import DASHI.Moonshine.Monster3BElementaryAbelianInvariantExact as Elementary
import DASHI.Moonshine.Base369AppraisalFibreHeisenbergCarrierBidiExact as Fibre
import DASHI.Moonshine.Base369PeriodicHeisenbergFibreEquivarianceExact as Periodic

------------------------------------------------------------------------
-- 1. Existing finite carrier facts.
------------------------------------------------------------------------

centreOrder : Nat
centreOrder = Elementary.centreOrder

lagrangianDimension : Nat
lagrangianDimension = Elementary.lLagrangianDimension

symplecticQuotientDimension : Nat
symplecticQuotientDimension = Elementary.fullSymplecticDimension

schrodingerDegree : Nat
schrodingerDegree = Elementary.schrodingerDimension

centreOrderIsThree : centreOrder ≡ 3
centreOrderIsThree = refl

lagrangianDimensionIsSix : lagrangianDimension ≡ 6
lagrangianDimensionIsSix = refl

symplecticQuotientDimensionIsTwelve : symplecticQuotientDimension ≡ 12
symplecticQuotientDimensionIsTwelve = refl

schrodingerDegreeIs729 : schrodingerDegree ≡ 729
schrodingerDegreeIs729 = refl

extraspecialOrderIsThreePowerThirteen :
  Multiplicity.extraspecialOrder ≡ 1594323
extraspecialOrderIsThreePowerThirteen = Multiplicity.extraspecialOrderIs3Power13

nonlinearDegreeMatchesSchrodinger :
  Multiplicity.nonlinearCharacterDegree Multiplicity.plusType
  ≡ schrodingerDegree
nonlinearDegreeMatchesSchrodinger = refl

base369FibreMatchesSchrodingerDegree :
  Fibre.heisenbergFibreStateCount ≡ schrodingerDegree
base369FibreMatchesSchrodingerDegree = refl

------------------------------------------------------------------------
-- 2. Weyl / central-extension / nondegeneracy surface.
------------------------------------------------------------------------

translationAxisCount : Nat
translationAxisCount = Generators.translationGeneratorCount

modulationAxisCount : Nat
modulationAxisCount = Generators.modulationGeneratorCount

axisCountsAreSix : translationAxisCount ≡ 6
axisCountsAreSix = refl

standardWeylPairCountIs36 : Generators.standardGeneratorPairCount ≡ 36
standardWeylPairCountIs36 = Generators.standardGeneratorPairCountIsThirtySix

periodicBase369ActionAvailable : Bool
periodicBase369ActionAvailable = true

periodicBase369ActionAvailableIsTrue : periodicBase369ActionAvailable ≡ true
periodicBase369ActionAvailableIsTrue = refl

centralExtensionCarrierAvailable : Bool
centralExtensionCarrierAvailable =
  Central.twelveDimensionalQuotientCarrierConstructed
    Central.canonicalHeisenbergCentralExtensionBoundary

centralExtensionCarrierAvailableIsTrue : centralExtensionCarrierAvailable ≡ true
centralExtensionCarrierAvailableIsTrue = refl

commutatorPairingConstructed : Bool
commutatorPairingConstructed =
  Central.alternatingCommutatorPairingConstructed
    Central.canonicalHeisenbergCentralExtensionBoundary

commutatorPairingConstructedIsTrue : commutatorPairingConstructed ≡ true
commutatorPairingConstructedIsTrue = refl

constructiveGlobalNondegeneracyAvailable : Bool
constructiveGlobalNondegeneracyAvailable =
  Nondegenerate.globalSymplecticNondegeneracyProved
    Nondegenerate.canonicalHeisenbergNondegeneracyBoundary

constructiveGlobalNondegeneracyAvailableIsTrue :
  constructiveGlobalNondegeneracyAvailable ≡ true
constructiveGlobalNondegeneracyAvailableIsTrue = refl

------------------------------------------------------------------------
-- 3. Existing elementary-abelian restriction evidence.
------------------------------------------------------------------------

rankTwoTranslationPlaneOrder : Nat
rankTwoTranslationPlaneOrder = Elementary.translationPlaneOrder

rankTwoRegularMultiplicity : Nat
rankTwoRegularMultiplicity = Elementary.regularCharacterMultiplicity

rankTwoRestrictionReconstructs729 :
  rankTwoRegularMultiplicity * rankTwoTranslationPlaneOrder
  ≡ schrodingerDegree
rankTwoRestrictionReconstructs729 =
  Elementary.regularCopiesTimesPlaneOrderIsSchrodinger

------------------------------------------------------------------------
-- 4. Exact theorem receipts still required for final Stone-von Neumann use.
------------------------------------------------------------------------

record FiniteStoneVonNeumannReceipt : Set where
  constructor finiteStoneVonNeumannReceipt
  field
    finiteHeisenbergGroupConstructed : Bool
    centreConstructedAndHasOrderThree : Bool
    commutatorPairingConstructedReceipt : Bool
    quotientPairingNondegenerate : Bool
    nontrivialCentralCharacterConstructed : Bool
    schrodingerRepresentationConstructed : Bool
    schrodingerRepresentationIrreducible : Bool
    uniquenessForFixedNontrivialCentralCharacter : Bool
open FiniteStoneVonNeumannReceipt public

record Certified729IdentificationReceipt : Set where
  constructor certified729IdentificationReceipt
  field
    stoneVonNeumann : FiniteStoneVonNeumannReceipt
    certifiedRestrictionHasNontrivialCentralCharacter : Bool
    certifiedRestrictionDegreeIs729 : Bool
    certifiedRepresentationIsomorphicToX6Model : Bool
open Certified729IdentificationReceipt public

------------------------------------------------------------------------
-- 5. Refined BIDI boundary.
------------------------------------------------------------------------

record StoneVonNeumannFrontierBoundary : Set where
  constructor stoneVonNeumannFrontierBoundary
  field
    extraspecialDegreeArithmeticAvailable : Bool
    sixDimensionalLagrangianAvailable : Bool
    twelveDimensionalSymplecticQuotientAvailable : Bool
    concreteX6WeylGeneratorsAvailable : Bool
    elementaryRestrictionChecksAvailable : Bool
    base369PeriodicX6CarrierChartAvailable : Bool
    centralExtensionCarrierConstructedHere : Bool
    commutatorPairingConstructedHere : Bool
    globalNondegenerateCommutatorPairingProvedHere : Bool
    finiteHeisenbergGroupLawsFullyProvedHere : Bool
    irreducibilityOfX6SchrodingerModelProvedHere : Bool
    uniquenessForCentralCharacterProvedHere : Bool
    certifiedMonster729ConstituentIdentifiedWithX6Here : Bool
open StoneVonNeumannFrontierBoundary public

canonicalStoneVonNeumannFrontierBoundary : StoneVonNeumannFrontierBoundary
canonicalStoneVonNeumannFrontierBoundary =
  stoneVonNeumannFrontierBoundary
    true true true true true true
    true true true
    false false false false

------------------------------------------------------------------------
-- 6. Scientific proof-search frontier.
--
-- "blocked" remains dependency-blocked, not a claim of falsity.
------------------------------------------------------------------------

data StoneVonNeumannProofLeaf : Set where
  constructCentralExtensionCarrier : StoneVonNeumannProofLeaf
  proveFiniteHeisenbergGroupLaws : StoneVonNeumannProofLeaf
  proveGlobalCommutatorNondegeneracy : StoneVonNeumannProofLeaf
  proveSchrodingerIrreducible : StoneVonNeumannProofLeaf
  proveFixedCentralCharacterUniqueness : StoneVonNeumannProofLeaf
  identifyCertifiedMonster729Constituent : StoneVonNeumannProofLeaf

data LeafState : Set where closed open blocked : LeafState

leafState : StoneVonNeumannProofLeaf → LeafState
leafState constructCentralExtensionCarrier = closed
leafState proveFiniteHeisenbergGroupLaws = open
leafState proveGlobalCommutatorNondegeneracy = closed
leafState proveSchrodingerIrreducible = blocked
leafState proveFixedCentralCharacterUniqueness = blocked
leafState identifyCertifiedMonster729Constituent = blocked

centralExtensionLeafClosed :
  leafState constructCentralExtensionCarrier ≡ closed
centralExtensionLeafClosed = refl

nondegeneracyLeafClosed :
  leafState proveGlobalCommutatorNondegeneracy ≡ closed
nondegeneracyLeafClosed = refl

groupLawsNowSoleStructuralPrerequisite :
  leafState proveFiniteHeisenbergGroupLaws ≡ open
groupLawsNowSoleStructuralPrerequisite = refl

------------------------------------------------------------------------
-- 7. Explicit dependencies explain every remaining block.
------------------------------------------------------------------------

data Requires : StoneVonNeumannProofLeaf → StoneVonNeumannProofLeaf → Set where
  groupNeedsCarrier :
    Requires proveFiniteHeisenbergGroupLaws constructCentralExtensionCarrier
  nondegeneracyNeedsCarrier :
    Requires proveGlobalCommutatorNondegeneracy constructCentralExtensionCarrier
  irreducibleNeedsGroup :
    Requires proveSchrodingerIrreducible proveFiniteHeisenbergGroupLaws
  irreducibleNeedsNondegenerate :
    Requires proveSchrodingerIrreducible proveGlobalCommutatorNondegeneracy
  uniquenessNeedsIrreducible :
    Requires proveFixedCentralCharacterUniqueness proveSchrodingerIrreducible
  identifyNeedsUniqueness :
    Requires identifyCertifiedMonster729Constituent proveFixedCentralCharacterUniqueness

highestImpactStructuralLeaf : StoneVonNeumannProofLeaf
highestImpactStructuralLeaf = proveFiniteHeisenbergGroupLaws

highestImpactStructuralLeafIsOpen :
  leafState highestImpactStructuralLeaf ≡ open
highestImpactStructuralLeafIsOpen = refl
