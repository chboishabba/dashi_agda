module DASHI.Moonshine.Monster3BFiniteStoneVonNeumannFrontierExact where

------------------------------------------------------------------------
-- FINITE STONE-VON NEUMANN FRONTIER FOR THE MONSTER 3B HEISENBERG FACTOR
--
-- Structural prerequisites are now theorem-bearing: the actual finite
-- Heisenberg multiplication has identity/associativity/inverses, and the
-- quotient commutator pairing is constructively nondegenerate.  The live
-- theorem leaf is therefore irreducibility of the concrete X6 Schrodinger
-- representation, followed by fixed-central-character uniqueness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Moonshine.Monster3BHeisenbergMultiplicityExact as Multiplicity
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as Generators
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as Central
import DASHI.Moonshine.Monster3BFiniteHeisenbergNondegeneracyExact as Nondegenerate
import DASHI.Moonshine.Monster3BFiniteHeisenbergGroupLawFrontierExact as GroupLaws
import DASHI.Moonshine.Monster3BElementaryAbelianInvariantExact as Elementary
import DASHI.Moonshine.Base369AppraisalFibreHeisenbergCarrierBidiExact as Fibre
import DASHI.Moonshine.Base369PeriodicHeisenbergFibreEquivarianceExact as Periodic

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

finiteHeisenbergGroupLawsAvailable : Bool
finiteHeisenbergGroupLawsAvailable =
  GroupLaws.finiteHeisenbergGroupLawsComplete
    GroupLaws.canonicalHeisenbergGroupLawBoundary

finiteHeisenbergGroupLawsAvailableIsTrue :
  finiteHeisenbergGroupLawsAvailable ≡ true
finiteHeisenbergGroupLawsAvailableIsTrue = refl

constructiveGlobalNondegeneracyAvailable : Bool
constructiveGlobalNondegeneracyAvailable =
  Nondegenerate.globalSymplecticNondegeneracyProved
    Nondegenerate.canonicalHeisenbergNondegeneracyBoundary

constructiveGlobalNondegeneracyAvailableIsTrue :
  constructiveGlobalNondegeneracyAvailable ≡ true
constructiveGlobalNondegeneracyAvailableIsTrue = refl

rankTwoTranslationPlaneOrder : Nat
rankTwoTranslationPlaneOrder = Elementary.translationPlaneOrder

rankTwoRegularMultiplicity : Nat
rankTwoRegularMultiplicity = Elementary.regularCharacterMultiplicity

rankTwoRestrictionReconstructs729 :
  rankTwoRegularMultiplicity * rankTwoTranslationPlaneOrder
  ≡ schrodingerDegree
rankTwoRestrictionReconstructs729 =
  Elementary.regularCopiesTimesPlaneOrderIsSchrodinger

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
    finiteHeisenbergGroupLawsFullyProvedHere : Bool
    globalNondegenerateCommutatorPairingProvedHere : Bool
    irreducibilityOfX6SchrodingerModelProvedHere : Bool
    uniquenessForCentralCharacterProvedHere : Bool
    certifiedMonster729ConstituentIdentifiedWithX6Here : Bool
open StoneVonNeumannFrontierBoundary public

canonicalStoneVonNeumannFrontierBoundary : StoneVonNeumannFrontierBoundary
canonicalStoneVonNeumannFrontierBoundary =
  stoneVonNeumannFrontierBoundary
    true true true true true true
    true true true
    false false false

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
leafState proveFiniteHeisenbergGroupLaws = closed
leafState proveGlobalCommutatorNondegeneracy = closed
leafState proveSchrodingerIrreducible = open
leafState proveFixedCentralCharacterUniqueness = blocked
leafState identifyCertifiedMonster729Constituent = blocked

groupLawLeafClosed : leafState proveFiniteHeisenbergGroupLaws ≡ closed
groupLawLeafClosed = refl

nondegeneracyLeafClosed : leafState proveGlobalCommutatorNondegeneracy ≡ closed
nondegeneracyLeafClosed = refl

irreducibilityNowLive : leafState proveSchrodingerIrreducible ≡ open
irreducibilityNowLive = refl

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
highestImpactStructuralLeaf = proveSchrodingerIrreducible

highestImpactStructuralLeafIsOpen :
  leafState highestImpactStructuralLeaf ≡ open
highestImpactStructuralLeafIsOpen = refl
