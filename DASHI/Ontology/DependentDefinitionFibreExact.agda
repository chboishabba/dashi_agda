module DASHI.Ontology.DependentDefinitionFibreExact where

------------------------------------------------------------------------
-- DEPENDENT-DEFINITION / POSITIVE-BUNDLE BOUNDARY
--
-- A flat positive-description carrier forms a Cartesian product first and asks
-- a Boolean validator afterwards whether the combination is coherent.  A
-- dependent/fibred carrier instead makes the legal next choices depend on the
-- already-selected parent coordinate, so invalid combinations are absent from
-- the type itself.
--
-- The finite vehicle example is intentionally ordinary: Make restricts Model,
-- and Model can be read back to its compatible Make.  It is an exact toy model
-- for the ontology issue where independently positive descriptors admit
-- divergent transcriptions while a pullback/dependent construction propagates
-- compatibility locally.
--
-- This module also reuses Base369SignedMembershipExact to retain a context
-- bundle while its local signed coordinate is neutral/non-determinant.  Thus
-- local zero does not imply global semantic absence.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

import Base369 as Base
import DASHI.Foundations.Base369SignedMembershipExact as Signed

data Make : Set where
  ford toyota : Make

data FlatModel : Set where
  fiestaTag focusTag corollaTag : FlatModel

FlatVehicle : Set
FlatVehicle = Make × FlatModel

validFlat : FlatVehicle → Bool
validFlat (ford , fiestaTag) = true
validFlat (ford , focusTag) = true
validFlat (ford , corollaTag) = false
validFlat (toyota , fiestaTag) = false
validFlat (toyota , focusTag) = false
validFlat (toyota , corollaTag) = true

flatToyotaFiestaExists : FlatVehicle
flatToyotaFiestaExists = toyota , fiestaTag

flatToyotaFiestaNeedsPostHocRejection : validFlat flatToyotaFiestaExists ≡ false
flatToyotaFiestaNeedsPostHocRejection = refl

-- The flat product constructs all 2 x 3 combinations before validity is known.
flatCombinationCount : Nat
flatCombinationCount = 2 * 3

flatCombinationCountIsSix : flatCombinationCount ≡ 6
flatCombinationCountIsSix = refl

data FordModel : Set where
  fiesta focus : FordModel

data ToyotaModel : Set where
  corolla : ToyotaModel

Model : Make → Set
Model ford = FordModel
Model toyota = ToyotaModel

Vehicle : Set
Vehicle = Σ Make Model

fordFiesta : Vehicle
fordFiesta = ford , fiesta

fordFocus : Vehicle
fordFocus = ford , focus

toyotaCorolla : Vehicle
toyotaCorolla = toyota , corolla

-- The dependent sum has exactly 2 Ford models + 1 Toyota model.
dependentCombinationCount : Nat
dependentCombinationCount = 2 + 1

dependentCombinationCountIsThree : dependentCombinationCount ≡ 3
dependentCombinationCountIsThree = refl

invalidFlatCombinationCount : Nat
invalidFlatCombinationCount = 3

flatCountSplitsAsValidPlusInvalid :
  flatCombinationCount ≡ dependentCombinationCount + invalidFlatCombinationCount
flatCountSplitsAsValidPlusInvalid = refl

modelTag : ∀ {make} → Model make → FlatModel
modelTag {ford} fiesta = fiestaTag
modelTag {ford} focus = focusTag
modelTag {toyota} corolla = corollaTag

flattenVehicle : Vehicle → FlatVehicle
flattenVehicle (make , model) = make , modelTag model

dependentCarrierOnlyFlattensToValidCombinations :
  (vehicle : Vehicle) → validFlat (flattenVehicle vehicle) ≡ true
dependentCarrierOnlyFlattensToValidCombinations (ford , fiesta) = refl
dependentCarrierOnlyFlattensToValidCombinations (ford , focus) = refl
dependentCarrierOnlyFlattensToValidCombinations (toyota , corolla) = refl

noToyotaFiestaSection :
  (vehicle : Vehicle) →
  proj₁ vehicle ≡ toyota →
  modelTag (proj₂ vehicle) ≡ fiestaTag →
  ⊥
noToyotaFiestaSection (ford , fiesta) () modelEq
noToyotaFiestaSection (ford , focus) () modelEq
noToyotaFiestaSection (toyota , corolla) makeEq ()

record ContextualBundle : Set where
  constructor contextualBundle
  field
    retainedInContext : Bool
    localOrientation : Signed.FibredOrientation

open ContextualBundle public

relevantButNonDeterminant : ContextualBundle
relevantButNonDeterminant =
  contextualBundle true (Signed.fibredOrientation Base.tri-mid Signed.zeroOpen)

relevantBundleIsRetained : retainedInContext relevantButNonDeterminant ≡ true
relevantBundleIsRetained = refl

relevantBundleIsLocallyNeutral :
  Signed.sign (localOrientation relevantButNonDeterminant) ≡ Base.tri-mid
relevantBundleIsLocallyNeutral = refl

localNeutralityDoesNotMeanContextErasure :
  retainedInContext relevantButNonDeterminant ≡ false → ⊥
localNeutralityDoesNotMeanContextErasure ()

record DependentDefinitionFibreBoundary : Set where
  constructor dependentDefinitionFibreBoundary
  field
    flatProductsCanContainInvalidCombinations : Bool
    flatAndDependentCombinationCountsCoincide : Bool
    dependentCarrierRequiresPostHocValidityForItsOwnValues : Bool
    parentChoiceRestrictsChildFibre : Bool
    localNeutralityErasesRetainedContext : Bool
    BooleanFailureIdentifiesWhichDependencyFailed : Bool

canonicalDependentDefinitionFibreBoundary : DependentDefinitionFibreBoundary
canonicalDependentDefinitionFibreBoundary =
  dependentDefinitionFibreBoundary true false false true false false
