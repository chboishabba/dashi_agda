module DASHI.Environment.QuantitiesConservation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat using (_+_; _≤_)

------------------------------------------------------------------------
-- Unit-tagged quantities.
--
-- Magnitudes are natural-number ticks at an explicitly declared scale.  This
-- avoids silently adding unlike quantities while leaving runtime adapters free
-- to use decimal, rational, interval, or floating-point representations.

data Unit : Set where
  audCents : Unit
  labourMinutes : Unit
  machineMinutes : Unit
  fuelMillilitres : Unit
  waterLitres : Unit
  earthworkLitres : Unit
  rainfallMicrometres : Unit
  nitrogenGrams : Unit
  phosphorusGrams : Unit
  carbonGrams : Unit
  sedimentGrams : Unit
  habitatSquareMetres : Unit
  cropGrams : Unit
  emissionGramsCO2e : Unit
  confidenceBasisPoints : Unit

record Quantity (u : Unit) : Set where
  constructor qty
  field
    magnitude : Nat
open Quantity public

_⊕_ : ∀ {u} → Quantity u → Quantity u → Quantity u
qty x ⊕ qty y = qty (x + y)

zeroQuantity : ∀ {u} → Quantity u
zeroQuantity = qty zero

quantityMonotone : ∀ {u} → Quantity u → Quantity u → Set
quantityMonotone (qty x) (qty y) = x ≤ y

------------------------------------------------------------------------
-- Typed operational and economic ledgers.

record ResourceLedger : Set where
  constructor mkResourceLedger
  field
    capitalCost : Quantity audCents
    labourUse : Quantity labourMinutes
    machineUse : Quantity machineMinutes
    fuelUse : Quantity fuelMillilitres
    waterUse : Quantity waterLitres
    earthworkVolume : Quantity earthworkLitres
    projectedRevenue : Quantity audCents
    priceScenario : String
    costProvenance : List String
open ResourceLedger public

------------------------------------------------------------------------
-- Conservation receipts.

record BalanceReceipt (u : Unit) : Set where
  constructor mkBalanceReceipt
  field
    openingStorage : Quantity u
    externalInput : Quantity u
    externalExport : Quantity u
    closingStorage : Quantity u
    accountedTransformation : Quantity u
    unaccountedResidual : Quantity u
    balanceEquation :
      openingStorage ⊕ externalInput
      ≡ externalExport ⊕ closingStorage
        ⊕ accountedTransformation ⊕ unaccountedResidual
    residualTolerance : Quantity u
    residualWithinTolerance :
      quantityMonotone unaccountedResidual residualTolerance
    modelReference : String
    evidenceReferences : List String
open BalanceReceipt public

WaterBalance : Set
WaterBalance = BalanceReceipt waterLitres

NitrogenBalance : Set
NitrogenBalance = BalanceReceipt nitrogenGrams

PhosphorusBalance : Set
PhosphorusBalance = BalanceReceipt phosphorusGrams

CarbonBalance : Set
CarbonBalance = BalanceReceipt carbonGrams

SedimentBalance : Set
SedimentBalance = BalanceReceipt sedimentGrams

------------------------------------------------------------------------
-- A scenario is conservation-admissible only through actual receipts.

record ConservationBundle : Set where
  constructor mkConservationBundle
  field
    water : WaterBalance
    nitrogen : NitrogenBalance
    phosphorus : PhosphorusBalance
    carbon : CarbonBalance
    sediment : SedimentBalance
    allRelevantStoresDeclared : Bool
    transformationsDocumented : Bool
open ConservationBundle public

record QuantityBoundary : Set where
  constructor mkQuantityBoundary
  field
    unlikeUnitsCannotBeAddedByTypedOperator : Bool
    runtimeScaleMustBeDeclared : Bool
    zeroResidualIsNotAssumed : Bool
    boundedResidualMustBeDisclosed : Bool
    economicValueIsNotEcologicalValue : Bool
    conservationReceiptIsModelRelative : Bool
open QuantityBoundary public

canonicalQuantityBoundary : QuantityBoundary
canonicalQuantityBoundary =
  mkQuantityBoundary true true true true true true

------------------------------------------------------------------------
-- Canonical exact-zero witness used by regression fixtures.

exactZeroBalance : ∀ {u} → String → BalanceReceipt u
exactZeroBalance {u} model =
  mkBalanceReceipt
    zeroQuantity
    zeroQuantity
    zeroQuantity
    zeroQuantity
    zeroQuantity
    zeroQuantity
    refl
    zeroQuantity
    (Data.Nat.z≤n)
    model
    []
