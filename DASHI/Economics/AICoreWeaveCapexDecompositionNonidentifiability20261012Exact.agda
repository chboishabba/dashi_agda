module DASHI.Economics.AICoreWeaveCapexDecompositionNonidentifiability20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.ExperimentalCoordinateDesignExact as Experimental
import DASHI.Economics.AICoreWeaveCapitalReinvestmentCoverage20261012Exact as Reinvestment

------------------------------------------------------------------------
-- COREWEAVE CAPEX-DECOMPOSITION NON-IDENTIFIABILITY
--
-- The source-paid H1-2026 aggregate capex point is USD 14.117B.  Aggregate
-- capex alone cannot identify how much is growth, maintenance or replacement
-- capex.  This owner makes that obstruction constructive and reuses the repo's
-- ExperimentalCoordinateDesignExact machinery to state what extra observation
-- would actually separate the collision.
------------------------------------------------------------------------

aggregateCapexCollisionPaid : Bool
aggregateCapexCollisionPaid = true

maintenanceReplacementStillRequiresExternalCoordinate : Bool
maintenanceReplacementStillRequiresExternalCoordinate = true

record CapexDecomposition : Set where
  constructor capex-decomposition
  field
    growthCapexMillionUSD : Nat
    maintenanceCapexMillionUSD : Nat
    replacementCapexMillionUSD : Nat
    totalMatchesReportedCapex :
      growthCapexMillionUSD + maintenanceCapexMillionUSD + replacementCapexMillionUSD ≡ 14117

open CapexDecomposition public

-- Two valid decompositions of the same literal reported H1-2026 total.
-- They differ only in whether one USD million is classified as replacement.
allGrowthWorld : CapexDecomposition
allGrowthWorld = capex-decomposition 14117 0 0 refl

oneReplacementWorld : CapexDecomposition
oneReplacementWorld = capex-decomposition 14116 0 1 refl

aggregateCapex : CapexDecomposition → Nat
aggregateCapex d =
  growthCapexMillionUSD d + maintenanceCapexMillionUSD d + replacementCapexMillionUSD d

aggregateCapexCollision :
  aggregateCapex allGrowthWorld ≡ aggregateCapex oneReplacementWorld
aggregateCapexCollision = refl

replacementValuesDiffer :
  replacementCapexMillionUSD allGrowthWorld ≡
  replacementCapexMillionUSD oneReplacementWorld → ⊥
replacementValuesDiffer ()

-- Stronger functional non-identifiability: no function of aggregate capex alone
-- can recover replacement capex for every valid decomposition.
record AggregateReplacementRecovery (recover : Nat → Nat) : Set where
  constructor aggregate-replacement-recovery
  field
    exact :
      (d : CapexDecomposition) →
      recover (aggregateCapex d) ≡ replacementCapexMillionUSD d

open AggregateReplacementRecovery public

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

aggregateCapexDoesNotDetermineReplacement :
  (recover : Nat → Nat) → AggregateReplacementRecovery recover → ⊥
aggregateCapexDoesNotDetermineReplacement recover receipt =
  replacementValuesDiffer
    (trans
      (sym (exact receipt allGrowthWorld))
      (exact receipt oneReplacementWorld))

------------------------------------------------------------------------
-- Repository-native coordinate-refinement witness.
------------------------------------------------------------------------

data CapexCoordinate : Set where
  totalCapexCoordinate : CapexCoordinate
  growthCapexCoordinate : CapexCoordinate
  maintenanceCapexCoordinate : CapexCoordinate
  replacementCapexCoordinate : CapexCoordinate

data CapexControl : Set where
  observeOnly : CapexControl

data CapexDimension : Set where
  millionUSD : CapexDimension

capexDesign :
  Experimental.ExperimentalCoordinateDesign
    CapexDecomposition CapexControl Nat CapexDimension
capexDesign = Experimental.experimentalCoordinateDesign
  CapexCoordinate
  role
  dimension
  read
  applyControl
  coordinateReference
  dimensionReference
  calibrationReference
  controlReference
  where
  role : CapexCoordinate → Experimental.CoordinateRole
  role totalCapexCoordinate = Experimental.measuredObservable
  role growthCapexCoordinate = Experimental.measuredObservable
  role maintenanceCapexCoordinate = Experimental.measuredObservable
  role replacementCapexCoordinate = Experimental.measuredObservable

  dimension : CapexCoordinate → CapexDimension
  dimension _ = millionUSD

  read : CapexCoordinate → CapexDecomposition → Nat
  read totalCapexCoordinate d = aggregateCapex d
  read growthCapexCoordinate d = growthCapexMillionUSD d
  read maintenanceCapexCoordinate d = maintenanceCapexMillionUSD d
  read replacementCapexCoordinate d = replacementCapexMillionUSD d

  applyControl : CapexControl → CapexDecomposition → CapexDecomposition
  applyControl observeOnly d = d

  coordinateReference : CapexCoordinate → String
  coordinateReference totalCapexCoordinate = "CoreWeave H1-2026 reported aggregate capex"
  coordinateReference growthCapexCoordinate = "growth-capex classification to acquire"
  coordinateReference maintenanceCapexCoordinate = "maintenance-capex classification to acquire"
  coordinateReference replacementCapexCoordinate = "replacement/refresh-capex classification to acquire"

  dimensionReference : CapexCoordinate → String
  dimensionReference _ = "USD million on the same H1-2026 accounting horizon"

  calibrationReference : CapexCoordinate → String
  calibrationReference totalCapexCoordinate = "source-paid SEC/company period coordinate"
  calibrationReference growthCapexCoordinate = "requires filing/asset-rollforward or independently auditable classification"
  calibrationReference maintenanceCapexCoordinate = "requires filing/asset-rollforward or independently auditable classification"
  calibrationReference replacementCapexCoordinate = "requires filing/asset-retirement/refresh schedule or independently auditable classification"

  controlReference : CapexControl → String
  controlReference observeOnly = "observational accounting decomposition; no intervention claimed"

replacementCoordinateSeparatesCollision :
  Experimental.CoordinateSeparatesCollision capexDesign aggregateCapex
replacementCoordinateSeparatesCollision =
  Experimental.coordinateSeparatesCollision
    replacementCapexCoordinate
    allGrowthWorld
    oneReplacementWorld
    refl
    replacementValuesDiffer

------------------------------------------------------------------------
-- Same-object source tie and promotion boundary.
------------------------------------------------------------------------

coreWeaveReportedAggregateCapexIs14117 :
  Reinvestment.capitalExpenditureMillionUSD
    Reinvestment.coreWeaveH12026ReinvestmentCoverage ≡ 14117
coreWeaveReportedAggregateCapexIs14117 = refl

data AggregateCapexIdentifiesMaintenancePermission : Set where
data DepreciationEqualsReplacementCapexPermission : Set where

aggregateCapexDoesNotIdentifyMaintenance :
  AggregateCapexIdentifiesMaintenancePermission → ⊥
aggregateCapexDoesNotIdentifyMaintenance ()

depreciationDoesNotEqualReplacementCapexByNaming :
  DepreciationEqualsReplacementCapexPermission → ⊥
depreciationDoesNotEqualReplacementCapexByNaming ()

boundary : String
boundary =
  "The source-paid CoreWeave H1-2026 aggregate capex total is compatible with distinct valid growth/maintenance/replacement decompositions. Aggregate capex therefore cannot identify replacement capex by itself. ExperimentalCoordinateDesignExact supplies the correct repair shape: acquire a same-horizon independently sourced maintenance/replacement coordinate that separates the aggregate collision. D&A is not relabelled as replacement capex."
