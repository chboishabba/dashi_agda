module DASHI.Physics.YangMills.BalabanCommon196608AtlasExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine", Bulletin of the London Mathematical Society 11
-- (1979), 308--339.
-- DOI: 10.1112/blms/11.3.308.
--
-- John H. Conway and Neil J. A. Sloane,
-- "Sphere Packings, Lattices and Groups", third edition, Springer.
-- DOI: 10.1007/978-1-4757-6568-7.
--
-- DASHI CONTRIBUTION
--
-- Package three exact but typed presentations of 196608:
--
--   Yang--Mills: 24 * 8192,
--   Monster phase: 3 * 65536,
--   Leech weight-two coordinates: 196560 + 24 + 24.
--
-- The atlas also records 196884 = 196608 + 276.  Distinct chart constructors
-- prevent equality of the integer from being mistaken for an intertwiner,
-- representation isomorphism or dynamical identification.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

data Common196608Chart : Set where
  yangMillsWilsonRadiusChart : Common196608Chart
  monsterPhaseChart : Common196608Chart
  leechWeightTwoCoordinateChart : Common196608Chart

chartValue : Common196608Chart → Nat
chartValue yangMillsWilsonRadiusChart = 24 * 8192
chartValue monsterPhaseChart = 3 * 65536
chartValue leechWeightTwoCoordinateChart = 196560 + 24 + 24

common196608 : Nat
common196608 = 196608

moonshineWeightTwo : Nat
moonshineWeightTwo = 196884

griessResidualDimension : Nat
griessResidualDimension = 276

yangMillsChartIs196608 :
  chartValue yangMillsWilsonRadiusChart ≡ common196608
yangMillsChartIs196608 = refl

phaseChartIs196608 :
  chartValue monsterPhaseChart ≡ common196608
phaseChartIs196608 = refl

leechChartIs196608 :
  chartValue leechWeightTwoCoordinateChart ≡ common196608
leechChartIs196608 = refl

moonshineWeightTwoCompletion :
  common196608 + griessResidualDimension ≡ moonshineWeightTwo
moonshineWeightTwoCompletion = refl

record Common196608Atlas : Set where
  constructor common196608Atlas
  field
    yangMillsChart :
      chartValue yangMillsWilsonRadiusChart ≡ common196608
    phaseChart :
      chartValue monsterPhaseChart ≡ common196608
    leechChart :
      chartValue leechWeightTwoCoordinateChart ≡ common196608
    moonshineCompletion :
      common196608 + griessResidualDimension ≡ moonshineWeightTwo

open Common196608Atlas public

canonicalCommon196608Atlas : Common196608Atlas
canonicalCommon196608Atlas =
  common196608Atlas
    yangMillsChartIs196608
    phaseChartIs196608
    leechChartIs196608
    moonshineWeightTwoCompletion

record Common196608IntertwinerBoundary : Set where
  constructor common196608IntertwinerBoundary
  field
    wilsonToPhaseCoordinateMapConstructed : Bool
    phaseToLeechCoordinateMapConstructed : Bool
    relevantOperatorIntertwined : Bool
    physicalDefectTransported : Bool

canonicalCommon196608IntertwinerBoundary :
  Common196608IntertwinerBoundary
canonicalCommon196608IntertwinerBoundary =
  common196608IntertwinerBoundary false false false false

common196608AtlasLevel : ProofLevel
common196608AtlasLevel = machineChecked

common196608IntertwinerLevel : ProofLevel
common196608IntertwinerLevel = conditional
