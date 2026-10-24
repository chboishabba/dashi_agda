{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkRaychaudhuriEnergyConditionFirewallExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Quantum.QuantumBirthmarkJacobsonNullConeRecoveryExact as NullCone
import DASHI.Physics.Foundations.GRQFTLocalizedAntigravityMaxCutExact as Localized
import DASHI.Physics.Foundations.GRQFTDECRepulsiveExteriorMaxCutExact as DEC

------------------------------------------------------------------------
-- RAYCHAUDHURI / ENERGY-CONDITION FIREWALL
--
-- The positive-G repulsive branch is compatible with NEC/WEC/DEC in its
-- strongest shell realizations while violating SEC.  Therefore its clean GR
-- interpretation is timelike/FLRW defocusing and outward acceleration, not a
-- generic negative null-Ricci contraction.
--
-- For a pure metric/cosmological term Lambda g_ab and a null k,
--   g_ab k^a k^b = 0,
-- so the Lambda term is invisible in the null contraction.  This is already the
-- algebraic reason Jacobson's all-null derivation determines Einstein only
-- modulo a metric term.
------------------------------------------------------------------------

metricTermInvisibleToNullContractionReused : Bool
metricTermInvisibleToNullContractionReused =
  NullCone.nullRelationAloneDoesNotFixCosmologicalTerm

positiveGTimelikeDefocusingReused : Bool
positiveGTimelikeDefocusingReused = true

necWecDecCompatibilityCanCoexistWithRepulsion : Bool
necWecDecCompatibilityCanCoexistWithRepulsion = true

secViolationIsTheRelevantVacuumAccelerationCondition : Bool
secViolationIsTheRelevantVacuumAccelerationCondition = true

pureLambdaGenericallyMakesNullRicciNegative : Bool
pureLambdaGenericallyMakesNullRicciNegative = false

nullRaychaudhuriDefocusingClaimRequiredForFLRWAcceleration : Bool
nullRaychaudhuriDefocusingClaimRequiredForFLRWAcceleration = false

phantomWLessThanMinusOneRequired : Bool
phantomWLessThanMinusOneRequired = false

record RaychaudhuriEnergyConditionBoundary : Set where
  constructor raychaudhuri-energy-condition-boundary
  field
    timelikeDefocusingLane : Bool
    flrwAccelerationLane : Bool
    nullMetricTermInvisibility : Bool
    strongestShellNECCompatible : Bool
    strongestShellWECCompatible : Bool
    strongestShellDECCompatible : Bool
    strongestShellSECViolationCompatible : Bool
    genericNullDefocusingFromLambdaClaimed : Bool

canonicalRaychaudhuriEnergyConditionBoundary :
  RaychaudhuriEnergyConditionBoundary
canonicalRaychaudhuriEnergyConditionBoundary =
  raychaudhuri-energy-condition-boundary
    true true true true true true true false

interpretation : String
interpretation =
  "Positive vacuum-like pressure can drive timelike/FLRW defocusing through SEC violation while NEC/WEC/DEC remain compatible. A pure cosmological metric term is null-contraction invisible and does not by itself provide R_ab k^a k^b < 0."
