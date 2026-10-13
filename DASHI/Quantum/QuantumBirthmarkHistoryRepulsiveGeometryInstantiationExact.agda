{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHistoryRepulsiveGeometryInstantiationExact where

open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Stress
import DASHI.Physics.Foundations.GRQFTDECRepulsiveExteriorMaxCutExact as DEC
import DASHI.Physics.Foundations.GRQFTTwoVacuumAmplitudePotentialExact as DECPotential
import DASHI.Physics.Foundations.GRQFTNambuGotoRepulsiveBubbleMaxCutExact as Nambu

------------------------------------------------------------------------
-- CONCRETE REPULSIVE-GEOMETRY INSTANTIATIONS
--
-- The repo already contains exact double-well potentials for both the DEC
-- repulsive exterior and Nambu-Goto bubble geometries.  Therefore the remaining
-- history-sector task is not to invent a two-vacuum scalar model; it is to
-- derive/map the microscopic residual-history dynamics into the relevant order
-- parameter and normalized CMP119 stress carrier.
------------------------------------------------------------------------

historyDECRepulsiveExterior :
  ∀ {StressTensor : Set}
    {evaluator : Stress.CMP119RationalStressComponentEvaluator StressTensor}
    {cmp119Stress : StressTensor}
    {normalized :
      Stress.NormalizedCrossSectorStressInstance
        StressTensor evaluator cmp119Stress} →
  DEC.DECRepulsiveExteriorMaxCut
    evaluator cmp119Stress normalized DECPotential.twoVacuumAmplitudeModelReceipt
historyDECRepulsiveExterior =
  DEC.decRepulsiveExteriorMaxCut DECPotential.twoVacuumAmplitudeModelReceipt

historyNambuGotoRepulsiveBubble :
  ∀ {StressTensor : Set}
    {evaluator : Stress.CMP119RationalStressComponentEvaluator StressTensor}
    {cmp119Stress : StressTensor} →
  (normalized :
    Stress.NormalizedCrossSectorStressInstance
      StressTensor evaluator cmp119Stress) →
  Nambu.NambuGotoRepulsiveBubbleCandidate evaluator cmp119Stress normalized
historyNambuGotoRepulsiveBubble =
  Nambu.nambuGotoRepulsiveBubbleCandidate

twoVacuumDECAmplitudeModelAlreadyConstructed : Bool
twoVacuumDECAmplitudeModelAlreadyConstructed = true

nambuGotoTwoVacuumPotentialAlreadyConstructed : Bool
nambuGotoTwoVacuumPotentialAlreadyConstructed = true

repulsiveGeometryCompilerAlreadyConstructed : Bool
repulsiveGeometryCompilerAlreadyConstructed = true

microscopicHistoryToOrderParameterMapStillRequired : Bool
microscopicHistoryToOrderParameterMapStillRequired = true

sourceNativeCMP119PotentialCouplingStillRequired : Bool
sourceNativeCMP119PotentialCouplingStillRequired = true

newScalarPotentialByHandStillRequired : Bool
newScalarPotentialByHandStillRequired = false
