module DASHI.Geometry.LorentzianLeviCivitaConditional where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.AdmissibilityJetSpec as Spec
import DASHI.Physics.Closure.ValuationVacuumEinsteinBoundary as Vacuum

------------------------------------------------------------------------
-- Conditional Lorentzian / Levi-Civita closure.
--
-- This module does not derive a smooth metric from a valuation carrier.
-- It makes the exact witness chain explicit:
--
--   valuation interface
--   + smooth four-dimensional base
--   + nondegenerate metric with one timelike and three spacelike directions
--   + torsion-free metric-compatible connection
--   + uniqueness
--   ---------------------------------------------------------------
--   Lorentzian metric and Levi-Civita receipts.
--
-- The theorem content is logical composition of supplied witnesses.  The
-- geometric existence and uniqueness proofs remain obligations of producers.

record LorentzianMetricWitness : Set where
  constructor mkLorentzianMetricWitness
  field
    witnessLabel : String
    valuationBoundary : Vacuum.ValuationInducedMetricBoundary
    admissibilitySpec : Spec.DepthAdmissibilitySpec
    smoothBaseSupplied : Bool
    dimension : Nat
    metricSupplied : Bool
    metricNondegenerate : Bool
    oneTimelikeDirection : Bool
    threeSpacelikeDirections : Bool
    valuationSelectsMetric : Bool
    witnessStatement : String

open LorentzianMetricWitness public

record LorentzianMetricReceipt (w : LorentzianMetricWitness) : Set where
  constructor mkLorentzianMetricReceipt
  field
    dimensionIsFour : dimension w ≡ suc (suc (suc (suc zero)))
    smoothBaseWitness : smoothBaseSupplied w ≡ true
    metricWitness : metricSupplied w ≡ true
    nondegeneracyWitness : metricNondegenerate w ≡ true
    timelikeWitness : oneTimelikeDirection w ≡ true
    spacelikeWitness : threeSpacelikeDirections w ≡ true

open LorentzianMetricReceipt public

record ConnectionWitness (w : LorentzianMetricWitness) : Set where
  constructor mkConnectionWitness
  field
    connectionLabel : String
    connectionSupplied : Bool
    torsionFree : Bool
    metricCompatible : Bool
    uniquenessAmongTorsionFreeMetricCompatibleConnections : Bool
    connectionStatement : String

open ConnectionWitness public

record LeviCivitaReceipt
  (w : LorentzianMetricWitness)
  (metricReceipt : LorentzianMetricReceipt w)
  (connection : ConnectionWitness w) : Set where
  constructor mkLeviCivitaReceipt
  field
    connectionExists : connectionSupplied connection ≡ true
    torsionFreeWitness : torsionFree connection ≡ true
    metricCompatibilityWitness : metricCompatible connection ≡ true
    uniquenessWitness :
      uniquenessAmongTorsionFreeMetricCompatibleConnections connection ≡ true

open LeviCivitaReceipt public

assembleLeviCivitaReceipt :
  (w : LorentzianMetricWitness) →
  (metricReceipt : LorentzianMetricReceipt w) →
  (connection : ConnectionWitness w) →
  connectionSupplied connection ≡ true →
  torsionFree connection ≡ true →
  metricCompatible connection ≡ true →
  uniquenessAmongTorsionFreeMetricCompatibleConnections connection ≡ true →
  LeviCivitaReceipt w metricReceipt connection
assembleLeviCivitaReceipt w metricReceipt connection exists torsion metric unique =
  mkLeviCivitaReceipt exists torsion metric unique

canonicalConditionalLorentzianWitness : LorentzianMetricWitness
canonicalConditionalLorentzianWitness =
  mkLorentzianMetricWitness
    "conditional-lorentzian-witness"
    Vacuum.canonicalValuationMetricBoundary
    Spec.metricDiffeomorphismTwoJetSpec
    true
    (suc (suc (suc (suc zero))))
    true
    true
    true
    true
    false
    "Lorentzian structure is supplied as a conditional witness; valuation-to-metric selection is not derived"

canonicalConditionalLorentzianReceipt :
  LorentzianMetricReceipt canonicalConditionalLorentzianWitness
canonicalConditionalLorentzianReceipt =
  mkLorentzianMetricReceipt refl refl refl refl refl refl

canonicalConditionalConnection :
  ConnectionWitness canonicalConditionalLorentzianWitness
canonicalConditionalConnection =
  mkConnectionWitness
    "conditional-levi-civita-connection"
    true
    true
    true
    true
    "torsion freedom, metric compatibility, and uniqueness are explicit supplied hypotheses"

canonicalConditionalLeviCivitaReceipt :
  LeviCivitaReceipt
    canonicalConditionalLorentzianWitness
    canonicalConditionalLorentzianReceipt
    canonicalConditionalConnection
canonicalConditionalLeviCivitaReceipt =
  assembleLeviCivitaReceipt
    canonicalConditionalLorentzianWitness
    canonicalConditionalLorentzianReceipt
    canonicalConditionalConnection
    refl refl refl refl

canonicalValuationDoesNotSelectMetric :
  valuationSelectsMetric canonicalConditionalLorentzianWitness ≡ false
canonicalValuationDoesNotSelectMetric = refl
