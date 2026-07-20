module DASHI.Geometry.Admissibility369UltrametricBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec using ([]; _∷_)

import DASHI.Geometry.AdmissibilityJetSpec as Spec
import DASHI.Geometry.SSP369Ultrametric as Geo

------------------------------------------------------------------------
-- Bridge the new admissibility-depth language to the repo's existing typed
-- prefix ultrametric.  The bridge is intentionally finite and carrier-level:
-- it records that depth agreement can supply a hierarchy of observational
-- resolution.  It does not identify the 369 address metric with spacetime,
-- a physical p-adic metric, or a complete invariant classifier.


two : Nat
two = suc (suc zero)

metricTwoJetAddress : Geo.Address two
metricTwoJetAddress = Geo.digit3 ∷ Geo.digit6 ∷ []

spinorOneJetAddress : Geo.Address (suc zero)
spinorOneJetAddress = Geo.digit3 ∷ []

record AdmissibilityUltrametricRow : Set where
  constructor mkAdmissibilityUltrametricRow
  field
    admissibilitySpec : Spec.DepthAdmissibilitySpec
    addressDepth : Nat
    address : Geo.Address addressDepth
    jetOrderMatchesAddressDepth : Spec.jetOrder admissibilitySpec ≡ addressDepth
    selfAgreement : Geo.agreementDepth address address ≡ addressDepth
    selfDistanceZero : Geo.distance address address ≡ zero
    physicalMetricClaimed : Bool
    completeInvariantClaimed : Bool

open AdmissibilityUltrametricRow public

metricTwoJetUltrametricRow : AdmissibilityUltrametricRow
metricTwoJetUltrametricRow =
  mkAdmissibilityUltrametricRow
    Spec.metricDiffeomorphismTwoJetSpec
    two
    metricTwoJetAddress
    refl
    (Geo.agreementDepth-self metricTwoJetAddress)
    (Geo.distance-self-zero metricTwoJetAddress)
    false
    false

spinorOneJetUltrametricRow : AdmissibilityUltrametricRow
spinorOneJetUltrametricRow =
  mkAdmissibilityUltrametricRow
    Spec.spinorOneJetSpec
    (suc zero)
    spinorOneJetAddress
    refl
    (Geo.agreementDepth-self spinorOneJetAddress)
    (Geo.distance-self-zero spinorOneJetAddress)
    false
    false

metricRowUsesExistingUltrametricSelfDistance :
  Geo.distance metricTwoJetAddress metricTwoJetAddress ≡ zero
metricRowUsesExistingUltrametricSelfDistance =
  Geo.distance-self-zero metricTwoJetAddress

metricRowDoesNotPromotePhysicalMetric :
  physicalMetricClaimed metricTwoJetUltrametricRow ≡ false
metricRowDoesNotPromotePhysicalMetric = refl
