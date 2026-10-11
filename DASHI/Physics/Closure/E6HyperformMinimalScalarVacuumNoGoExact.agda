module DASHI.Physics.Closure.E6HyperformMinimalScalarVacuumNoGoExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.E6HyperformPoissonLorentzMetricExact as Metric

------------------------------------------------------------------------
-- MINIMALLY-COUPLED SCALAR + VACUUM NO-GO AT THE EXCEPTIONAL ORIGIN
--
-- The exact continuum interpolation has phi(0)=5/27 and d phi(0)=0. Hence for
-- any scalar psi=f(phi), the minimally coupled kinetic term vanishes at the
-- origin. Any scalar potential V(psi) and any cosmological/vacuum contribution
-- are both proportional to g_mu_nu there.
--
-- Local symbolic evaluation of the independently derived metric gives
--
--   Omega(0)=32/27
--   g_00(0)=-1024/729 ; g_11(0)=+1024/729
--   G_00(0)=0          ; G_11(0)=-3/16.
--
-- Therefore G_mu_nu(0) is not proportional to g_mu_nu(0). No choice of scalar
-- normalization, scalar potential, Newton coupling, or cosmological constant
-- can make a minimally-coupled scalar-plus-vacuum stress satisfy Einstein's
-- equation at this point. More structured matter/nonminimal coupling is needed.
------------------------------------------------------------------------

record MinimalScalarVacuumOriginNoGoReceipt : Set where
  constructor minimal-scalar-vacuum-origin-no-go-receipt
  field
    exceptionalMetricFromExistingOwner : Bool
    originPhi : String
    originPhiGradientZeroChecked : Bool
    originOmega : String
    originMetric00 : String
    originMetric11 : String
    originEinstein00 : String
    originEinstein11 : String
    minimallyCoupledScalarStressAtOriginProportionalToMetric : Bool
    vacuumStressAtOriginProportionalToMetric : Bool
    combinedScalarVacuumStressAtOriginProportionalToMetric : Bool
    einsteinTensorAtOriginNotProportionalToMetric : Bool
    minimallyCoupledScalarPlusVacuumEinsteinClosureImpossible : Bool
    gaugeSpinorAnisotropicOrNonminimalMatterStillCandidate : Bool
    boundary : String
open MinimalScalarVacuumOriginNoGoReceipt public

canonicalMinimalScalarVacuumOriginNoGoReceipt : MinimalScalarVacuumOriginNoGoReceipt
canonicalMinimalScalarVacuumOriginNoGoReceipt =
  minimal-scalar-vacuum-origin-no-go-receipt
    true
    "5/27" true "32/27"
    "-1024/729" "1024/729"
    "0" "-3/16"
    true true true true true true
    "The exceptional Poisson metric cannot be sourced by a minimally coupled scalar psi=f(phi), with arbitrary scalar potential, even after adding a cosmological/vacuum term: at the stationary origin that entire matter family is proportional to g_mu_nu while the derived Einstein tensor is not. This is a local no-go for that matter family only; it points toward anisotropic gauge/spinor or nonminimal matter rather than proving the trinification matter model."

data ScalarVacuumNoGoEliminatesAllMatter : Set where

scalarVacuumNoGoDoesNotEliminateAllMatter :
  ScalarVacuumNoGoEliminatesAllMatter → {A : Set} → A
scalarVacuumNoGoDoesNotEliminateAllMatter ()
