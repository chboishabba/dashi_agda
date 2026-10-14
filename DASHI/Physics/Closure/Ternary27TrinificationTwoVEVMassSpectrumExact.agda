module DASHI.Physics.Closure.Ternary27TrinificationTwoVEVMassSpectrumExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.Ternary27TrinificationTwoNeutralVEVBreakingExact as Breaking

------------------------------------------------------------------------
-- CONDITIONAL GAUGE-MASS SPECTRUM FOR THE TWO-NEUTRAL-VEV BREAKING PATTERN
--
-- Same two neutral lepton-block directions E32 and E33 as the previous owner.
-- For standard Hermitian generators T_a=lambda_a/2 and the explicit comparison
-- normalization g_L=g_R=v_32=v_33=1, the positive semidefinite quadratic form
--
--   sum_i || T_L <Phi_i> - <Phi_i> T_R ||^2
--
-- on su(3)_L + su(3)_R has rank 12.  Its four-dimensional kernel is exactly
-- su(2)_L plus the already-owned hypercharge generator.  The nonzero spectrum
-- has multiplicities
--
--   (1/4)^4, (1/2)^7, (5/6)^1.
--
-- These are dimensionless comparison eigenvalues under the declared equal-unit
-- normalization, not measured W/Z/exotic masses.  General physical masses still
-- require g_L, g_R, both VEV magnitudes, scalar normalization and running/mixing.
------------------------------------------------------------------------

leftRightGeneratorCount : Nat
leftRightGeneratorCount = 16

singleNeutralVEVStabilizerDimension : Nat
singleNeutralVEVStabilizerDimension = 7

twoNeutralVEVStabilizerDimension : Nat
twoNeutralVEVStabilizerDimension = 4

twoNeutralVEVMassRank : Nat
twoNeutralVEVMassRank = 12

quarterMultiplicity : Nat
quarterMultiplicity = 4

halfMultiplicity : Nat
halfMultiplicity = 7

fiveSixthsMultiplicity : Nat
fiveSixthsMultiplicity = 1

comparisonNormalization : String
comparisonNormalization = "T_a=lambda_a/2; g_L=g_R=v_32=v_33=1"

unbrokenKernel : String
unbrokenKernel = "su(2)_L plus Y"

record TwoVEVMassSpectrumLocalReceipt : Set where
  constructor two-vev-mass-spectrum-local-receipt
  field
    sameTwoNeutralVEVDirectionsUsed : Bool
    standardGellMannHalfNormalizationUsed : Bool
    singleVEVLeavesDimensionSeven : Bool
    twoVEVsLeaveDimensionFour : Bool
    twoVEVMassRankTwelve : Bool
    survivingSU2LGeneratorsChecked : Bool
    survivingHyperchargeGeneratorChecked : Bool
    colorSectorUntouched : Bool
    quarterMultiplicityFourChecked : Bool
    halfMultiplicitySevenChecked : Bool
    fiveSixthsMultiplicityOneChecked : Bool
    physicalGaugeCouplingsDerived : Bool
    physicalVEVScaleDerived : Bool
    observedMassesPredicted : Bool
    scalarPotentialDerived : Bool
    boundary : String
open TwoVEVMassSpectrumLocalReceipt public

canonicalTwoVEVMassSpectrumLocalReceipt : TwoVEVMassSpectrumLocalReceipt
canonicalTwoVEVMassSpectrumLocalReceipt =
  two-vev-mass-spectrum-local-receipt
    true true true true true true true true true true true
    false false false false
    "The two-neutral-27 breaking pattern gives a rank-12 positive gauge-mass quadratic form and leaves exactly su(2)_L plus the same hypercharge direction in the L/R sector, with color untouched. Under equal unit couplings/VEVs its dimensionless positive spectrum is (1/4)^4,(1/2)^7,(5/6)^1. This is a conditional representation-theoretic spectrum, not a physical mass prediction without a scalar potential, VEV scale and gauge couplings."

breakingReceipt : Breaking.TwoNeutralVEVBreakingLocalReceipt
breakingReceipt = Breaking.canonicalTwoNeutralVEVBreakingLocalReceipt

data ConditionalGaugeSpectrumCreatesObservedMasses : Set where

conditionalSpectrumDoesNotCreateObservedMasses :
  ConditionalGaugeSpectrumCreatesObservedMasses → {A : Set} → A
conditionalSpectrumDoesNotCreateObservedMasses ()
