{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTNegativeActiveStressRepulsionRouteExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (zero; suc)
open import Data.Rational.Base using (ℚ; +_; -[1+_]; _+_)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Foundations.GRQFTRationalStressComponentCutExact as Cut
import DASHI.Physics.Foundations.CMP119SymmetricStressComponentReductionExact as Sym

------------------------------------------------------------------------
-- NEGATIVE ACTIVE-STRESS ROUTE
--
-- In a local orthonormal rest-frame diagonal interpretation, the combination
--
--     rho + p_x + p_y + p_z
--
-- is the stress-side quantity that appears in the standard GR focusing /
-- acceleration diagnostics (rho + 3p in the isotropic case).
--
-- This file does NOT silently assert that every RationalTensor4 uses that
-- physical convention.  The convention is explicit and the algebraic result is
-- then exact.
------------------------------------------------------------------------

data DiagonalStressInterpretationConvention : Set where
  localOrthonormalCovariantRestFrame :
    DiagonalStressInterpretationConvention

activeStressSum :
  Cut.RationalTensor4 → ℚ
activeStressSum tensor =
  tensor Flat.timeAxis Flat.timeAxis
  + tensor Flat.xAxis Flat.xAxis
  + tensor Flat.yAxis Flat.yAxis
  + tensor Flat.zAxis Flat.zAxis

finiteGRActiveStressSum :
  ℚ
finiteGRActiveStressSum =
  activeStressSum Cut.finiteGRStressRational

finiteGRActiveStressSumIsNegativeTwo :
  finiteGRActiveStressSum ≡ -[1+ suc zero ]
finiteGRActiveStressSumIsNegativeTwo = refl

------------------------------------------------------------------------
-- The normalized GR target is therefore not merely "positive energy density".
-- Its three principal spatial diagonal entries are equal negative tensions.
------------------------------------------------------------------------

record NormalizedTensionDominatedGRDiagnostic : Set where
  constructor normalized-tension-dominated-gr-diagnostic
  field
    convention : DiagonalStressInterpretationConvention

    energyDensity :
      Cut.finiteGRStressRational Flat.timeAxis Flat.timeAxis ≡ + 1

    xPressure :
      Cut.finiteGRStressRational Flat.xAxis Flat.xAxis ≡ -[1+ zero ]

    yPressure :
      Cut.finiteGRStressRational Flat.yAxis Flat.yAxis ≡ -[1+ zero ]

    zPressure :
      Cut.finiteGRStressRational Flat.zAxis Flat.zAxis ≡ -[1+ zero ]

    activeStress :
      activeStressSum Cut.finiteGRStressRational ≡ -[1+ suc zero ]

open NormalizedTensionDominatedGRDiagnostic public

canonicalNormalizedTensionDominatedGRDiagnostic :
  NormalizedTensionDominatedGRDiagnostic
canonicalNormalizedTensionDominatedGRDiagnostic =
  normalized-tension-dominated-gr-diagnostic
    localOrthonormalCovariantRestFrame
    Cut.finiteGR00
    Cut.finiteGR11
    Cut.finiteGR22
    Cut.finiteGR33
    finiteGRActiveStressSumIsNegativeTwo

------------------------------------------------------------------------
-- CMP119 TRANSPORT
--
-- Once the ten symmetric CMP119 component equations are paid, the QFT tensor
-- has the same four diagonal components.  The negative active-stress
-- diagnostic therefore requires no additional GRQFT tensor theorem.
------------------------------------------------------------------------

cmp119ActiveStressSum :
  ∀ {StressTensor : Set} →
  (evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor) →
  StressTensor →
  ℚ
cmp119ActiveStressSum evaluator stress =
  Cut.component evaluator stress Flat.timeAxis Flat.timeAxis
  + Cut.component evaluator stress Flat.xAxis Flat.xAxis
  + Cut.component evaluator stress Flat.yAxis Flat.yAxis
  + Cut.component evaluator stress Flat.zAxis Flat.zAxis

tenComponentsCompileToNegativeActiveStress :
  ∀ {StressTensor : Set}
    {evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor}
    {stress : StressTensor} →
  Sym.NormalizedSymmetricTenComponentInstance evaluator stress →
  cmp119ActiveStressSum evaluator stress ≡ -[1+ suc zero ]
tenComponentsCompileToNegativeActiveStress instance
  rewrite Sym.qft00 instance
        | Sym.qft11 instance
        | Sym.qft22 instance
        | Sym.qft33 instance
  = refl

record CMP119NegativeActiveStressDiagnostic
    {StressTensor : Set}
    (evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor)
    (stress : StressTensor) : Set where
  constructor cmp119-negative-active-stress-diagnostic
  field
    convention : DiagonalStressInterpretationConvention
    tenComponentInstance :
      Sym.NormalizedSymmetricTenComponentInstance evaluator stress
    activeStressNegativeTwo :
      cmp119ActiveStressSum evaluator stress ≡ -[1+ suc zero ]

open CMP119NegativeActiveStressDiagnostic public

cmp119NegativeActiveStressDiagnostic :
  ∀ {StressTensor : Set}
    {evaluator : Cut.CMP119RationalStressComponentEvaluator StressTensor}
    {stress : StressTensor} →
  Sym.NormalizedSymmetricTenComponentInstance evaluator stress →
  CMP119NegativeActiveStressDiagnostic evaluator stress
cmp119NegativeActiveStressDiagnostic instance =
  cmp119-negative-active-stress-diagnostic
    localOrthonormalCovariantRestFrame
    instance
    (tenComponentsCompileToNegativeActiveStress instance)

------------------------------------------------------------------------
-- MECHANISM INTERPRETATION
--
-- Algebraically this identifies a source-side route:
--
--   positive T00 + sufficiently negative principal stresses/tensions
--        -> negative active stress sum.
--
-- It is distinct from both negative inertial mass and a sign reversal of G.
-- Turning negative active stress into a solved local repulsive geometry still
-- requires the ordinary GR dynamical hypotheses: Einstein equation, selected
-- geometry/initial data, and the relevant focusing/geodesic statement.
------------------------------------------------------------------------

data GRQFTRepulsionMechanismCandidate : Set where
  negativePressureTensionActiveSource :
    GRQFTRepulsionMechanismCandidate

normalizedGRTargetSelectsNegativePressureTensionCandidate :
  GRQFTRepulsionMechanismCandidate
normalizedGRTargetSelectsNegativePressureTensionCandidate =
  negativePressureTensionActiveSource

record NegativeActiveStressPromotionBoundary : Set where
  constructor negative-active-stress-promotion-boundary
  field
    normalizedGRTargetHasNegativeActiveStressUnderDeclaredConvention : Bool
    cmp119TenComponentPaymentTransportsNegativeActiveStress : Bool
    negativeActiveStressEqualsNegativeInertialMass : Bool
    negativeActiveStressRequiresNegativeNewtonG : Bool
    algebraicNegativeActiveStressAloneSolvesRepulsiveGeometry : Bool
    einsteinDynamicsAndGeometryStillRequired : Bool

canonicalNegativeActiveStressPromotionBoundary :
  NegativeActiveStressPromotionBoundary
canonicalNegativeActiveStressPromotionBoundary =
  negative-active-stress-promotion-boundary
    true true false false false true
