module DASHI.Physics.Closure.UnifiedEnergyFunctionalSurface where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_<_)
open import Relation.Binary.PropositionalEquality using (subst)

import Contraction as Contract
import JFixedPoint as J
import UFTC_Lattice as UFTC
import Ultrametric as UMetric

import DASHI.Physics.ShiftPotentialQuadraticEnergy as ShiftEnergy

------------------------------------------------------------------------
-- Unified energy-functional surface.
--
-- This module records the already-present Lyapunov skeleton without
-- promoting any open P0 lane.  It links:
--
-- * UFTC severity propagation as max-energy;
-- * strict contraction as distance-to-fixed-point energy descent;
-- * shift quadratic energy as a concrete finite descent instance;
-- * J fixed point normalization as the invariant scalar.

CodeEnergy : UFTC.Code → Nat
CodeEnergy = UFTC.severity

codeCombineMaxLaw :
  ∀ x y →
  CodeEnergy (UFTC.C_XOR x y)
    ≡
  (CodeEnergy x UFTC.⊔s CodeEnergy y)
codeCombineMaxLaw x y = refl

strictContractionDistanceDescent :
  ∀ {S : Set}
    {U : UMetric.Ultrametric S}
    {K : S → S}
    (sc : Contract.StrictContraction U K)
    (x : S) →
  x Contract.≢ Contract.StrictContraction.fp sc →
  UMetric.Ultrametric.d U (K x) (Contract.StrictContraction.fp sc)
    <
  UMetric.Ultrametric.d U x (Contract.StrictContraction.fp sc)
strictContractionDistanceDescent {U = U} {K = K} sc x x≢fp =
  let
    open Contract.StrictContraction sc
    open Contract.Contractive≢ contractive≢
  in
  subst
    (λ y →
      UMetric.Ultrametric.d U (K x) y
        <
      UMetric.Ultrametric.d U x fp)
    fixed
    (contraction≢ x≢fp)

jFixedDepthInvariant :
  ∀ n →
  J.contract (J.stack n) ≡ 196884
jFixedDepthInvariant zero = refl
jFixedDepthInvariant (suc n) = refl

record UnifiedEnergyFunctionalSurface : Setω where
  field
    codeCarrier :
      Set

    codeEnergy :
      codeCarrier → Nat

    codeCombine :
      codeCarrier → codeCarrier → codeCarrier

    codeCombineMax :
      ∀ x y →
      codeEnergy (codeCombine x y)
        ≡
      (codeEnergy x UFTC.⊔s codeEnergy y)

    strictContractionDescent :
      ∀ {S : Set}
        {U : UMetric.Ultrametric S}
        {K : S → S}
        (sc : Contract.StrictContraction U K)
        (x : S) →
      x Contract.≢ Contract.StrictContraction.fp sc →
      UMetric.Ultrametric.d U (K x) (Contract.StrictContraction.fp sc)
        <
      UMetric.Ultrametric.d U x (Contract.StrictContraction.fp sc)

    shiftQuadraticEnergy :
      ShiftEnergy.ShiftPotentialQuadraticEnergy

    jScalar :
      Nat

    jUnitNormalizes :
      J.contract J.unit-obs ≡ jScalar

    jDepthNormalizes :
      ∀ n →
      J.contract (J.stack n) ≡ jScalar

    nonPromotionBoundary :
      List String

unifiedEnergyFunctionalSurface :
  UnifiedEnergyFunctionalSurface
unifiedEnergyFunctionalSurface =
  record
    { codeCarrier =
        UFTC.Code
    ; codeEnergy =
        CodeEnergy
    ; codeCombine =
        UFTC.C_XOR
    ; codeCombineMax =
        codeCombineMaxLaw
    ; strictContractionDescent =
        strictContractionDistanceDescent
    ; shiftQuadraticEnergy =
        ShiftEnergy.shiftPotentialQuadraticEnergy
    ; jScalar =
        196884
    ; jUnitNormalizes =
        J.unit-converges
    ; jDepthNormalizes =
        jFixedDepthInvariant
    ; nonPromotionBoundary =
        "This surface identifies the shared energy-functional skeleton already present in the repo"
        ∷ "It does not merge the carriers for W1, W3, W4, W5, W6, W8, or W9"
        ∷ "It does not construct external empirical authority, physical calibration, runtime PNF receipts, origin promotion, or pressure witnesses"
        ∷ "It may be consumed as a coordination interface for future Lyapunov-style unification work"
        ∷ []
    }
