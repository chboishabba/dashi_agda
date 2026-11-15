module DASHI.Physics.Gravity.KSW668AdS5FrozenNeumannSeriesReuseExact where

------------------------------------------------------------------------
-- Reuse existing DASHI/YangMills/Balaban finite and weighted Neumann
-- series algebra for ORIGINAL KSW668 frozen moving AdS5 boundary symbols.
-- A geometric-series inverse is not itself a Neumann boundary PDE.
-- The real analytic high-s rho=5/(4sqrt 2) and physical oblique
-- symbol must be supplied to the generic interface separately.
-- No full moving Green, retarded Weyl or physical acceptance asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_×_; _,_)

open import DASHI.Physics.YangMills.BalabanFiniteNeumannParametrix
  using (AdditiveParametrixData; operator; subtract;
         residualPower; finiteNeumannApproximation;
         finiteRightNeumannTelescope; finiteRightNeumannExactAtDepth;
         additiveZero)
open import DASHI.Physics.YangMills.BalabanWeightedNeumannRemainder
  using (WeightedResidualContraction; finiteNeumannResidualControl;
         norm; LessEqual; multiplyBound; boundPower)

kswFrozenBoundaryFiniteResidual :
  ∀ {a} {Carrier : Set a}
  (bundle : AdditiveParametrixData Carrier) →
  ∀ depth source →
  operator bundle (finiteNeumannApproximation bundle depth source)
    ≡ subtract bundle source (residualPower bundle depth source)
kswFrozenBoundaryFiniteResidual = finiteRightNeumannTelescope

kswFrozenBoundaryExactIfNilpotent :
  ∀ {a} {Carrier : Set a}
  (bundle : AdditiveParametrixData Carrier) →
  ∀ depth source →
  residualPower bundle depth source ≡ additiveZero bundle →
  operator bundle (finiteNeumannApproximation bundle depth source)
    ≡ source
kswFrozenBoundaryExactIfNilpotent = finiteRightNeumannExactAtDepth

kswFrozenBoundaryWeightedResidual :
  ∀ {Carrier Bound : Set}
  {bundle : AdditiveParametrixData Carrier} →
  (control : WeightedResidualContraction Carrier Bound bundle) →
  ∀ depth source →
  (operator bundle (finiteNeumannApproximation bundle depth source)
    ≡ subtract bundle source (residualPower bundle depth source))
  ×
  LessEqual control
    (norm control (residualPower bundle depth source))
    (multiplyBound control
      (boundPower control depth)
      (norm control source))
kswFrozenBoundaryWeightedResidual = finiteNeumannResidualControl
