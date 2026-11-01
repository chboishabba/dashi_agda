module DASHI.Physics.YangMills.BalabanFiniteNeumannParametrix where

------------------------------------------------------------------------
-- Exact algebra behind the random-walk/Neumann construction.
--
-- If a local approximate inverse G* satisfies
--
--   A (G* x) = x - R x,
--
-- then the recursively localized finite sum
--
--   G* x + G* R x + ... + G* R^(n-1) x
--
-- has residual exactly R^n x.  This theorem is purely finite and algebraic:
-- no completeness, operator norm, or convergence premise is hidden here.
-- The analytic frontier is therefore isolated to proving that R^n tends to zero
-- in the required weighted norm.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (Level; lsuc)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

record AdditiveParametrixData {a : Level} (Carrier : Set a) : Set (lsuc a) where
  field
    additiveZero : Carrier
    add subtract : Carrier → Carrier → Carrier

    operator local residual : Carrier → Carrier

    operatorZero : operator additiveZero ≡ additiveZero
    operatorAdd : ∀ left right →
      operator (add left right) ≡ add (operator left) (operator right)

    localResidualEquation : ∀ value →
      operator (local value) ≡ subtract value (residual value)

    subtractSelf : ∀ value → subtract value value ≡ additiveZero
    subtractZeroRight : ∀ value → subtract value additiveZero ≡ value
    telescopeAdd : ∀ left middle right →
      add (subtract left middle) (subtract middle right)
        ≡ subtract left right

open AdditiveParametrixData public

residualPower :
  ∀ {a} {Carrier : Set a} →
  AdditiveParametrixData Carrier → Nat → Carrier → Carrier
residualPower bundle zero value = value
residualPower bundle (suc depth) value =
  residualPower bundle depth (residual bundle value)

finiteNeumannApproximation :
  ∀ {a} {Carrier : Set a} →
  AdditiveParametrixData Carrier → Nat → Carrier → Carrier
finiteNeumannApproximation bundle zero value = additiveZero bundle
finiteNeumannApproximation bundle (suc depth) value =
  add bundle
    (local bundle value)
    (finiteNeumannApproximation bundle depth (residual bundle value))

finiteRightNeumannTelescope :
  ∀ {a} {Carrier : Set a}
  (bundle : AdditiveParametrixData Carrier) →
  ∀ depth value →
  operator bundle (finiteNeumannApproximation bundle depth value)
    ≡ subtract bundle value (residualPower bundle depth value)
finiteRightNeumannTelescope bundle zero value =
  trans
    (operatorZero bundle)
    (sym (subtractSelf bundle value))
finiteRightNeumannTelescope bundle (suc depth) value =
  trans
    (operatorAdd bundle
      (local bundle value)
      (finiteNeumannApproximation bundle depth (residual bundle value)))
    (trans
      (cong₂ (add bundle)
        (localResidualEquation bundle value)
        (finiteRightNeumannTelescope bundle depth (residual bundle value)))
      (telescopeAdd bundle
        value
        (residual bundle value)
        (residualPower bundle depth (residual bundle value))))

finiteRightNeumannExactAtDepth :
  ∀ {a} {Carrier : Set a}
  (bundle : AdditiveParametrixData Carrier) →
  ∀ depth value →
  residualPower bundle depth value ≡ additiveZero bundle →
  operator bundle (finiteNeumannApproximation bundle depth value) ≡ value
finiteRightNeumannExactAtDepth bundle depth value residualVanishes =
  trans
    (finiteRightNeumannTelescope bundle depth value)
    (trans
      (cong (subtract bundle value) residualVanishes)
      (subtractZeroRight bundle value))
