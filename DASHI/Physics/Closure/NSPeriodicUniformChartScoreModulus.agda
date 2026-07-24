module DASHI.Physics.Closure.NSPeriodicUniformChartScoreModulus where

open import Agda.Primitive using (Level; lsuc)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Uniform score-modulus ledger.
--
-- The selected chart score combines Gamma, normalized packet fraction,
-- off-packet ratio and size.  This module proves that four cutoff-uniform
-- component derivative bounds give one cutoff/shell/trajectory-independent
-- score derivative bound, and transports that bound through the ordinary
-- fundamental theorem of calculus to a Lipschitz modulus.
------------------------------------------------------------------------

record UniformScoreDerivativeInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    gammaDerivativeMagnitude packetDerivativeMagnitude
      ratioDerivativeMagnitude sizeDerivativeMagnitude : Scalar A

    gammaDerivativeBound packetDerivativeBound
      ratioDerivativeBound sizeDerivativeBound : Scalar A

    scoreDerivativeMagnitude : Scalar A

    scoreDerivativeBelowComponents :
      _≤_ A scoreDerivativeMagnitude
        (_+_ A gammaDerivativeMagnitude
          (_+_ A packetDerivativeMagnitude
            (_+_ A ratioDerivativeMagnitude sizeDerivativeMagnitude)))

    gammaDerivativeUniform :
      _≤_ A gammaDerivativeMagnitude gammaDerivativeBound

    packetDerivativeUniform :
      _≤_ A packetDerivativeMagnitude packetDerivativeBound

    ratioDerivativeUniform :
      _≤_ A ratioDerivativeMagnitude ratioDerivativeBound

    sizeDerivativeUniform :
      _≤_ A sizeDerivativeMagnitude sizeDerivativeBound

open UniformScoreDerivativeInputs public

uniformScoreLipschitzConstant :
  ∀ {A : AbsorptionArithmetic} →
  UniformScoreDerivativeInputs A → Scalar A
uniformScoreLipschitzConstant {A = A} I =
  _+_ A (gammaDerivativeBound I)
    (_+_ A (packetDerivativeBound I)
      (_+_ A (ratioDerivativeBound I) (sizeDerivativeBound I)))

componentDerivativeSumBelowUniformConstant :
  ∀ {A : AbsorptionArithmetic} →
  (I : UniformScoreDerivativeInputs A) →
  _≤_ A
    (_+_ A (gammaDerivativeMagnitude I)
      (_+_ A (packetDerivativeMagnitude I)
        (_+_ A (ratioDerivativeMagnitude I)
          (sizeDerivativeMagnitude I))))
    (uniformScoreLipschitzConstant I)
componentDerivativeSumBelowUniformConstant {A = A} I =
  additionMonotone A
    (gammaDerivativeUniform I)
    (additionMonotone A
      (packetDerivativeUniform I)
      (additionMonotone A
        (ratioDerivativeUniform I)
        (sizeDerivativeUniform I)))
  where
  additionMonotone :
    (A : AbsorptionArithmetic) →
    ∀ {a b c d} →
    _≤_ A a b → _≤_ A c d →
    _≤_ A (_+_ A a c) (_+_ A b d)
  additionMonotone A left right =
    ≤-trans A
      (additionMonotoneRight A left)
      (additionMonotoneLeft A right)

uniformScoreDerivativeBound :
  ∀ {A : AbsorptionArithmetic} →
  (I : UniformScoreDerivativeInputs A) →
  _≤_ A
    (scoreDerivativeMagnitude I)
    (uniformScoreLipschitzConstant I)
uniformScoreDerivativeBound {A = A} I =
  ≤-trans A
    (scoreDerivativeBelowComponents I)
    (componentDerivativeSumBelowUniformConstant I)

record UniformScoreModulusInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Time Shell State : Set i) : Set (lsuc i) where
  field
    scoreDifferenceMagnitude :
      Shell → Time → Time → State → Scalar A

    timeIncrement : Time → Time → Scalar A
    scale : Scalar A → Scalar A → Scalar A

    derivativeLedger :
      Shell → Time → State → UniformScoreDerivativeInputs A

    commonLipschitzConstant : Scalar A

    derivativeLedgerUsesCommonConstant : ∀ shell τ state →
      uniformScoreLipschitzConstant (derivativeLedger shell τ state)
      ≡ commonLipschitzConstant

    integrateDerivativeBound :
      (∀ shell τ state →
        _≤_ A
          (scoreDerivativeMagnitude (derivativeLedger shell τ state))
          commonLipschitzConstant) →
      ∀ shell start finish state →
      _≤_ A
        (scoreDifferenceMagnitude shell start finish state)
        (scale commonLipschitzConstant (timeIncrement start finish))

open UniformScoreModulusInputs public

uniformDerivativeUsesCommonConstant :
  ∀ {i} {A : AbsorptionArithmetic} {Time Shell State : Set i} →
  (M : UniformScoreModulusInputs A Time Shell State) →
  ∀ shell τ state →
  _≤_ A
    (scoreDerivativeMagnitude (derivativeLedger M shell τ state))
    (commonLipschitzConstant M)
uniformDerivativeUsesCommonConstant {A = A} M shell τ state =
  subst
    (λ upper →
      _≤_ A
        (scoreDerivativeMagnitude (derivativeLedger M shell τ state))
        upper)
    (derivativeLedgerUsesCommonConstant M shell τ state)
    (uniformScoreDerivativeBound (derivativeLedger M shell τ state))

uniformScoreModulus :
  ∀ {i} {A : AbsorptionArithmetic} {Time Shell State : Set i} →
  (M : UniformScoreModulusInputs A Time Shell State) →
  ∀ shell start finish state →
  _≤_ A
    (scoreDifferenceMagnitude M shell start finish state)
    (scale M
      (commonLipschitzConstant M)
      (timeIncrement M start finish))
uniformScoreModulus M =
  integrateDerivativeBound M (uniformDerivativeUsesCommonConstant M)

------------------------------------------------------------------------
-- Status: the universal score-modulus problem is reduced to four explicit
-- component derivative bounds and one standard FTC integration instance.  The
-- existing hysteresis-separation/dwell modules consume the resulting modulus.
------------------------------------------------------------------------

uniformChartScoreModulusLevel : ProofLevel
uniformChartScoreModulusLevel = machineChecked
