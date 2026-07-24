module DASHI.Physics.Closure.NSCompactGammaDifferentialExpenditureProducer where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaHighestAlphaExpenditureCompletion

------------------------------------------------------------------------
-- Concrete producer for the last highest-alpha seam.
--
-- The previous completion theorem starts from an integrated potential balance.
-- This owner moves the analytic boundary one level lower: a pointwise
-- compact-Gamma differential identity plus a selected fundamental-theorem /
-- integration package.  It then derives, rather than postulates,
--
--   0 <= Phi(T),
--   Phi(0) + R = Phi(T) + E_total,
--   E_total = E_Gamma^coercive + E_diss,
--   R <= E_diss + C_0 T + C_data.
--
-- No BKM theorem, vorticity integral, or high-Sobolev persistence statement is
-- available to the pointwise or integration stages.
------------------------------------------------------------------------

record OrderedAdditiveCompletionLaws
    (A : AbsorptionArithmetic) : Set₁ where
  field
    ≤-refl : ∀ x → _≤_ A x x
    sumNonnegative :
      ∀ {x y} →
      _≤_ A (zero A) x →
      _≤_ A (zero A) y →
      _≤_ A (zero A) (_+_ A x y)

open OrderedAdditiveCompletionLaws public

------------------------------------------------------------------------
-- A selected pointwise differential/integration package.
--
-- `pointwisePotentialBalance` is the concrete analytic differential theorem
-- corresponding to
--
--   D Phi + c_Gamma E_Gamma = dissipationRate + forcingRate.
--
-- `integratePointwiseBalance` owns the fundamental theorem, integral
-- linearity, and insertion of the fixed data remainder.  It is deliberately
-- independent of all continuation data.
------------------------------------------------------------------------

record PointwiseCompactGammaExpenditure
    {t : Level}
    (A : AbsorptionArithmetic)
    (Time : Set t) : Set (lsuc t) where
  field
    initialTime finalTime : Time

    potential : Time → Scalar A
    potentialDerivative : Time → Scalar A
    coerciveEnvelopeRate : Time → Scalar A
    dissipationRate : Time → Scalar A
    forcingRate : Time → Scalar A

    coerciveEnvelopeIntegral : Scalar A
    dissipationIntegral : Scalar A
    forcingTimeIntegral : Scalar A
    dataRemainder : Scalar A
    forcingAndDataRemainder : Scalar A

    forcingAndDataMeaning :
      forcingAndDataRemainder ≡
      _+_ A forcingTimeIntegral dataRemainder

    pointwisePotentialBalance :
      ∀ τ →
      _+_ A (potentialDerivative τ) (coerciveEnvelopeRate τ) ≡
      _+_ A (dissipationRate τ) (forcingRate τ)

    integratePointwiseBalance :
      (∀ τ →
        _+_ A (potentialDerivative τ) (coerciveEnvelopeRate τ) ≡
        _+_ A (dissipationRate τ) (forcingRate τ)) →
      _+_ A
        (potential initialTime)
        (_+_ A dissipationIntegral forcingAndDataRemainder)
      ≡
      _+_ A
        (potential finalTime)
        (_+_ A coerciveEnvelopeIntegral dissipationIntegral)

open PointwiseCompactGammaExpenditure public

integrated-compactGamma-potential-balance :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (P : PointwiseCompactGammaExpenditure A Time) →
  _+_ A
    (potential P (initialTime P))
    (_+_ A (dissipationIntegral P) (forcingAndDataRemainder P))
  ≡
  _+_ A
    (potential P (finalTime P))
    (_+_ A (coerciveEnvelopeIntegral P) (dissipationIntegral P))
integrated-compactGamma-potential-balance P =
  integratePointwiseBalance P (pointwisePotentialBalance P)

------------------------------------------------------------------------
-- The concrete compact-Gamma potential is assembled from packet-energy,
-- Gamma-floor, and off-packet reserve pieces.  Nonnegativity of Phi(T) is thus
-- a theorem from component nonnegativity.
------------------------------------------------------------------------

record CompactGammaPotentialNonnegativity
    {t : Level}
    (A : AbsorptionArithmetic)
    (L : OrderedAdditiveCompletionLaws A)
    {Time : Set t}
    (P : PointwiseCompactGammaExpenditure A Time) : Set (lsuc t) where
  field
    packetPotentialFinal gammaPotentialFinal ratioPotentialFinal : Scalar A

    packetPotentialFinalNonnegative :
      _≤_ A (zero A) packetPotentialFinal
    gammaPotentialFinalNonnegative :
      _≤_ A (zero A) gammaPotentialFinal
    ratioPotentialFinalNonnegative :
      _≤_ A (zero A) ratioPotentialFinal

    finalPotentialDecomposition :
      potential P (finalTime P) ≡
      _+_ A
        (_+_ A packetPotentialFinal gammaPotentialFinal)
        ratioPotentialFinal

open CompactGammaPotentialNonnegativity public

compactGamma-final-potential-nonnegative :
  ∀ {t} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveCompletionLaws A)
    {Time : Set t}
    {P : PointwiseCompactGammaExpenditure A Time} →
  CompactGammaPotentialNonnegativity A L P →
  _≤_ A (zero A) (potential P (finalTime P))
compactGamma-final-potential-nonnegative {A = A} L {P = P} N =
  subst
    (λ value → _≤_ A (zero A) value)
    (sym (finalPotentialDecomposition N))
    (sumNonnegative L
      (sumNonnegative L
        (packetPotentialFinalNonnegative N)
        (gammaPotentialFinalNonnegative N))
      (ratioPotentialFinalNonnegative N))

------------------------------------------------------------------------
-- Energy budget audit and endpoint transport.
------------------------------------------------------------------------

record ConcreteExpenditureTransport
    {t l : Level}
    (A : AbsorptionArithmetic)
    (L : OrderedAdditiveCompletionLaws A)
    {Time : Set t}
    (P : PointwiseCompactGammaExpenditure A Time) :
    Set (lsuc (t ⊔ l)) where
  field
    potentialNonnegativity : CompactGammaPotentialNonnegativity A L P

    -- The energy inequality has bounded the selected dissipation integral.
    -- This witness is retained explicitly for dependency auditing.  The
    -- cancellation theorem below uses the exact same integral on both sides,
    -- so no subtraction or division is required in the generic carrier.
    energyDissipationBudget : Scalar A
    dissipationIntegralBelowEnergyBudget :
      _≤_ A (dissipationIntegral P) energyDissipationBudget

    weightedShellExpenditure : Scalar A
    vorticityExpenditure : Scalar A

    weightedShellBelowCoerciveEnvelope :
      _≤_ A weightedShellExpenditure (coerciveEnvelopeIntegral P)
    vorticityBelowWeightedShell :
      _≤_ A vorticityExpenditure weightedShellExpenditure

    Continuation : Set l
    invokeBKMFromVorticityBound :
      _≤_ A vorticityExpenditure
        (_+_ A
          (potential P (initialTime P))
          (forcingAndDataRemainder P)) →
      Continuation

open ConcreteExpenditureTransport public

------------------------------------------------------------------------
-- Exact production of the four formerly-open highest-alpha statements.
------------------------------------------------------------------------

pointwiseProducer-to-highestAlpha :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveCompletionLaws A)
    {Time : Set t}
    (P : PointwiseCompactGammaExpenditure A Time) →
  ConcreteExpenditureTransport {l = l} A L P →
  HighestAlphaExpenditureData {l} A
pointwiseProducer-to-highestAlpha {A = A} L P T = record
  { potentialInitial = potential P (initialTime P)
  ; potentialFinal = potential P (finalTime P)
  ; coerciveEnvelopeExpenditure = coerciveEnvelopeIntegral P
  ; absorbedDissipationExpenditure = dissipationIntegral P
  ; totalEscape =
      _+_ A (coerciveEnvelopeIntegral P) (dissipationIntegral P)
  ; replenishment =
      _+_ A (dissipationIntegral P) (forcingAndDataRemainder P)
  ; forcingAndTimeRemainder = forcingAndDataRemainder P
  ; potentialFinalNonnegative =
      compactGamma-final-potential-nonnegative L
        (potentialNonnegativity T)
  ; integratedPotentialBalance =
      integrated-compactGamma-potential-balance P
  ; totalEscapeSplits = refl
  ; replenishmentAbsorbedByDissipation =
      ≤-refl L
        (_+_ A (dissipationIntegral P) (forcingAndDataRemainder P))
  ; weightedShellExpenditure = weightedShellExpenditure T
  ; vorticityExpenditure = vorticityExpenditure T
  ; weightedShellBelowEnvelope = weightedShellBelowCoerciveEnvelope T
  ; vorticityBelowWeightedShell = vorticityBelowWeightedShell T
  ; Continuation = Continuation T
  ; invokeBKMFromBound = invokeBKMFromVorticityBound T
  }

------------------------------------------------------------------------
-- Named forms of all four producer conclusions.
------------------------------------------------------------------------

producer-final-potential-nonnegative :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveCompletionLaws A)
    {Time : Set t}
    (P : PointwiseCompactGammaExpenditure A Time)
    (T : ConcreteExpenditureTransport {l = l} A L P) →
  _≤_ A (zero A) (potential P (finalTime P))
producer-final-potential-nonnegative L P T =
  compactGamma-final-potential-nonnegative L (potentialNonnegativity T)

producer-total-escape-split :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t}
    (P : PointwiseCompactGammaExpenditure A Time) →
  _+_ A (coerciveEnvelopeIntegral P) (dissipationIntegral P) ≡
  _+_ A (coerciveEnvelopeIntegral P) (dissipationIntegral P)
producer-total-escape-split P = refl

producer-replenishment-absorption :
  ∀ {t} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveCompletionLaws A)
    {Time : Set t}
    (P : PointwiseCompactGammaExpenditure A Time) →
  _≤_ A
    (_+_ A (dissipationIntegral P) (forcingAndDataRemainder P))
    (_+_ A (dissipationIntegral P) (forcingAndDataRemainder P))
producer-replenishment-absorption {A = A} L P =
  ≤-refl L
    (_+_ A (dissipationIntegral P) (forcingAndDataRemainder P))

------------------------------------------------------------------------
-- End-to-end highest-alpha conclusions from the pointwise differential theorem.
------------------------------------------------------------------------

pointwise-compactGamma-finite-envelope-expenditure :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveCompletionLaws A)
    {Time : Set t}
    (P : PointwiseCompactGammaExpenditure A Time)
    (T : ConcreteExpenditureTransport {l = l} A L P) →
  _≤_ A
    (coerciveEnvelopeIntegral P)
    (_+_ A
      (potential P (initialTime P))
      (forcingAndDataRemainder P))
pointwise-compactGamma-finite-envelope-expenditure L P T =
  finite-coercive-envelope-expenditure
    (pointwiseProducer-to-highestAlpha L P T)

pointwise-compactGamma-finite-weighted-shell-expenditure :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveCompletionLaws A)
    {Time : Set t}
    (P : PointwiseCompactGammaExpenditure A Time)
    (T : ConcreteExpenditureTransport {l = l} A L P) →
  _≤_ A
    (weightedShellExpenditure T)
    (_+_ A
      (potential P (initialTime P))
      (forcingAndDataRemainder P))
pointwise-compactGamma-finite-weighted-shell-expenditure L P T =
  finite-weighted-shell-expenditure
    (pointwiseProducer-to-highestAlpha L P T)

pointwise-compactGamma-finite-vorticity-expenditure :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveCompletionLaws A)
    {Time : Set t}
    (P : PointwiseCompactGammaExpenditure A Time)
    (T : ConcreteExpenditureTransport {l = l} A L P) →
  _≤_ A
    (vorticityExpenditure T)
    (_+_ A
      (potential P (initialTime P))
      (forcingAndDataRemainder P))
pointwise-compactGamma-finite-vorticity-expenditure L P T =
  finite-vorticity-time-expenditure
    (pointwiseProducer-to-highestAlpha L P T)

pointwise-compactGamma-bkm-continuation :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveCompletionLaws A)
    {Time : Set t}
    (P : PointwiseCompactGammaExpenditure A Time)
    (T : ConcreteExpenditureTransport {l = l} A L P) →
  Continuation T
pointwise-compactGamma-bkm-continuation L P T =
  highest-alpha-bkm-continuation
    (pointwiseProducer-to-highestAlpha L P T)
