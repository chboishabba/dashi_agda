module DASHI.Physics.Closure.NSCompactGammaInequalityExpenditureProducer where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption

------------------------------------------------------------------------
-- Route B: inequality-native compact-Gamma expenditure production.
--
-- The analytic estimates naturally produce
--
--   D Phi + C <= D + F.
--
-- Integration therefore yields
--
--   Phi(T) + integral C <= Phi(0) + integral D + integral F.
--
-- No subtraction, ordered additive completion, or artificial slack variable
-- is required.  The final expenditure estimate follows by monotonicity,
-- transitivity, and cancellation of the absorbed dissipation contribution.
------------------------------------------------------------------------

record OrderedAdditiveInequalityLaws
    (A : AbsorptionArithmetic) : Set₁ where
  field
    ≤-refl : ∀ x → _≤_ A x x
    sumNonnegative :
      ∀ {x y} →
      _≤_ A (zero A) x →
      _≤_ A (zero A) y →
      _≤_ A (zero A) (_+_ A x y)

open OrderedAdditiveInequalityLaws public

------------------------------------------------------------------------
-- Equality remains admissible as a special case of the inequality route.
------------------------------------------------------------------------

equalityImpliesInequality :
  ∀ {A : AbsorptionArithmetic}
    (L : OrderedAdditiveInequalityLaws A)
    {x y : Scalar A} →
  x ≡ y →
  _≤_ A x y
equalityImpliesInequality L {x = x} refl = ≤-refl L x

------------------------------------------------------------------------
-- Integrated absorption stated directly with an inequality.
------------------------------------------------------------------------

record InequalityCompactGammaAbsorptionInputs
    (A : AbsorptionArithmetic) : Set₁ where
  field
    initialPotential : Scalar A
    finalPotential : Scalar A
    escapeSupply : Scalar A
    replenishment : Scalar A
    thetaEscape : Scalar A
    marginEscape : Scalar A
    remainderConstant : Scalar A

    finalPotentialNonnegative :
      _≤_ A (zero A) finalPotential

    -- Inequality-native integrated potential law:
    --   final + escape <= initial + replenishment.
    integratedPotentialInequality :
      _≤_ A
        (_+_ A finalPotential escapeSupply)
        (_+_ A initialPotential replenishment)

    replenishmentAbsorbed :
      _≤_ A replenishment
        (_+_ A thetaEscape remainderConstant)

    escapeSplitsMarginAndAbsorbedPart :
      escapeSupply ≡ _+_ A marginEscape thetaEscape

open InequalityCompactGammaAbsorptionInputs public

inequalityAbsorptionBoundsEscapeMargin :
  (A : AbsorptionArithmetic) →
  (I : InequalityCompactGammaAbsorptionInputs A) →
  _≤_ A
    (marginEscape I)
    (_+_ A (initialPotential I) (remainderConstant I))
inequalityAbsorptionBoundsEscapeMargin A I =
  additionCancelRight A marginPlusTheta≤upperPlusTheta
  where
  escape≤finalPlusEscape :
    _≤_ A
      (escapeSupply I)
      (_+_ A (finalPotential I) (escapeSupply I))
  escape≤finalPlusEscape =
    subst
      (λ lhs →
        _≤_ A lhs (_+_ A (finalPotential I) (escapeSupply I)))
      (addZeroLeft A (escapeSupply I))
      (additionMonotoneRight A (finalPotentialNonnegative I))

  escape≤initialPlusReplenishment :
    _≤_ A
      (escapeSupply I)
      (_+_ A (initialPotential I) (replenishment I))
  escape≤initialPlusReplenishment =
    ≤-trans A
      escape≤finalPlusEscape
      (integratedPotentialInequality I)

  initialPlusReplenishment≤initialPlusAbsorbed :
    _≤_ A
      (_+_ A (initialPotential I) (replenishment I))
      (_+_ A
        (initialPotential I)
        (_+_ A (thetaEscape I) (remainderConstant I)))
  initialPlusReplenishment≤initialPlusAbsorbed =
    additionMonotoneLeft A (replenishmentAbsorbed I)

  escape≤initialPlusThetaPlusRemainder :
    _≤_ A
      (escapeSupply I)
      (_+_ A
        (initialPotential I)
        (_+_ A (thetaEscape I) (remainderConstant I)))
  escape≤initialPlusThetaPlusRemainder =
    ≤-trans A
      escape≤initialPlusReplenishment
      initialPlusReplenishment≤initialPlusAbsorbed

  marginPlusTheta≤initialPlusThetaPlusRemainder :
    _≤_ A
      (_+_ A (marginEscape I) (thetaEscape I))
      (_+_ A
        (initialPotential I)
        (_+_ A (thetaEscape I) (remainderConstant I)))
  marginPlusTheta≤initialPlusThetaPlusRemainder =
    subst
      (λ lhs →
        _≤_ A lhs
          (_+_ A
            (initialPotential I)
            (_+_ A (thetaEscape I) (remainderConstant I))))
      (escapeSplitsMarginAndAbsorbedPart I)
      escape≤initialPlusThetaPlusRemainder

  upperReassociation :
    _+_ A
      (initialPotential I)
      (_+_ A (thetaEscape I) (remainderConstant I))
    ≡
    _+_ A
      (_+_ A (initialPotential I) (remainderConstant I))
      (thetaEscape I)
  upperReassociation =
    Agda.Builtin.Equality.trans
      (Agda.Builtin.Equality.cong
        (λ middle → _+_ A (initialPotential I) middle)
        (addCommutative A (thetaEscape I) (remainderConstant I)))
      (sym (addAssociative A
        (initialPotential I)
        (remainderConstant I)
        (thetaEscape I)))

  marginPlusTheta≤upperPlusTheta :
    _≤_ A
      (_+_ A (marginEscape I) (thetaEscape I))
      (_+_ A
        (_+_ A (initialPotential I) (remainderConstant I))
        (thetaEscape I))
  marginPlusTheta≤upperPlusTheta =
    subst
      (λ rhs →
        _≤_ A
          (_+_ A (marginEscape I) (thetaEscape I))
          rhs)
      upperReassociation
      marginPlusTheta≤initialPlusThetaPlusRemainder

------------------------------------------------------------------------
-- Pointwise differential inequality and its selected integration package.
------------------------------------------------------------------------

record PointwiseCompactGammaInequalityExpenditure
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

    pointwisePotentialInequality :
      ∀ τ →
      _≤_ A
        (_+_ A (potentialDerivative τ) (coerciveEnvelopeRate τ))
        (_+_ A (dissipationRate τ) (forcingRate τ))

    -- The selected fundamental-theorem/integration package carries the
    -- pointwise inequality to the endpoint inequality.  The absorbed
    -- dissipation integral is retained on both sides for later cancellation.
    integratePointwiseInequality :
      (∀ τ →
        _≤_ A
          (_+_ A (potentialDerivative τ) (coerciveEnvelopeRate τ))
          (_+_ A (dissipationRate τ) (forcingRate τ))) →
      _≤_ A
        (_+_ A
          (potential finalTime)
          (_+_ A coerciveEnvelopeIntegral dissipationIntegral))
        (_+_ A
          (potential initialTime)
          (_+_ A dissipationIntegral forcingAndDataRemainder))

open PointwiseCompactGammaInequalityExpenditure public

integrated-compactGamma-potential-inequality :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (P : PointwiseCompactGammaInequalityExpenditure A Time) →
  _≤_ A
    (_+_ A
      (potential P (finalTime P))
      (_+_ A
        (coerciveEnvelopeIntegral P)
        (dissipationIntegral P)))
    (_+_ A
      (potential P (initialTime P))
      (_+_ A
        (dissipationIntegral P)
        (forcingAndDataRemainder P)))
integrated-compactGamma-potential-inequality P =
  integratePointwiseInequality P (pointwisePotentialInequality P)

------------------------------------------------------------------------
-- Endpoint nonnegativity and monotone Bernstein/BKM transport.
------------------------------------------------------------------------

record InequalityCompactGammaTransport
    {t l : Level}
    (A : AbsorptionArithmetic)
    (L : OrderedAdditiveInequalityLaws A)
    {Time : Set t}
    (P : PointwiseCompactGammaInequalityExpenditure A Time) :
    Set (lsuc (t ⊔ l)) where
  field
    potentialFinalNonnegative :
      _≤_ A (zero A) (potential P (finalTime P))

    weightedShellExpenditure : Scalar A
    vorticityExpenditure : Scalar A

    weightedShellBelowEnvelope :
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

open InequalityCompactGammaTransport public

pointwiseInequality-asAbsorptionInputs :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveInequalityLaws A)
    {Time : Set t}
    (P : PointwiseCompactGammaInequalityExpenditure A Time)
    (T : InequalityCompactGammaTransport {l = l} A L P) →
  InequalityCompactGammaAbsorptionInputs A
pointwiseInequality-asAbsorptionInputs {A = A} L P T = record
  { initialPotential = potential P (initialTime P)
  ; finalPotential = potential P (finalTime P)
  ; escapeSupply =
      _+_ A (coerciveEnvelopeIntegral P) (dissipationIntegral P)
  ; replenishment =
      _+_ A (dissipationIntegral P) (forcingAndDataRemainder P)
  ; thetaEscape = dissipationIntegral P
  ; marginEscape = coerciveEnvelopeIntegral P
  ; remainderConstant = forcingAndDataRemainder P
  ; finalPotentialNonnegative = potentialFinalNonnegative T
  ; integratedPotentialInequality =
      integrated-compactGamma-potential-inequality P
  ; replenishmentAbsorbed =
      ≤-refl L
        (_+_ A (dissipationIntegral P) (forcingAndDataRemainder P))
  ; escapeSplitsMarginAndAbsorbedPart = refl
  }

pointwise-compactGamma-finite-envelope-expenditure-inequality :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveInequalityLaws A)
    {Time : Set t}
    (P : PointwiseCompactGammaInequalityExpenditure A Time)
    (T : InequalityCompactGammaTransport {l = l} A L P) →
  _≤_ A
    (coerciveEnvelopeIntegral P)
    (_+_ A
      (potential P (initialTime P))
      (forcingAndDataRemainder P))
pointwise-compactGamma-finite-envelope-expenditure-inequality {A = A} L P T =
  inequalityAbsorptionBoundsEscapeMargin A
    (pointwiseInequality-asAbsorptionInputs L P T)

pointwise-compactGamma-finite-weighted-shell-expenditure-inequality :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveInequalityLaws A)
    {Time : Set t}
    (P : PointwiseCompactGammaInequalityExpenditure A Time)
    (T : InequalityCompactGammaTransport {l = l} A L P) →
  _≤_ A
    (weightedShellExpenditure T)
    (_+_ A
      (potential P (initialTime P))
      (forcingAndDataRemainder P))
pointwise-compactGamma-finite-weighted-shell-expenditure-inequality
    {A = A} L P T =
  ≤-trans A
    (weightedShellBelowEnvelope T)
    (pointwise-compactGamma-finite-envelope-expenditure-inequality L P T)

pointwise-compactGamma-finite-vorticity-expenditure-inequality :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveInequalityLaws A)
    {Time : Set t}
    (P : PointwiseCompactGammaInequalityExpenditure A Time)
    (T : InequalityCompactGammaTransport {l = l} A L P) →
  _≤_ A
    (vorticityExpenditure T)
    (_+_ A
      (potential P (initialTime P))
      (forcingAndDataRemainder P))
pointwise-compactGamma-finite-vorticity-expenditure-inequality
    {A = A} L P T =
  ≤-trans A
    (vorticityBelowWeightedShell T)
    (pointwise-compactGamma-finite-weighted-shell-expenditure-inequality L P T)

pointwise-compactGamma-bkm-continuation-inequality :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveInequalityLaws A)
    {Time : Set t}
    (P : PointwiseCompactGammaInequalityExpenditure A Time)
    (T : InequalityCompactGammaTransport {l = l} A L P) →
  Continuation T
pointwise-compactGamma-bkm-continuation-inequality L P T =
  invokeBKMFromVorticityBound T
    (pointwise-compactGamma-finite-vorticity-expenditure-inequality L P T)

------------------------------------------------------------------------
-- Route-selection certificate: the producer consumes inequalities directly.
------------------------------------------------------------------------

data CompactGammaBalanceRoute : Set where
  inequalityNativeRoute : CompactGammaBalanceRoute

selectedCompactGammaBalanceRoute : CompactGammaBalanceRoute
selectedCompactGammaBalanceRoute = inequalityNativeRoute
