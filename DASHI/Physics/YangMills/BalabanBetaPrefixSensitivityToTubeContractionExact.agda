module DASHI.Physics.YangMills.BalabanBetaPrefixSensitivityToTubeContractionExact where

------------------------------------------------------------------------
-- A: CUMULATIVE BETA SENSITIVITY -> RENORMALISATION-MAP CONTRACTION
--
-- The source shooting map has the form
--
--       T_K(u) = u_R + B_K(u),
--
-- where B_K(u) is the cumulative history-dependent beta correction generated
-- by the trajectory starting from u.  Therefore the constant target u_R drops
-- out of differences exactly.  A q-Lipschitz estimate for B_K, q < 1, is the
-- exact contraction estimate required by the beta-tube fixed-point route.
--
-- This file proves that algebraic implication.  The new physical analytic
-- task is consequently sharp: prove the cumulative beta sensitivity bound on
-- the literal Wilson/reduced-FP/Haar trajectory.  No marginal coupling is
-- assigned an artificial exponential-forgetting law.
--
-- PRIMARY SOURCE
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; _+ℝ_
  ; _-ℝ_
  ; _*ℝ_
  ; _≤ℝ_
  ; absℝ
  ; subAddDistributes
  ; subSelf
  ; +-identityˡ
  ; cong
  ; trans
  )
open import DASHI.Physics.YangMills.CompactLieProofLevel

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

record BetaPrefixShootingMap (TubePoint : Set) : Set₁ where
  field
    initialInverseSquare : TubePoint → ℝ
    renormalisationMap : TubePoint → TubePoint
    renormalisedInverseSquare : ℝ
    cumulativeBeta : TubePoint → ℝ

    mapHasSourceFormula : ∀ u →
      initialInverseSquare (renormalisationMap u)
        ≡ renormalisedInverseSquare +ℝ cumulativeBeta u

open BetaPrefixShootingMap public

sourceMapDifferenceIsBetaDifference :
  ∀ {TubePoint}
    (dataSet : BetaPrefixShootingMap TubePoint)
    (u v : TubePoint) →
  initialInverseSquare dataSet (renormalisationMap dataSet u)
    -ℝ initialInverseSquare dataSet (renormalisationMap dataSet v)
  ≡ cumulativeBeta dataSet u -ℝ cumulativeBeta dataSet v
sourceMapDifferenceIsBetaDifference dataSet u v =
  let
    target = renormalisedInverseSquare dataSet
    betaU = cumulativeBeta dataSet u
    betaV = cumulativeBeta dataSet v

    replaceLeft = cong
      (λ x → x -ℝ initialInverseSquare dataSet (renormalisationMap dataSet v))
      (mapHasSourceFormula dataSet u)

    replaceRight = cong
      (λ y → (target +ℝ betaU) -ℝ y)
      (mapHasSourceFormula dataSet v)

    split = subAddDistributes target betaU target betaV
    cancelTarget = cong
      (λ x → x +ℝ (betaU -ℝ betaV))
      (subSelf target)
    removeZero = +-identityˡ (betaU -ℝ betaV)
  in
    trans replaceLeft
      (trans replaceRight
        (trans split
          (trans cancelTarget removeZero)))

sourceMapAbsoluteDifferenceIsBetaDifference :
  ∀ {TubePoint}
    (dataSet : BetaPrefixShootingMap TubePoint)
    (u v : TubePoint) →
  absℝ
    (initialInverseSquare dataSet (renormalisationMap dataSet u)
      -ℝ initialInverseSquare dataSet (renormalisationMap dataSet v))
  ≡
  absℝ (cumulativeBeta dataSet u -ℝ cumulativeBeta dataSet v)
sourceMapAbsoluteDifferenceIsBetaDifference dataSet u v =
  cong absℝ (sourceMapDifferenceIsBetaDifference dataSet u v)

-- The exact bridge consumed by the tube construction.  No Banach theorem is
-- hidden here: this proves only the contraction inequality; fixed-point
-- existence remains the standard complete-metric consequence once the literal
-- tube is shown closed/complete in the chosen coordinate.
prefixSensitivityImpliesShootingContraction :
  ∀ {TubePoint}
    (dataSet : BetaPrefixShootingMap TubePoint)
    (q : ℝ) →
  (prefixSensitivity : ∀ u v →
    absℝ (cumulativeBeta dataSet u -ℝ cumulativeBeta dataSet v)
      ≤ℝ
    q *ℝ
      absℝ
        (initialInverseSquare dataSet u
          -ℝ initialInverseSquare dataSet v)) →
  ∀ u v →
  absℝ
    (initialInverseSquare dataSet (renormalisationMap dataSet u)
      -ℝ initialInverseSquare dataSet (renormalisationMap dataSet v))
    ≤ℝ
  q *ℝ
    absℝ
      (initialInverseSquare dataSet u
        -ℝ initialInverseSquare dataSet v)
prefixSensitivityImpliesShootingContraction dataSet q prefixSensitivity u v =
  replaceLeft
    (sourceMapAbsoluteDifferenceIsBetaDifference dataSet u v)
    (prefixSensitivity u v)
  where
    replaceLeft : ∀ {a b c : ℝ} → a ≡ b → b ≤ℝ c → a ≤ℝ c
    replaceLeft refl b≤c = b≤c

betaPrefixSensitivityToTubeContractionLevel : ProofLevel
betaPrefixSensitivityToTubeContractionLevel = machineChecked

-- Literal physical seam: prove q < 1 for the cumulative history-dependent beta
-- law on the admissible source tube.  Irrelevant-memory decay can contribute
-- to this estimate, but cannot replace the current marginal sensitivity.
literalCumulativeBetaSensitivityStrictContractionLevel : ProofLevel
literalCumulativeBetaSensitivityStrictContractionLevel = conditional
