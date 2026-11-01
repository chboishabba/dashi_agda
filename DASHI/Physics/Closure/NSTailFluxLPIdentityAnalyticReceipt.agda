module DASHI.Physics.Closure.NSTailFluxLPIdentityAnalyticReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSTailFluxAbsorptionMarginReceipt as Margin
import DASHI.Physics.Closure.NSTailFluxIdentityAnalyticTargetReceipt as Target

------------------------------------------------------------------------
-- Littlewood-Paley fixed-K tail flux identity, analytic form.
--
-- This receipt sharpens the existing fixed-K analytic target by recording
-- the exact Navier-Stokes terms, weights, signs, and commutator obligation.
-- It is deliberately fail-closed: the identity is structurally locked, while
-- the Coifman-Meyer/Kato-Ponce commutator inhabitant remains an analytic
-- obligation rather than an Agda proof.

data SobolevExponent : Set where
  elevenOverEight :
    SobolevExponent

data LPTailWeight : Set where
  weightTwoToElevenJOverFour :
    LPTailWeight

data FixedKLPFormulaTerm : Set where
  tailEnergySumOverJGreaterThanK :
    FixedKLPFormulaTerm

  projectedNavierStokesEquation :
    FixedKLPFormulaTerm

  pressureKilledByLerayProjection :
    FixedKLPFormulaTerm

  viscousTermNegativeWithGradientNorm :
    FixedKLPFormulaTerm

  nonlinearProjectedFluxTerm :
    FixedKLPFormulaTerm

  thetaDefinedAfterFluxDissProfile :
    FixedKLPFormulaTerm

canonicalFixedKLPFormulaTerms :
  List FixedKLPFormulaTerm
canonicalFixedKLPFormulaTerms =
  tailEnergySumOverJGreaterThanK
  ∷ projectedNavierStokesEquation
  ∷ pressureKilledByLerayProjection
  ∷ viscousTermNegativeWithGradientNorm
  ∷ nonlinearProjectedFluxTerm
  ∷ thetaDefinedAfterFluxDissProfile
  ∷ []

data LPAnalyticAlgebraStep : Set where
  termwiseDifferentiateFixedCutoffTail :
    LPAnalyticAlgebraStep

  substituteNSIntoTimeDerivative :
    LPAnalyticAlgebraStep

  selfAdjointShellProjectorPairing :
    LPAnalyticAlgebraStep

  integrateByPartsForLaplacian :
    LPAnalyticAlgebraStep

  useDivergenceFreeToRemovePressure :
    LPAnalyticAlgebraStep

  nameDissipationAndFlux :
    LPAnalyticAlgebraStep

canonicalLPAnalyticAlgebraSteps :
  List LPAnalyticAlgebraStep
canonicalLPAnalyticAlgebraSteps =
  termwiseDifferentiateFixedCutoffTail
  ∷ substituteNSIntoTimeDerivative
  ∷ selfAdjointShellProjectorPairing
  ∷ integrateByPartsForLaplacian
  ∷ useDivergenceFreeToRemovePressure
  ∷ nameDissipationAndFlux
  ∷ []

data LPCommutatorObligation : Set where
  coifmanMeyerOrKatoPonceTailFluxBound :
    LPCommutatorObligation

  highHighRemainderControlledAtFixedK :
    LPCommutatorObligation

  noMovingCutoffBoundaryTerm :
    LPCommutatorObligation

canonicalLPCommutatorObligations :
  List LPCommutatorObligation
canonicalLPCommutatorObligations =
  coifmanMeyerOrKatoPonceTailFluxBound
  ∷ highHighRemainderControlledAtFixedK
  ∷ noMovingCutoffBoundaryTerm
  ∷ []

data LPIdentityPromotion : Set where

lpIdentityPromotionImpossibleHere :
  LPIdentityPromotion →
  ⊥
lpIdentityPromotionImpossibleHere ()

lpIdentityFormula :
  String
lpIdentityFormula =
  "For fixed K: d/dt E_{>K} = -2 nu sum_{j>K} w_j ||grad P_j u||^2 + 2 sum_{j>K} w_j <P_j (-(u.grad)u), P_j u>."

commutatorObligationFormula :
  String
commutatorObligationFormula =
  "The open analytic inhabitant is a Coifman-Meyer/Kato-Ponce fixed-K tail flux estimate; it is not supplied by this receipt."

record NSTailFluxLPIdentityAnalyticReceipt (K : Nat) : Set where
  field
    sourceTarget :
      Target.NSTailFluxIdentityAnalyticTargetReceipt K

    sourceTargetIdentityStillOpen :
      Target.lpIdentityProvedHere sourceTarget ≡ false

    marginIdentity :
      Margin.TailFluxIdentity_K K

    marginIdentityIsCanonical :
      marginIdentity ≡ Margin.canonicalTailFluxIdentity K

    sobolevExponent :
      SobolevExponent

    sobolevExponentIsElevenOverEight :
      sobolevExponent ≡ elevenOverEight

    tailWeight :
      LPTailWeight

    tailWeightIsCanonical :
      tailWeight ≡ weightTwoToElevenJOverFour

    formulaTerms :
      List FixedKLPFormulaTerm

    formulaTermsAreCanonical :
      formulaTerms ≡ canonicalFixedKLPFormulaTerms

    algebraSteps :
      List LPAnalyticAlgebraStep

    algebraStepsAreCanonical :
      algebraSteps ≡ canonicalLPAnalyticAlgebraSteps

    commutatorObligations :
      List LPCommutatorObligation

    commutatorObligationsAreCanonical :
      commutatorObligations ≡ canonicalLPCommutatorObligations

    formula :
      String

    formulaIsCanonical :
      formula ≡ lpIdentityFormula

    commutatorFormula :
      String

    commutatorFormulaIsCanonical :
      commutatorFormula ≡ commutatorObligationFormula

    lpIdentitySignsCorrect :
      Bool

    lpIdentitySignsCorrectIsTrue :
      lpIdentitySignsCorrect ≡ true

    thetaDefinitionLocked :
      Bool

    thetaDefinitionLockedIsTrue :
      thetaDefinitionLocked ≡ true

    commutatorBoundStated :
      Bool

    commutatorBoundStatedIsTrue :
      commutatorBoundStated ≡ true

    commutatorBoundProved :
      Bool

    commutatorBoundProvedIsFalse :
      commutatorBoundProved ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List LPIdentityPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      LPIdentityPromotion →
      ⊥

open NSTailFluxLPIdentityAnalyticReceipt public

canonicalNSTailFluxLPIdentityAnalyticReceipt :
  NSTailFluxLPIdentityAnalyticReceipt zero
canonicalNSTailFluxLPIdentityAnalyticReceipt =
  record
    { sourceTarget =
        Target.canonicalNSTailFluxIdentityAnalyticTargetReceipt
    ; sourceTargetIdentityStillOpen =
        refl
    ; marginIdentity =
        Margin.canonicalTailFluxIdentity zero
    ; marginIdentityIsCanonical =
        refl
    ; sobolevExponent =
        elevenOverEight
    ; sobolevExponentIsElevenOverEight =
        refl
    ; tailWeight =
        weightTwoToElevenJOverFour
    ; tailWeightIsCanonical =
        refl
    ; formulaTerms =
        canonicalFixedKLPFormulaTerms
    ; formulaTermsAreCanonical =
        refl
    ; algebraSteps =
        canonicalLPAnalyticAlgebraSteps
    ; algebraStepsAreCanonical =
        refl
    ; commutatorObligations =
        canonicalLPCommutatorObligations
    ; commutatorObligationsAreCanonical =
        refl
    ; formula =
        lpIdentityFormula
    ; formulaIsCanonical =
        refl
    ; commutatorFormula =
        commutatorObligationFormula
    ; commutatorFormulaIsCanonical =
        refl
    ; lpIdentitySignsCorrect =
        true
    ; lpIdentitySignsCorrectIsTrue =
        refl
    ; thetaDefinitionLocked =
        true
    ; thetaDefinitionLockedIsTrue =
        refl
    ; commutatorBoundStated =
        true
    ; commutatorBoundStatedIsTrue =
        refl
    ; commutatorBoundProved =
        false
    ; commutatorBoundProvedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        lpIdentityPromotionImpossibleHere
    }

canonicalLPIdentityNoClayPromotion :
  clayNavierStokesPromoted canonicalNSTailFluxLPIdentityAnalyticReceipt
  ≡ false
canonicalLPIdentityNoClayPromotion =
  refl
