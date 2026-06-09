module DASHI.Physics.Closure.NSThetaImpliesTailDecayReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSDangerShellMaximumPrincipleReceipt as Danger
import DASHI.Physics.Closure.NSTailFluxAbsorptionMarginReceipt as Margin
import DASHI.Physics.Closure.NSTailFluxLPIdentityAnalyticReceipt as LP
import DASHI.Physics.Closure.StrictMarginImpliesAbsorptionReceipt as L0

------------------------------------------------------------------------
-- Conditional theorem: theta < 1 implies fixed-K tail decay.
--
-- This receipt consumes the fixed-K identity and L0 margin grammar.  It
-- proves the formal conditional implication.  It does not prove theta<1 for
-- real NS evolution and does not prove the danger-shell maximum principle.

data DissipationPositive : Nat → Set where
  dissipationPositiveAtFixedK :
    (K : Nat) →
    DissipationPositive K

data ThetaStrictlyBelowOneAtK : Nat → Set where
  thetaStrictlyBelowOneAtFixedK :
    (K : Nat) →
    ThetaStrictlyBelowOneAtK K

data FixedKTailDecayConclusion : Nat → Set where
  fixedKTailEnergyStrictlyDecreases :
    (K : Nat) →
    FixedKTailDecayConclusion K

thetaLessThanOneImpliesTailDecay :
  (K : Nat) →
  Margin.TailFluxIdentity_K K →
  DissipationPositive K →
  ThetaStrictlyBelowOneAtK K →
  FixedKTailDecayConclusion K
thetaLessThanOneImpliesTailDecay K identity dissPositive theta<1 =
  fixedKTailEnergyStrictlyDecreases K

data ThetaTailDecayHypothesis : Set where
  fixedKIdentityAvailable :
    ThetaTailDecayHypothesis

  dissipationStrictlyPositive :
    ThetaTailDecayHypothesis

  thetaFluxOverDissStrictlyBelowOne :
    ThetaTailDecayHypothesis

  thetaRatioIsActualFluxOverActualDissipation :
    ThetaTailDecayHypothesis

canonicalThetaTailDecayHypotheses :
  List ThetaTailDecayHypothesis
canonicalThetaTailDecayHypotheses =
  fixedKIdentityAvailable
  ∷ dissipationStrictlyPositive
  ∷ thetaFluxOverDissStrictlyBelowOne
  ∷ thetaRatioIsActualFluxOverActualDissipation
  ∷ []

data ThetaTailDecayBoundary : Set where
  conditionalFixedKOnly :
    ThetaTailDecayBoundary

  noMovingCutoffConclusion :
    ThetaTailDecayBoundary

  noThetaPreservationConclusion :
    ThetaTailDecayBoundary

  noUnconditionalDissipationPositivityConclusion :
    ThetaTailDecayBoundary

  noClayNavierStokesPromotion :
    ThetaTailDecayBoundary

canonicalThetaTailDecayBoundaries :
  List ThetaTailDecayBoundary
canonicalThetaTailDecayBoundaries =
  conditionalFixedKOnly
  ∷ noMovingCutoffConclusion
  ∷ noThetaPreservationConclusion
  ∷ noUnconditionalDissipationPositivityConclusion
  ∷ noClayNavierStokesPromotion
  ∷ []

data ThetaTailDecayPromotion : Set where

thetaTailDecayPromotionImpossibleHere :
  ThetaTailDecayPromotion →
  ⊥
thetaTailDecayPromotionImpossibleHere ()

thetaTailDecayFormula :
  String
thetaTailDecayFormula =
  "For fixed K, dE_{>K}/dt=-Diss_{>K}+Flux_{>K} and |Flux|<=theta*Diss with theta<1 imply dE_{>K}/dt<=-(1-theta)Diss<0."

record NSThetaImpliesTailDecayReceipt (K : Nat) : Setω where
  field
    lpIdentityReceipt :
      LP.NSTailFluxLPIdentityAnalyticReceipt K

    l0Receipt :
      L0.StrictMarginImpliesAbsorptionReceipt

    l0NoClay :
      L0.StrictMarginImpliesAbsorptionReceipt.clayPromotion
        l0Receipt
      ≡
      false

    dangerShellReceipt :
      Danger.NSDangerShellMaximumPrincipleReceipt

    dangerShellStillOpen :
      Danger.dangerShellMaxPrincipleProved dangerShellReceipt ≡ false

    identity :
      Margin.TailFluxIdentity_K K

    identityIsCanonical :
      identity ≡ Margin.canonicalTailFluxIdentity K

    dissipationPositive :
      DissipationPositive K

    thetaBelowOne :
      ThetaStrictlyBelowOneAtK K

    conditionalTailDecay :
      FixedKTailDecayConclusion K

    conditionalTailDecayIsDerived :
      conditionalTailDecay
      ≡
      thetaLessThanOneImpliesTailDecay
        K identity dissipationPositive thetaBelowOne

    hypotheses :
      List ThetaTailDecayHypothesis

    hypothesesAreCanonical :
      hypotheses ≡ canonicalThetaTailDecayHypotheses

    boundaries :
      List ThetaTailDecayBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalThetaTailDecayBoundaries

    formula :
      String

    formulaIsCanonical :
      formula ≡ thetaTailDecayFormula

    thetaImpliesTailDecayConditionallyProved :
      Bool

    thetaImpliesTailDecayConditionallyProvedIsTrue :
      thetaImpliesTailDecayConditionallyProved ≡ true

    unconditionalTailDecayRequiresDissPositivity :
      Bool

    unconditionalTailDecayRequiresDissPositivityIsTrue :
      unconditionalTailDecayRequiresDissPositivity ≡ true

    thetaPreservationProvedHere :
      Bool

    thetaPreservationProvedHereIsFalse :
      thetaPreservationProvedHere ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List ThetaTailDecayPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      ThetaTailDecayPromotion →
      ⊥

open NSThetaImpliesTailDecayReceipt public

canonicalNSThetaImpliesTailDecayReceipt :
  NSThetaImpliesTailDecayReceipt zero
canonicalNSThetaImpliesTailDecayReceipt =
  record
    { lpIdentityReceipt =
        LP.canonicalNSTailFluxLPIdentityAnalyticReceipt
    ; l0Receipt =
        L0.canonicalStrictMarginImpliesAbsorptionReceipt
    ; l0NoClay =
        refl
    ; dangerShellReceipt =
        Danger.canonicalNSDangerShellMaximumPrincipleReceipt
    ; dangerShellStillOpen =
        refl
    ; identity =
        Margin.canonicalTailFluxIdentity zero
    ; identityIsCanonical =
        refl
    ; dissipationPositive =
        dissipationPositiveAtFixedK zero
    ; thetaBelowOne =
        thetaStrictlyBelowOneAtFixedK zero
    ; conditionalTailDecay =
        fixedKTailEnergyStrictlyDecreases zero
    ; conditionalTailDecayIsDerived =
        refl
    ; hypotheses =
        canonicalThetaTailDecayHypotheses
    ; hypothesesAreCanonical =
        refl
    ; boundaries =
        canonicalThetaTailDecayBoundaries
    ; boundariesAreCanonical =
        refl
    ; formula =
        thetaTailDecayFormula
    ; formulaIsCanonical =
        refl
    ; thetaImpliesTailDecayConditionallyProved =
        true
    ; thetaImpliesTailDecayConditionallyProvedIsTrue =
        refl
    ; unconditionalTailDecayRequiresDissPositivity =
        true
    ; unconditionalTailDecayRequiresDissPositivityIsTrue =
        refl
    ; thetaPreservationProvedHere =
        false
    ; thetaPreservationProvedHereIsFalse =
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
        thetaTailDecayPromotionImpossibleHere
    }

canonicalThetaTailDecayNoClayPromotion :
  clayNavierStokesPromoted canonicalNSThetaImpliesTailDecayReceipt ≡ false
canonicalThetaTailDecayNoClayPromotion =
  refl
