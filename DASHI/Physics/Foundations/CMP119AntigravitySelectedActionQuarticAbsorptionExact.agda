{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravitySelectedActionQuarticAbsorptionExact where

-- The existing finite-mode atom/mode inequalities already prove that the
-- quartic interaction cannot cancel more than half the *certified* Gaussian
-- floor. This is an actual quantitative estimate, not a reflexive
-- |R| <= |R|. The lower bound is transported to the physically selected
-- plaquette projector only through its exact same-object coefficient weld.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _+_; _≤_; 0ℚ)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Local
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as Finite
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.Foundations.CMP119AntigravitySelectedActionFiniteModePhysicalWeldExact as Weld

selectedActionGaussianHalfFloor :
  ∀ {trajectory Mode Atom finiteMode oneLoop remainder selected}
    (source : Weld.SelectedActionFiniteModePlaquetteIdentification
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      finiteMode oneLoop remainder selected)
    k →
  Local.half * Local.computedGaussianLower
      (Finite.gaussianAt finiteMode k)
  ≤ Plaquette.plaquetteCoefficientProjector
      (Plaquette.effectiveAction selected k)
selectedActionGaussianHalfFloor {trajectory = trajectory}
    {finiteMode = finiteMode} source k =
  let
    gaussian = Finite.gaussianAt finiteMode k
    interaction = Finite.interactionAt finiteMode k
    floorBelowSplit :
      Local.half * Local.computedGaussianLower gaussian
      ≤ Local.betaZ gaussian + Local.betaInt interaction
    floorBelowSplit =
      Local.betaSplitLowerAfterQuarticAbsorption
        gaussian interaction
        (Finite.gamma finiteMode k)
        (Finite.interactionCouplingNonnegative finiteMode k)
        (Finite.gammaNonnegative finiteMode k)
        (Finite.interactionCouplingBelowGamma finiteMode k)
        (Finite.interactionCoefficientTotalNonnegative finiteMode k)
        (Finite.quarticAbsorption finiteMode k)

    floorBelowSource :
      Local.half * Local.computedGaussianLower gaussian
      ≤ Flow.beta trajectory (suc k)
    floorBelowSource =
      subst
        (λ value →
          Local.half * Local.computedGaussianLower gaussian ≤ value)
        (sym (Finite.sourceBetaSplitExact finiteMode k))
        floorBelowSplit
  in
  subst
    (λ value →
      Local.half * Local.computedGaussianLower gaussian ≤ value)
    (Weld.sourceBetaIsSelectedActionCoefficient source k)
    floorBelowSource
