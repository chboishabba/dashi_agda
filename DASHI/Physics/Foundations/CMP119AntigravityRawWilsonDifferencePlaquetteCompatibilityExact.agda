{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRawWilsonDifferencePlaquetteCompatibilityExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (_-_)
open import Relation.Binary.PropositionalEquality using (trans; sym)

import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.Foundations.CMP119AntigravityCMP109WilsonDifferenceOrientationExact as Orientation
import DASHI.Physics.Foundations.CMP119AntigravityRawActionSelectedBetaSameObjectExact as Action
import DASHI.Physics.Foundations.CMP119AntigravitySelectedActionFiniteModePhysicalWeldExact as Weld

-- CMP119 Eq (2.23) has a Wilson coefficient at each node, whereas T4
-- produces a one-step plaquette coefficient. The following identifies the
-- edge with the difference of TWO source-node Wilson coefficients, but ONLY
-- after showing both node coefficients represent the CMP109 inverse coupling.

rawSourceBetaIsWilsonNodeDifference :
  ∀ {trajectory Density Background Fluctuation ActionCarrier
       Wilson Small R Boundary Vacuum}
    {raw : Raw.CMP119SourceNativeRawState
      Density Background Fluctuation ActionCarrier
      Wilson Small R Boundary Vacuum}
    (nodeMeaning : ∀ k →
      Raw.wilsonCoefficient raw k ≡ Flow.inverseCoupling trajectory k)
    k →
  Flow.beta trajectory (suc k)
  ≡ Raw.wilsonCoefficient raw k - Raw.wilsonCoefficient raw (suc k)
rawSourceBetaIsWilsonNodeDifference {trajectory = trajectory} {raw = raw}
    nodeMeaning =
  Orientation.sourceBetaIsWilsonCoefficientDifference
    trajectory (Raw.wilsonCoefficient raw) nodeMeaning

rawPlaquetteEqualsWilsonNodeDifference :
  ∀ {trajectory Mode Atom finiteMode oneLoop remainder selected}
    {Density Background Fluctuation Wilson Small R Boundary Vacuum}
    {raw : Raw.CMP119SourceNativeRawState
      Density Background Fluctuation Plaquette.LocalizedAction
      Wilson Small R Boundary Vacuum}
    (nodeMeaning : ∀ k →
      Raw.wilsonCoefficient raw k ≡ Flow.inverseCoupling trajectory k)
    (selectedIsRaw : ∀ k →
      Plaquette.effectiveAction selected k ≡ Raw.effectiveAction raw (suc k))
    (physical : Weld.SelectedActionFiniteModePlaquetteIdentification
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      finiteMode oneLoop remainder selected)
    k →
  Plaquette.plaquetteCoefficientProjector
    (Raw.effectiveAction raw (suc k))
  ≡ Raw.wilsonCoefficient raw k - Raw.wilsonCoefficient raw (suc k)
rawPlaquetteEqualsWilsonNodeDifference nodeMeaning selectedIsRaw physical k =
  trans
    (sym (Action.rawCMP119SelectedBeta selectedIsRaw physical k))
    (rawSourceBetaIsWilsonNodeDifference nodeMeaning k)

-- This theorem is a consistency TEST. A physical action cannot satisfy
-- its premises if its complete Wilson coefficient and one-step projected
-- coefficient have incompatible source normalizations.
