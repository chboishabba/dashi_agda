{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1R143LocalizedCompilerExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans)

import DASHI.Physics.Foundations.CMP119CosmologyE1LocalizedD1CovarianceExact as LocalE1
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanBC2CompactGroupSameDensityRound119Exact as BC2
import DASHI.Physics.YangMills.BalabanBC2FiniteLocalizedFirstVariationRound143Exact as R143

record R143LocalizedEuclideanCovariance
    {History Cell : Set}
    {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs History Cell cutoff)
    (laws : R143.PresentCutBC2FirstVariationLinearity present)
    (EuclideanAction : Set)
    : Set₁ where
  field
    localized :
      LocalE1.LocalizedD1EuclideanCovariance
        (Carrier.finiteAction (Present.bc1Carrier present))
        (R143.asFirstVariationLinearity laws)
        EuclideanAction

open R143LocalizedEuclideanCovariance public

bc2FirstVariationCovariantFromLocalizedD1 :
  ∀ {History Cell cutoff present laws EuclideanAction}
    (dataSet :
      R143LocalizedEuclideanCovariance
        {History = History} {Cell = Cell} {cutoff = cutoff}
        present laws EuclideanAction)
    action background tangent →
  BC2.firstVariation (Present.bc2 present)
    (Carrier.effectivePotential (Present.bc1Carrier present))
    (LocalE1.actConfiguration (localized dataSet) action background)
    (LocalE1.actTangent (localized dataSet) action tangent)
  ≡
  BC2.firstVariation (Present.bc2 present)
    (Carrier.effectivePotential (Present.bc1Carrier present))
    background tangent
bc2FirstVariationCovariantFromLocalizedD1
    {present = present} {laws = laws}
    dataSet action background tangent =
  trans
    (R143.bc2GlobalFirstVariationIsFiniteLocalizedSum
      laws
      (LocalE1.actConfiguration (localized dataSet) action background)
      (LocalE1.actTangent (localized dataSet) action tangent))
    (trans
      (LocalE1.finiteLocalizedFirstVariationCovariant
        (localized dataSet) action background tangent)
      (sym
        (R143.bc2GlobalFirstVariationIsFiniteLocalizedSum
          laws background tangent)))

globalBC2CovarianceNoLongerPrimitive : Bool
globalBC2CovarianceNoLongerPrimitive = true

e1GlobalDerivativeResidualNowLocalComponentCovariance : Bool
e1GlobalDerivativeResidualNowLocalComponentCovariance = true
