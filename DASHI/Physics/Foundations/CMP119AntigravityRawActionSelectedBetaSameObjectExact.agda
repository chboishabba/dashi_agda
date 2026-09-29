{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRawActionSelectedBetaSameObjectExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
import DASHI.Physics.Foundations.CMP119AntigravityRawActionPlaquetteTransportExact as Source
import DASHI.Physics.Foundations.CMP119AntigravitySelectedActionFiniteModePhysicalWeldExact as Weld

-- The CMP119 Eq.2.23 action is the only action in the conclusion. The
-- already-available selected finite-mode coefficient theorem is transported
-- through an explicit selected-action = raw-successor-action law.

rawCMP119SelectedBeta :
  ∀ {trajectory Mode Atom finiteMode oneLoop remainder selected}
    {Density Background Fluctuation Wilson Small R Boundary Vacuum}
    {raw : Raw.CMP119SourceNativeRawState
      Density Background Fluctuation Plaquette.LocalizedAction
      Wilson Small R Boundary Vacuum}
    (sameAction : ∀ k →
      Plaquette.effectiveAction selected k
      ≡ Raw.effectiveAction raw (suc k))
    (physical : Weld.SelectedActionFiniteModePlaquetteIdentification
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      finiteMode oneLoop remainder selected)
    k →
  Flow.beta trajectory (suc k)
  ≡ Plaquette.plaquetteCoefficientProjector
      (Raw.effectiveAction raw (suc k))
rawCMP119SelectedBeta {selected = selected} sameAction physical k =
  trans (Weld.sourceBetaIsSelectedActionCoefficient physical k)
    (Source.selectedActionProjectionTransport selected sameAction k)

rawCMP119Equation223Beta :
  ∀ {trajectory Mode Atom finiteMode oneLoop remainder selected}
    {Density Background Fluctuation Wilson Small R Boundary Vacuum}
    {raw : Raw.CMP119SourceNativeRawState
      Density Background Fluctuation Plaquette.LocalizedAction
      Wilson Small R Boundary Vacuum}
    (sameAction : ∀ k →
      Plaquette.effectiveAction selected k
      ≡ Raw.effectiveAction raw (suc k))
    (physical : Weld.SelectedActionFiniteModePlaquetteIdentification
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      finiteMode oneLoop remainder selected)
    k →
  Flow.beta trajectory (suc k)
  ≡ Plaquette.plaquetteCoefficientProjector
    (Raw.assemble (Raw.actionAlgebra raw)
      (Raw.wilsonCoefficient raw (suc k))
      (Raw.wilsonActionTerm raw (suc k))
      (Raw.regularSmallFieldTerm raw (suc k))
      (Raw.rOperationTerm raw (suc k))
      (Raw.boundaryTerm raw (suc k))
      (Raw.vacuumEnergy raw (suc k)))
rawCMP119Equation223Beta {raw = raw} sameAction physical k =
  trans (rawCMP119SelectedBeta sameAction physical k)
    (Source.sourceActionPlaquetteEquation223 raw k)
