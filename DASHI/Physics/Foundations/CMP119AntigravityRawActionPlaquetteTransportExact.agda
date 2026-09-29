{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRawActionPlaquetteTransportExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette

-- Transport the selected CMP119 source action through its own Eq. (2.23)
-- into the T4 rational projector.  The Action carrier is fixed rather than
-- replaced by an unrelated modeled action.

sourceActionPlaquetteEquation223 :
  ∀ {Density Background Fluctuation Wilson Small R Boundary Vacuum}
    (source : Raw.CMP119SourceNativeRawState
      Density Background Fluctuation Plaquette.LocalizedAction
      Wilson Small R Boundary Vacuum) k →
  Plaquette.plaquetteCoefficientProjector
    (Raw.effectiveAction source (suc k))
  ≡ Plaquette.plaquetteCoefficientProjector
    (Raw.assemble (Raw.actionAlgebra source)
      (Raw.wilsonCoefficient source (suc k))
      (Raw.wilsonActionTerm source (suc k))
      (Raw.regularSmallFieldTerm source (suc k))
      (Raw.rOperationTerm source (suc k))
      (Raw.boundaryTerm source (suc k))
      (Raw.vacuumEnergy source (suc k)))
sourceActionPlaquetteEquation223 source k =
  cong Plaquette.plaquetteCoefficientProjector
    (Raw.equation223 source (suc k))

selectedActionProjectionTransport :
  ∀ {Density Background Fluctuation Wilson Small R Boundary Vacuum}
    {source : Raw.CMP119SourceNativeRawState
      Density Background Fluctuation Plaquette.LocalizedAction
      Wilson Small R Boundary Vacuum}
    (selected : Plaquette.ExactOneStepEffectiveActionData Nat)
    (sameAction : ∀ k →
      Plaquette.effectiveAction selected k
      ≡ Raw.effectiveAction source (suc k))
    k →
  Plaquette.plaquetteCoefficientProjector
    (Plaquette.effectiveAction selected k)
  ≡ Plaquette.plaquetteCoefficientProjector
    (Raw.effectiveAction source (suc k))
selectedActionProjectionTransport selected sameAction k =
  cong Plaquette.plaquetteCoefficientProjector (sameAction k)
