module DASHI.Physics.Plasma.KSW668MHDSelectedStateTransferExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Plasma.MHDPlusMinusProjectedPseudoEnergyExact as State
import DASHI.Physics.Plasma.MHDLiteralIdealElsasserGalerkinDynamicsExact as Dynamics
import DASHI.Physics.Plasma.MHDElsasserProjectedNonlinearCoefficientExact as Projected
import DASHI.Physics.Closure.NSTriadKNComplex3OrderedRealityCancellation as Ordered

------------------------------------------------------------------------
-- A1: the ACTUAL original-state physical observable and same-object weld.
-- The selected state satisfies all Fourier reality / transversality axioms
-- encoded by IdealElsasserFourierState. The associated signed transfer is
-- taken from the original Galerkin / projected-Elsasser application.
------------------------------------------------------------------------

doubleMagneticMode :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  State.IdealElsasserFourierState F E →
  Z3.FourierMode → C3.Complex3 F
doubleMagneticMode state k =
  C3.complex3Subtract
    (State.zPlus state k)
    (State.zMinus state k)

doubleMagneticSquaredStrength :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  State.IdealElsasserFourierState F E →
  Z3.FourierMode → C3.Carrier F
doubleMagneticSquaredStrength state k =
  C3.real
    (C3.hermitianPairing3
      (doubleMagneticMode state k)
      (doubleMagneticMode state k))

selectedPlusTransfer :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  C3.ModeInverseSquare F E →
  State.IdealElsasserFourierState F E →
  Z3.FourierMode → Z3.FourierMode → Z3.FourierMode →
  C3.Complex F
selectedPlusTransfer {E = E} I state k p q =
  Projected.testedElsasserOrderedTransfer
    E I k q (State.zMinus state p)
    (State.zPlus state q) (State.zPlus state k)

originalMHDSelectedStateNormalForm :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (I : C3.ModeInverseSquare F E)
    (state : State.IdealElsasserFourierState F E)
    (k p q : Z3.FourierMode) →
  Helical.Transverse E k (State.zPlus state k) →
  selectedPlusTransfer I state k p q
  ≡
  C3.complexRealPart
    (C3.complexMultiply
      (Ordered.minusI F)
      (C3.complexMultiply
        (C3.bilinearDot3 (State.zMinus state p) (C3.modeVector E q))
        (C3.hermitianPairing3
          (State.zPlus state k) (State.zPlus state q))))
originalMHDSelectedStateNormalForm {E = E} I state k p q transverse =
  Projected.elsasserOrderedTransferNormalForm
    E I k q (State.zMinus state p)
    (State.zPlus state q) (State.zPlus state k) transverse

originalMHDGalerkinProjectedSameState :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (I : C3.ModeInverseSquare F E)
    (state : State.IdealElsasserFourierState F E)
    (k p q : Z3.FourierMode) →
  Dynamics.plusOrderedInteraction I state k p q
  ≡ Projected.elsasserOrderedInteraction
      E I k q (State.zMinus state p) (State.zPlus state q)
originalMHDGalerkinProjectedSameState =
  Dynamics.plusInteractionIsProjectedElsasser

------------------------------------------------------------------------
-- The numerical original-form witness instantiates p=(1,0,0),
-- q=(0,1,0), k=p+q, with conjugate-paired Fourier coefficients and checks
-- the selected transfer +/-1 with identical squared magnetic magnitudes.
-- An Agda construction of those exact states, rational inverse-square
-- projector, and order proof remains the source-inhabitation gate.
------------------------------------------------------------------------
