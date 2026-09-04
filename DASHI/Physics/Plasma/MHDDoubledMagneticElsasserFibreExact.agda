module DASHI.Physics.Plasma.MHDDoubledMagneticElsasserFibreExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3RealityLawsRound35Exact as RealityLaws
import DASHI.Physics.Closure.NSTriadKNOrderedInteractionRealityRound35Exact as InteractionReality
import DASHI.Physics.Closure.NSTriadKNComplex3TransverseDifference as Difference
import DASHI.Physics.Closure.NSTriadKNLerayOutputTransversalityRound30Exact as LerayOut
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as Signed
import DASHI.Physics.Plasma.MHDPlusMinusProjectedPseudoEnergyExact as State
import DASHI.Physics.Plasma.MHDLiteralIdealElsasserGalerkinDynamicsExact as Dynamics

------------------------------------------------------------------------
-- DIVISION-FREE MAGNETIC FIBRE
--
-- Physical b_A = (z+ - z-)/2.  For cancellation it is cleaner to keep the
-- doubled magnetic coordinate
--
--   B~ = z+ - z-
--
-- and its doubled tangent
--
--   dB~ = N+ - N-.
--
-- This avoids introducing an inverse of 2 into the invariant proof.  The
-- physical normalization can be restored only after the zero theorem.
------------------------------------------------------------------------

doubledMagnetic :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  State.IdealElsasserFourierState F E →
  Z3.FourierMode → C3.Complex3 F
doubledMagnetic state k =
  C3.complex3Subtract (State.zPlus state k) (State.zMinus state k)

doubledInductionOrderedInteraction :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  C3.ModeInverseSquare F E →
  State.IdealElsasserFourierState F E →
  Z3.FourierMode → Z3.FourierMode → Z3.FourierMode → C3.Complex3 F
doubledInductionOrderedInteraction I state k p q =
  C3.complex3Subtract
    (Dynamics.plusOrderedInteraction I state k p q)
    (Dynamics.minusOrderedInteraction I state k p q)

------------------------------------------------------------------------
-- The doubled magnetic fibre inherits the two structural constraints exactly.
------------------------------------------------------------------------

doubledMagneticReality :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (state : State.IdealElsasserFourierState F E)
    (k : Z3.FourierMode) →
  doubledMagnetic state (Z3.negateMode k)
  ≡ C3.complex3Conjugate (doubledMagnetic state k)
doubledMagneticReality state k =
  trans
    (cong₂ C3.complex3Subtract
      (State.plusReality state k)
      (State.minusReality state k))
    (sym
      (RealityLaws.complex3ConjugateSubtract
        (State.zPlus state k)
        (State.zMinus state k)))

doubledMagneticTransverse :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (state : State.IdealElsasserFourierState F E)
    (k : Z3.FourierMode) →
  Helical.Transverse E k (doubledMagnetic state k)
doubledMagneticTransverse {E = E} state k =
  Difference.transverseSubtract E k
    (State.zPlus state k)
    (State.zMinus state k)
    (State.plusDivergenceFree state k)
    (State.minusDivergenceFree state k)

------------------------------------------------------------------------
-- Every ordered Galerkin interaction is transverse at its output because its
-- literal definition contains P_k.  The outer -i scale preserves the zero dot.
------------------------------------------------------------------------

orderedInteractionTransverse :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k p q : Z3.FourierMode) →
  Z3.NonZeroMode k →
  (uP uQ : C3.Complex3 F) →
  Helical.Transverse E k
    (Signed.orderedVelocityInteraction
      (C3.complex3VelocityGalerkinLaws F E I)
      k p q uP uQ)
orderedInteractionTransverse {F = F} E I k p q nonzero uP uQ =
  trans
    (Scaling.bilinearDot3ScaleRight
      (Signed.minusImaginary (C3.complex3VelocityGalerkinLaws F E I))
      (C3.modeVector E k)
      projected)
    (trans
      (cong
        (C3.complexMultiply
          (Signed.minusImaginary (C3.complex3VelocityGalerkinLaws F E I)))
        (LerayOut.lerayOutputTransverseExact E I k nonzero raw))
      (Field.complexMultiplyZeroRight
        (Signed.minusImaginary (C3.complex3VelocityGalerkinLaws F E I))))
  where
  raw =
    C3.complex3Scale
      (C3.bilinearDot3 uP (C3.modeVector E q))
      uQ
  projected = C3.lerayProject3 E I k raw

doubledInductionOrderedTransverse :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (I : C3.ModeInverseSquare F E)
    (state : State.IdealElsasserFourierState F E)
    (k p q : Z3.FourierMode) →
  Z3.NonZeroMode k →
  Helical.Transverse E k
    (doubledInductionOrderedInteraction I state k p q)
doubledInductionOrderedTransverse {F = F} {E = E}
    I state k p q nonzero =
  Difference.transverseSubtract E k
    (Dynamics.plusOrderedInteraction I state k p q)
    (Dynamics.minusOrderedInteraction I state k p q)
    (orderedInteractionTransverse E I k p q nonzero
      (State.zMinus state p) (State.zPlus state q))
    (orderedInteractionTransverse E I k p q nonzero
      (State.zPlus state p) (State.zMinus state q))

------------------------------------------------------------------------
-- Single-triad Fourier reality of the doubled induction tangent.
------------------------------------------------------------------------

doubledInductionOrderedReality :
  ∀ {r : Level} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (I : C3.ModeInverseSquare F E)
    (state : State.IdealElsasserFourierState F E)
    (k p q : Z3.FourierMode) →
  doubledInductionOrderedInteraction I state
    (Z3.negateMode k) (Z3.negateMode p) (Z3.negateMode q)
  ≡ C3.complex3Conjugate
      (doubledInductionOrderedInteraction I state k p q)
doubledInductionOrderedReality {F = F} {E = E} I state k p q
  rewrite State.minusReality state p
        | State.plusReality state q
        | State.plusReality state p
        | State.minusReality state q =
  trans
    (cong₂ C3.complex3Subtract
      (InteractionReality.orderedVelocityInteractionReality
        F E I k p q (State.zMinus state p) (State.zPlus state q))
      (InteractionReality.orderedVelocityInteractionReality
        F E I k p q (State.zPlus state p) (State.zMinus state q)))
    (sym
      (RealityLaws.complex3ConjugateSubtract
        (Dynamics.plusOrderedInteraction I state k p q)
        (Dynamics.minusOrderedInteraction I state k p q)))

record DoubledMagneticBoundary : Set where
  constructor doubled-magnetic-boundary
  field
    noHalfInverseNeededForCancellation : Bool
    noHalfInverseNeededForCancellationIsTrue :
      noHalfInverseNeededForCancellation ≡ true

    doubledMagneticRealityOwned : Bool
    doubledMagneticRealityOwnedIsTrue : doubledMagneticRealityOwned ≡ true

    doubledMagneticTransverseOwned : Bool
    doubledMagneticTransverseOwnedIsTrue : doubledMagneticTransverseOwned ≡ true

    doubledInductionRealityOwned : Bool
    doubledInductionRealityOwnedIsTrue : doubledInductionRealityOwned ≡ true

    doubledInductionTransverseOwned : Bool
    doubledInductionTransverseOwnedIsTrue : doubledInductionTransverseOwned ≡ true

canonicalDoubledMagneticBoundary : DoubledMagneticBoundary
canonicalDoubledMagneticBoundary =
  doubled-magnetic-boundary true refl true refl true refl true refl true refl
