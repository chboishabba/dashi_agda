module DASHI.Physics.Closure.NSTriadKNSelfWaleffePhaseProjectedCrossMassRound106Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- ROUND106 / SELF PHASE FORCING IS NOT AN OPAQUE NETWORK TERM
--
-- Combine the new vector Waleffe self-forcing normal form
--
--   N_k^{p,q}=(lambda_q-lambda_p) P_k(u_p x u_q)
--
-- with exact Hermitian self-adjointness and idempotence of P_k.  For a real
-- signed eigenvalue difference delta=lambda_q-lambda_p,
--
--   <N_k^{p,q}, u_p x u_q>
--     = delta <P_k X, P_k X>,     X=u_p x u_q.
--
-- Hence the k-slot contribution to the cubic Waleffe phase derivative is an
-- explicit signed eigenvalue difference times a projected-cross SQUARE MASS.
-- The self part is therefore algebraically structured; it must not be taxed as
-- arbitrary positive external forcing.  Only the genuinely external remainder
-- should enter the later occupation/Schur budget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNLeraySelfAdjointness as SelfAdjoint
import DASHI.Physics.Closure.NSTriadKNLerayOutputTransversalityRound30Exact as LerayExact
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNProjectedHelicalSelfForcingVectorRound106Exact as Vector

projectedCrossPairingIsProjectedCrossSelfPairing :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {p q k}
    (H : Vector.ProjectedHelicalPairData E I p q k) →
  let X = Cross.complex3Cross (Vector.uP H) (Vector.uQ H)
      PX = C3.lerayProject3 E I k X
  in
  C3.hermitianPairing3 PX X ≡ C3.hermitianPairing3 PX PX
projectedCrossPairingIsProjectedCrossSelfPairing {F = F} {E} {I} {p} {q} {k} H =
  let
    X = Cross.complex3Cross (Vector.uP H) (Vector.uQ H)
    PX = C3.lerayProject3 E I k X

    moveOnce :
      C3.hermitianPairing3 PX X ≡ C3.hermitianPairing3 X PX
    moveOnce = SelfAdjoint.leraySelfAdjoint E I k X X

    moveTwice :
      C3.hermitianPairing3 PX PX
      ≡ C3.hermitianPairing3 X (C3.lerayProject3 E I k PX)
    moveTwice = SelfAdjoint.leraySelfAdjoint E I k X PX

    idempotent = LerayExact.lerayIdempotentExact
      E I k (Vector.outputNonzero H) X

    projectedAgain :
      C3.hermitianPairing3 X (C3.lerayProject3 E I k PX)
      ≡ C3.hermitianPairing3 X PX
    projectedAgain = cong (C3.hermitianPairing3 X) idempotent

    selfToMoved :
      C3.hermitianPairing3 PX PX ≡ C3.hermitianPairing3 X PX
    selfToMoved = trans moveTwice projectedAgain
  in
  trans moveOnce (sym selfToMoved)

selfPhaseLegExact :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {p q k}
    (H : Vector.ProjectedHelicalPairData E I p q k) →
  C3.complexConjugate
    (C3.complexSubtract (Vector.signedEigenQ H) (Vector.signedEigenP H))
  ≡ C3.complexSubtract (Vector.signedEigenQ H) (Vector.signedEigenP H) →
  let X = Cross.complex3Cross (Vector.uP H) (Vector.uQ H)
      PX = C3.lerayProject3 E I k X
      force =
        DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient.orderedPairVelocityInteraction
          (C3.complex3VelocityGalerkinLaws F E I)
          k p q (Vector.uP H) (Vector.uQ H)
  in
  C3.hermitianPairing3 force X
  ≡ C3.complexMultiply
      (C3.complexSubtract (Vector.signedEigenQ H) (Vector.signedEigenP H))
      (C3.hermitianPairing3 PX PX)
selfPhaseLegExact {F = F} {E} {I} {p} {q} {k} H deltaReal =
  let
    X = Cross.complex3Cross (Vector.uP H) (Vector.uQ H)
    PX = C3.lerayProject3 E I k X
    delta = C3.complexSubtract (Vector.signedEigenQ H) (Vector.signedEigenP H)
    vectorMeaning = Vector.projectedHelicalOrderedPairVector H
  in
  trans
    (cong (λ force → C3.hermitianPairing3 force X) vectorMeaning)
    (trans
      (Scaling.hermitianPairingScaleLeft delta PX X)
      (trans
        (cong
          (λ scalar → C3.complexMultiply scalar
            (C3.hermitianPairing3 PX X))
          deltaReal)
        (cong (C3.complexMultiply delta)
          (projectedCrossPairingIsProjectedCrossSelfPairing H))))

round106SelfWaleffePhaseProjectedCrossMassClosed : Bool
round106SelfWaleffePhaseProjectedCrossMassClosed = true

round106SelfPhaseMayBeTaxedAsArbitraryExternalForcing : Bool
round106SelfPhaseMayBeTaxedAsArbitraryExternalForcing = false

round106SelfWaleffePhaseProjectedCrossMassClosedIsTrue :
  round106SelfWaleffePhaseProjectedCrossMassClosed ≡ true
round106SelfWaleffePhaseProjectedCrossMassClosedIsTrue = refl

round106SelfPhaseMayBeTaxedAsArbitraryExternalForcingIsFalse :
  round106SelfPhaseMayBeTaxedAsArbitraryExternalForcing ≡ false
round106SelfPhaseMayBeTaxedAsArbitraryExternalForcingIsFalse = refl
