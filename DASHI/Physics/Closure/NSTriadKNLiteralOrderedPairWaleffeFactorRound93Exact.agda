module DASHI.Physics.Closure.NSTriadKNLiteralOrderedPairWaleffeFactorRound93Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: Peter Constantin; Andrew Majda.
-- Title: "The Beltrami spectrum for incompressible fluid flows".
-- Communications in Mathematical Physics 115 (1988), 435--456.
-- DOI: 10.1007/BF01218019.
--
-- ROUND93 / LITERAL TESTED WALEFFE FACTOR
--
-- This module closes the local physical bridge that Round92 left abstract.
-- For one literal resonant ordered pair p+q=k, tested against the SAME
-- transverse output coefficient u_k, assume only that the two input modes are
-- curl eigenmodes
--
--   curl_p u_p = a u_p,    curl_q u_q = b u_q.
--
-- Then the repository's exact symmetrised Galerkin transfer is
--
--   T_k = Re [ (b-a) <u_k , u_p x u_q> ].
--
-- Thus the Waleffe signed-eigenvalue difference is not imported as an
-- alternate coefficient definition.  It is derived from the existing literal
-- convective coefficient through the exact convective/rotational identity and
-- transverse elimination of the resonant gradient term.
--
-- The remaining COMMON-amplitude issue across the three energy legs is now
-- only cyclic/reality transport of the geometric triple product.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3EnergyCancellation as Energy
import DASHI.Physics.Closure.NSTriadKNComplex3OrderedRealityCancellation as Ordered
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNConvectiveRotationalTriadIdentityRound93Exact as Conv
import DASHI.Physics.Closure.NSTriadKNHelicalInputDifferenceFactorizationRound93Exact as Difference
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross

minusI : ∀ {r} (F : C3.RealField r) → C3.Complex F
minusI F = C3.complexNegate (C3.complexI F)

resonanceRecord :
  (tau : Physical.PhysicalTriadIncidence) →
  Z3.Resonance (Physical.p tau) (Physical.q tau) (Physical.k tau)
resonanceRecord tau = record { closes = Physical.resonance tau }

orderedPairConvectiveNormalForm :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.DivergenceFreeCondition E velocity →
  Audit.orderedPairSignedTransferAt E I tau velocity
  ≡
  C3.complexRealPart
    (C3.complexMultiply (minusI F)
      (C3.hermitianPairing3
        (velocity (Physical.k tau))
        (Conv.convectivePair
          (C3.modeVector E (Physical.p tau))
          (C3.modeVector E (Physical.q tau))
          (velocity (Physical.p tau))
          (velocity (Physical.q tau)))))
orderedPairConvectiveNormalForm {F = F} E I tau velocity divergenceFree =
  trans
    (Energy.orderedPairCoefficientIsOrderedSum E I tau velocity)
    (trans
      (cong₂ C3.complexAdd
        (Ordered.orderedTransferNormalForm E I tau velocity divergenceFree)
        (Ordered.orderedTransferNormalForm
          E I (Symmetry.swapTriad tau) velocity divergenceFree))
      finalAlgebra)
  where
  uP = velocity (Physical.p tau)
  uQ = velocity (Physical.q tau)
  uK = velocity (Physical.k tau)
  pWave = C3.modeVector E (Physical.p tau)
  qWave = C3.modeVector E (Physical.q tau)
  alpha = C3.bilinearDot3 uP qWave
  beta = C3.bilinearDot3 uQ pWave
  pairQ = C3.hermitianPairing3 uK uQ
  pairP = C3.hermitianPairing3 uK uP

  pairingConvective :
    C3.hermitianPairing3 uK (Conv.convectivePair pWave qWave uP uQ)
    ≡
    C3.complexAdd
      (C3.complexMultiply alpha pairQ)
      (C3.complexMultiply beta pairP)
  pairingConvective =
    trans
      (Algebra.hermitianAddRight
        uK
        (C3.complex3Scale alpha uQ)
        (C3.complex3Scale beta uP))
      (cong₂ C3.complexAdd
        (Algebra.hermitianScaleRight uK uQ alpha)
        (Algebra.hermitianScaleRight uK uP beta))

  realPartCombine :
    C3.complexAdd
      (C3.complexRealPart
        (C3.complexMultiply (minusI F)
          (C3.complexMultiply alpha pairQ)))
      (C3.complexRealPart
        (C3.complexMultiply (minusI F)
          (C3.complexMultiply beta pairP)))
    ≡
    C3.complexRealPart
      (C3.complexMultiply (minusI F)
        (C3.complexAdd
          (C3.complexMultiply alpha pairQ)
          (C3.complexMultiply beta pairP)))
  realPartCombine =
    trans
      (sym
        (Algebra.complexRealPartAdd
          (C3.complexMultiply (minusI F) (C3.complexMultiply alpha pairQ))
          (C3.complexMultiply (minusI F) (C3.complexMultiply beta pairP))))
      (cong C3.complexRealPart
        (sym
          (Ring.complexDistributeLeft
            (minusI F)
            (C3.complexMultiply alpha pairQ)
            (C3.complexMultiply beta pairP))))

  finalAlgebra :
    C3.complexAdd
      (C3.complexRealPart
        (C3.complexMultiply (minusI F)
          (C3.complexMultiply alpha pairQ)))
      (C3.complexRealPart
        (C3.complexMultiply (minusI F)
          (C3.complexMultiply beta pairP)))
    ≡
    C3.complexRealPart
      (C3.complexMultiply (minusI F)
        (C3.hermitianPairing3 uK
          (Conv.convectivePair pWave qWave uP uQ)))
  finalAlgebra =
    trans realPartCombine
      (cong
        (λ value → C3.complexRealPart
          (C3.complexMultiply (minusI F) value))
        (sym pairingConvective))

negativeRotationalPairHasMinusIConvectivePairing :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    {p q k : Z3.FourierMode}
    (resonance : Z3.Resonance p q k)
    (uP uQ testK : C3.Complex3 F) →
  Helical.Transverse E k testK →
  C3.hermitianPairing3 testK
    (C3.complex3Negate
      (Conv.rotationalPair
        (C3.modeVector E p) (C3.modeVector E q) uP uQ))
  ≡
  C3.complexMultiply (minusI F)
    (C3.hermitianPairing3 testK
      (Conv.convectivePair
        (C3.modeVector E p) (C3.modeVector E q) uP uQ))
negativeRotationalPairHasMinusIConvectivePairing {F = F}
  E {p} {q} {k} resonance uP uQ testK transverse =
  trans
    (Additive.hermitianPairingNegateRight testK
      (Conv.rotationalPair
        (C3.modeVector E p) (C3.modeVector E q) uP uQ))
    (trans
      (cong C3.complexNegate
        (trans
          (cong (C3.hermitianPairing3 testK)
            (Conv.rotationalPairEqualsIConvectiveMinusGradient
              (C3.modeVector E p) (C3.modeVector E q) uP uQ))
          (trans
            (Algebra.hermitianScaleRight testK
              (C3.complex3Subtract
                (Conv.convectivePair
                  (C3.modeVector E p) (C3.modeVector E q) uP uQ)
                (Conv.gradientPair
                  (C3.modeVector E p) (C3.modeVector E q) uP uQ))
              (C3.complexI F))
            (cong
              (C3.complexMultiply (C3.complexI F))
              (trans
                (Additive.hermitianPairingSubtractRight testK
                  (Conv.convectivePair
                    (C3.modeVector E p) (C3.modeVector E q) uP uQ)
                  (Conv.gradientPair
                    (C3.modeVector E p) (C3.modeVector E q) uP uQ))
                (cong
                  (C3.complexSubtract
                    (C3.hermitianPairing3 testK
                      (Conv.convectivePair
                        (C3.modeVector E p) (C3.modeVector E q) uP uQ)))
                  (Conv.transverseTestKillsResonantGradient
                    E resonance uP uQ testK transverse)))))))
      finalScalar)
  where
  module R = Ring.Solver F
  c = C3.hermitianPairing3 testK
        (Conv.convectivePair
          (C3.modeVector E p) (C3.modeVector E q) uP uQ)

  finalScalar :
    C3.complexNegate
      (C3.complexMultiply (C3.complexI F)
        (C3.complexSubtract c (C3.complexZero F)))
    ≡ C3.complexMultiply (minusI F) c
  finalScalar =
    R.solve 2
      (λ i c → R.⊝ (i R.⊗ (c R.⊕ (R.⊝ (R.Κ (C3.complexZero F)))))
        R.⊜ (R.⊝ i) R.⊗ c)
      refl (C3.complexI F) c

record LiteralHelicalOrderedPairData
    {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence) : Set r where
  constructor literal-helical-ordered-pair-data
  field
    velocity : Z3.FourierMode → C3.Complex3 F
    divergenceFree : Audit.DivergenceFreeCondition E velocity
    signedEigenP signedEigenQ : C3.Complex F
    curlEigenP :
      Conv.curlFromWave
        (C3.modeVector E (Physical.p tau))
        (velocity (Physical.p tau))
      ≡ C3.complex3Scale signedEigenP (velocity (Physical.p tau))
    curlEigenQ :
      Conv.curlFromWave
        (C3.modeVector E (Physical.q tau))
        (velocity (Physical.q tau))
      ≡ C3.complex3Scale signedEigenQ (velocity (Physical.q tau))

open LiteralHelicalOrderedPairData public

literalOrderedPairWaleffeFactor :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (H : LiteralHelicalOrderedPairData E I tau) →
  Audit.orderedPairSignedTransferAt E I tau (velocity H)
  ≡
  C3.complexRealPart
    (C3.complexMultiply
      (C3.complexSubtract (signedEigenQ H) (signedEigenP H))
      (C3.hermitianPairing3
        (velocity H (Physical.k tau))
        (Cross.complex3Cross
          (velocity H (Physical.p tau))
          (velocity H (Physical.q tau)))))
literalOrderedPairWaleffeFactor {F = F} E I tau H =
  trans
    (orderedPairConvectiveNormalForm E I tau (velocity H) (divergenceFree H))
    (trans
      (cong C3.complexRealPart
        (sym
          (negativeRotationalPairHasMinusIConvectivePairing
            E
            (resonanceRecord tau)
            (velocity H (Physical.p tau))
            (velocity H (Physical.q tau))
            (velocity H (Physical.k tau))
            outputTransverse)))
      (cong C3.complexRealPart finalPairing))
  where
  outputTransverse :
    Helical.Transverse E (Physical.k tau) (velocity H (Physical.k tau))
  outputTransverse =
    trans
      (Algebra.bilinearDotCommutative
        (C3.modeVector E (Physical.k tau))
        (velocity H (Physical.k tau)))
      (divergenceFree H (Physical.k tau))

  rotationalFactor :
    Conv.rotationalPair
      (C3.modeVector E (Physical.p tau))
      (C3.modeVector E (Physical.q tau))
      (velocity H (Physical.p tau))
      (velocity H (Physical.q tau))
    ≡
    C3.complex3Scale
      (C3.complexSubtract (signedEigenP H) (signedEigenQ H))
      (Cross.complex3Cross
        (velocity H (Physical.p tau))
        (velocity H (Physical.q tau)))
  rotationalFactor =
    trans
      (cong₂
        (λ omegaP omegaQ →
          Difference.symmetrisedRotationalInteraction
            omegaP (velocity H (Physical.q tau))
            omegaQ (velocity H (Physical.p tau)))
        (curlEigenP H) (curlEigenQ H))
      (Difference.helicalInputDifferenceFactorization
        (signedEigenP H) (signedEigenQ H)
        (velocity H (Physical.p tau))
        (velocity H (Physical.q tau)))

  finalPairing :
    C3.hermitianPairing3
      (velocity H (Physical.k tau))
      (C3.complex3Negate
        (Conv.rotationalPair
          (C3.modeVector E (Physical.p tau))
          (C3.modeVector E (Physical.q tau))
          (velocity H (Physical.p tau))
          (velocity H (Physical.q tau))))
    ≡
    C3.complexMultiply
      (C3.complexSubtract (signedEigenQ H) (signedEigenP H))
      (C3.hermitianPairing3
        (velocity H (Physical.k tau))
        (Cross.complex3Cross
          (velocity H (Physical.p tau))
          (velocity H (Physical.q tau))))
  finalPairing =
    let
      crossPQ = Cross.complex3Cross
        (velocity H (Physical.p tau))
        (velocity H (Physical.q tau))
      deltaPQ = C3.complexSubtract (signedEigenP H) (signedEigenQ H)
      deltaQP = C3.complexSubtract (signedEigenQ H) (signedEigenP H)
      module R = Ring.Solver F

      vectorSign :
        C3.complex3Negate (C3.complex3Scale deltaPQ crossPQ)
        ≡ C3.complex3Scale deltaQP crossPQ
      vectorSign =
        Algebra.complex3Ext
          (R.solve 3
            (λ p q x → R.⊝ ((p R.⊕ (R.⊝ q)) R.⊗ x)
              R.⊜ ((q R.⊕ (R.⊝ p)) R.⊗ x))
            refl (signedEigenP H) (signedEigenQ H) (C3.x crossPQ))
          (R.solve 3
            (λ p q y → R.⊝ ((p R.⊕ (R.⊝ q)) R.⊗ y)
              R.⊜ ((q R.⊕ (R.⊝ p)) R.⊗ y))
            refl (signedEigenP H) (signedEigenQ H) (C3.y crossPQ))
          (R.solve 3
            (λ p q z → R.⊝ ((p R.⊕ (R.⊝ q)) R.⊗ z)
              R.⊜ ((q R.⊕ (R.⊝ p)) R.⊗ z))
            refl (signedEigenP H) (signedEigenQ H) (C3.z crossPQ))

      vectorRewrite :
        C3.complex3Negate
          (Conv.rotationalPair
            (C3.modeVector E (Physical.p tau))
            (C3.modeVector E (Physical.q tau))
            (velocity H (Physical.p tau))
            (velocity H (Physical.q tau)))
        ≡ C3.complex3Scale deltaQP crossPQ
      vectorRewrite =
        trans
          (cong C3.complex3Negate rotationalFactor)
          vectorSign
    in
    trans
      (cong (C3.hermitianPairing3 (velocity H (Physical.k tau))) vectorRewrite)
      (Algebra.hermitianScaleRight
        (velocity H (Physical.k tau)) crossPQ deltaQP)

round93LiteralOrderedPairWaleffeFactorClosed : Bool
round93LiteralOrderedPairWaleffeFactorClosed = true

round93ThreeLegCommonPhaseAmplitudeClosed : Bool
round93ThreeLegCommonPhaseAmplitudeClosed = false

round93LiteralOrderedPairWaleffeFactorClosedIsTrue :
  round93LiteralOrderedPairWaleffeFactorClosed ≡ true
round93LiteralOrderedPairWaleffeFactorClosedIsTrue = refl

round93ThreeLegCommonPhaseAmplitudeClosedIsFalse :
  round93ThreeLegCommonPhaseAmplitudeClosed ≡ false
round93ThreeLegCommonPhaseAmplitudeClosedIsFalse = refl
