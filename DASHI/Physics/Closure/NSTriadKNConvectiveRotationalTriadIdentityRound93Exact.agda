module DASHI.Physics.Closure.NSTriadKNConvectiveRotationalTriadIdentityRound93Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- ROUND93 / CONVECTIVE <-> ROTATIONAL FOURIER IDENTITY
--
-- For arbitrary complex Fourier vectors p,q,u_p,u_q, define
--
--   omega_p = i (p x u_p),   omega_q = i (q x u_q).
--
-- Then the symmetrised rotational interaction satisfies the exact vector law
--
--   omega_p x u_q + omega_q x u_p
--     = i [ C(p,q;u_p,u_q) - G(p,q;u_p,u_q) ],
--
-- where
--
--   C = (u_p.q)u_q + (u_q.p)u_p,
--   G = (u_p.u_q)(p+q).
--
-- Thus the difference between rotational and convective forms is literally
-- longitudinal.  On a resonant triad p+q=k, pairing with a transverse output
-- kills G exactly.  This is the local algebraic bridge required to promote the
-- Round93 helical signed-eigenvalue factorization to the repository's literal
-- convective Galerkin coefficient.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNHelicalInputDifferenceFactorizationRound93Exact as HelicalFactor
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical

curlFromWave :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
curlFromWave {F = F} wave value =
  C3.complex3Scale (C3.complexI F) (Cross.complex3Cross wave value)

convectivePair :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
convectivePair waveP waveQ uP uQ =
  C3.complex3Add
    (C3.complex3Scale (C3.bilinearDot3 uP waveQ) uQ)
    (C3.complex3Scale (C3.bilinearDot3 uQ waveP) uP)

gradientPair :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
gradientPair waveP waveQ uP uQ =
  C3.complex3Scale
    (C3.bilinearDot3 uP uQ)
    (C3.complex3Add waveP waveQ)

rotationalPair :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
rotationalPair waveP waveQ uP uQ =
  HelicalFactor.symmetrisedRotationalInteraction
    (curlFromWave waveP uP) uQ
    (curlFromWave waveQ uQ) uP

rotationalPairEqualsIConvectiveMinusGradient :
  ∀ {r} {F : C3.RealField r}
    (waveP waveQ uP uQ : C3.Complex3 F) →
  rotationalPair waveP waveQ uP uQ
  ≡
  C3.complex3Scale (C3.complexI F)
    (C3.complex3Subtract
      (convectivePair waveP waveQ uP uQ)
      (gradientPair waveP waveQ uP uQ))
rotationalPairEqualsIConvectiveMinusGradient {F = F}
  waveP waveQ uP uQ =
  Algebra.complex3Ext xProof yProof zProof
  where
  module R = Ring.Solver F
  i = C3.complexI F
  px = C3.x waveP
  py = C3.y waveP
  pz = C3.z waveP
  qx = C3.x waveQ
  qy = C3.y waveQ
  qz = C3.z waveQ
  ux = C3.x uP
  uy = C3.y uP
  uz = C3.z uP
  vx = C3.x uQ
  vy = C3.y uQ
  vz = C3.z uQ

  xProof :
    C3.x (rotationalPair waveP waveQ uP uQ)
    ≡ C3.x
      (C3.complex3Scale i
        (C3.complex3Subtract
          (convectivePair waveP waveQ uP uQ)
          (gradientPair waveP waveQ uP uQ)))
  xProof =
    R.solve 13
      (λ i px py pz qx qy qz ux uy uz vx vy vz →
        (((i R.⊗ ((pz R.⊗ ux) R.⊕ (R.⊝ (px R.⊗ uz)))) R.⊗ vz)
          R.⊕ (R.⊝ ((i R.⊗ ((px R.⊗ uy) R.⊕ (R.⊝ (py R.⊗ ux)))) R.⊗ vy))
          R.⊕ ((i R.⊗ ((qz R.⊗ vx) R.⊕ (R.⊝ (qx R.⊗ vz)))) R.⊗ uz)
          R.⊕ (R.⊝ ((i R.⊗ ((qx R.⊗ vy) R.⊕ (R.⊝ (qy R.⊗ vx)))) R.⊗ uy)))
        R.⊜
        (i R.⊗
          (((ux R.⊗ qx) R.⊕ (uy R.⊗ qy) R.⊕ (uz R.⊗ qz)) R.⊗ vx
            R.⊕ (((vx R.⊗ px) R.⊕ (vy R.⊗ py) R.⊕ (vz R.⊗ pz)) R.⊗ ux)
            R.⊕ (R.⊝
              (((ux R.⊗ vx) R.⊕ (uy R.⊗ vy) R.⊕ (uz R.⊗ vz))
                R.⊗ (px R.⊕ qx))))))
      refl i px py pz qx qy qz ux uy uz vx vy vz

  yProof :
    C3.y (rotationalPair waveP waveQ uP uQ)
    ≡ C3.y
      (C3.complex3Scale i
        (C3.complex3Subtract
          (convectivePair waveP waveQ uP uQ)
          (gradientPair waveP waveQ uP uQ)))
  yProof =
    R.solve 13
      (λ i px py pz qx qy qz ux uy uz vx vy vz →
        (((i R.⊗ ((px R.⊗ uy) R.⊕ (R.⊝ (py R.⊗ ux)))) R.⊗ vx)
          R.⊕ (R.⊝ ((i R.⊗ ((py R.⊗ uz) R.⊕ (R.⊝ (pz R.⊗ uy)))) R.⊗ vz))
          R.⊕ ((i R.⊗ ((qx R.⊗ vy) R.⊕ (R.⊝ (qy R.⊗ vx)))) R.⊗ ux)
          R.⊕ (R.⊝ ((i R.⊗ ((qy R.⊗ vz) R.⊕ (R.⊝ (qz R.⊗ vy)))) R.⊗ uz)))
        R.⊜
        (i R.⊗
          (((ux R.⊗ qx) R.⊕ (uy R.⊗ qy) R.⊕ (uz R.⊗ qz)) R.⊗ vy
            R.⊕ (((vx R.⊗ px) R.⊕ (vy R.⊗ py) R.⊕ (vz R.⊗ pz)) R.⊗ uy)
            R.⊕ (R.⊝
              (((ux R.⊗ vx) R.⊕ (uy R.⊗ vy) R.⊕ (uz R.⊗ vz))
                R.⊗ (py R.⊕ qy))))))
      refl i px py pz qx qy qz ux uy uz vx vy vz

  zProof :
    C3.z (rotationalPair waveP waveQ uP uQ)
    ≡ C3.z
      (C3.complex3Scale i
        (C3.complex3Subtract
          (convectivePair waveP waveQ uP uQ)
          (gradientPair waveP waveQ uP uQ)))
  zProof =
    R.solve 13
      (λ i px py pz qx qy qz ux uy uz vx vy vz →
        (((i R.⊗ ((py R.⊗ uz) R.⊕ (R.⊝ (pz R.⊗ uy)))) R.⊗ vy)
          R.⊕ (R.⊝ ((i R.⊗ ((pz R.⊗ ux) R.⊕ (R.⊝ (px R.⊗ uz)))) R.⊗ vx))
          R.⊕ ((i R.⊗ ((qy R.⊗ vz) R.⊕ (R.⊝ (qz R.⊗ vy)))) R.⊗ uy)
          R.⊕ (R.⊝ ((i R.⊗ ((qz R.⊗ vx) R.⊕ (R.⊝ (qx R.⊗ vz)))) R.⊗ ux)))
        R.⊜
        (i R.⊗
          (((ux R.⊗ qx) R.⊕ (uy R.⊗ qy) R.⊕ (uz R.⊗ qz)) R.⊗ vz
            R.⊕ (((vx R.⊗ px) R.⊕ (vy R.⊗ py) R.⊕ (vz R.⊗ pz)) R.⊗ uz)
            R.⊕ (R.⊝
              (((ux R.⊗ vx) R.⊕ (uy R.⊗ vy) R.⊕ (uz R.⊗ vz))
                R.⊗ (pz R.⊕ qz))))))
      refl i px py pz qx qy qz ux uy uz vx vy vz

resonantGradientIsOutputLongitudinal :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    {p q k : Z3.FourierMode}
    (resonance : Z3.Resonance p q k)
    (uP uQ : C3.Complex3 F) →
  gradientPair (C3.modeVector E p) (C3.modeVector E q) uP uQ
  ≡
  C3.complex3Scale
    (C3.bilinearDot3 uP uQ)
    (C3.modeVector E k)
resonantGradientIsOutputLongitudinal E {p} {q} {k} resonance uP uQ =
  cong
    (C3.complex3Scale (C3.bilinearDot3 uP uQ))
    (trans
      (sym (Algebra.modeVectorAdd E p q))
      (cong (C3.modeVector E) (Z3.Resonance.closes resonance)))

transverseTestKillsResonantGradient :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    {p q k : Z3.FourierMode}
    (resonance : Z3.Resonance p q k)
    (uP uQ testK : C3.Complex3 F) →
  Helical.Transverse E k testK →
  C3.hermitianPairing3 testK
    (gradientPair (C3.modeVector E p) (C3.modeVector E q) uP uQ)
  ≡ C3.complexZero F
transverseTestKillsResonantGradient {F = F} E {p} {q} {k}
  resonance uP uQ testK transverse =
  trans
    (cong (C3.hermitianPairing3 testK)
      (resonantGradientIsOutputLongitudinal E resonance uP uQ))
    (trans
      (Algebra.hermitianScaleRight
        testK (C3.modeVector E k) (C3.bilinearDot3 uP uQ))
      (trans
        (cong
          (C3.complexMultiply (C3.bilinearDot3 uP uQ))
          (trans
            (Algebra.modePairRight E k testK)
            (cong C3.complexConjugate transverse)))
        (Algebra.complexMultiplyZeroRight (C3.bilinearDot3 uP uQ))))

round93ConvectiveRotationalVectorIdentityClosed : Bool
round93ConvectiveRotationalVectorIdentityClosed = true

round93ResonantGradientKilledByTransverseOutput : Bool
round93ResonantGradientKilledByTransverseOutput = true

round93LiteralTestedWaleffeFactorizationClosed : Bool
round93LiteralTestedWaleffeFactorizationClosed = false

round93ConvectiveRotationalVectorIdentityClosedIsTrue :
  round93ConvectiveRotationalVectorIdentityClosed ≡ true
round93ConvectiveRotationalVectorIdentityClosedIsTrue = refl

round93ResonantGradientKilledByTransverseOutputIsTrue :
  round93ResonantGradientKilledByTransverseOutput ≡ true
round93ResonantGradientKilledByTransverseOutputIsTrue = refl

round93LiteralTestedWaleffeFactorizationClosedIsFalse :
  round93LiteralTestedWaleffeFactorizationClosed ≡ false
round93LiteralTestedWaleffeFactorizationClosedIsFalse = refl
