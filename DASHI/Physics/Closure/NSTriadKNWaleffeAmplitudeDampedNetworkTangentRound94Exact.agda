module DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: J. M. Manley; H. E. Rowe.
-- Title: "Some General Properties of Nonlinear Elements-Part I. General
-- Energy Relations".
-- Proceedings of the IRE 44(7) (1956), 904--913.
-- DOI: 10.1109/JRPROC.1956.275145.
--
-- Author: M. Hirota.
-- Title: "Lagrangian approach to resonant three-mode interaction in
-- magnetohydrodynamics".
-- 23rd IAEA Fusion Energy Conference, THS/P7-02 (2010).
-- DOI: no DOI recorded for the conference paper here.
--
-- ROUND94 / LITERAL DAMPED-FORCED TRIAD AMPLITUDE TANGENT
--
-- Round93 proved that one literal helical NS triad is controlled by the real
-- part of
--
--      Z(u_k,u_p,u_q) = <u_k , u_p x u_q>.
--
-- The isolated three-wave literature is useful because the same cubic phase
-- carrier drives all three modal exchanges, but the full NS network is NOT an
-- isolated triad.  This module therefore derives the exact product-rule
-- tangent on the literal Complex3 carrier and exposes the network forcing.
--
-- If each modal tangent is decomposed as
--
--      d u_j = - rho_j u_j + f_j,
--
-- with real rho_j, then
--
--   dZ = -(rho_k+rho_p+rho_q) Z
--        + <f_k,u_p x u_q>
--        + <u_k,f_p x u_q>
--        + <u_k,u_p x f_q>.
--
-- For the physical Galerkin ODE, rho_j is nu |j|^2 and f_j is the remainder
-- of the full nonlinear Fourier network.  Thus adverse helical-phase residence
-- is reduced to a damped-forced scalar problem.  No isolated-triad recurrence,
-- genericity, or statistical cascade theorem is imported.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross

crossAddLeft :
  ∀ {r} {F : C3.RealField r}
    (u v w : C3.Complex3 F) →
  Cross.complex3Cross (C3.complex3Add u v) w
  ≡ C3.complex3Add (Cross.complex3Cross u w) (Cross.complex3Cross v w)
crossAddLeft {F = F}
  (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) (C3.complex3 wx wy wz) =
  Algebra.complex3Ext
    (R.solve 6
      (λ uy uz vy vz wy wz →
        (((uy R.⊕ vy) R.⊗ wz) R.⊕ (R.⊝ ((uz R.⊕ vz) R.⊗ wy)))
        R.⊜
        ((uy R.⊗ wz) R.⊕ (R.⊝ (uz R.⊗ wy)))
          R.⊕ ((vy R.⊗ wz) R.⊕ (R.⊝ (vz R.⊗ wy))))
      refl uy uz vy vz wy wz)
    (R.solve 6
      (λ uz ux vz vx wz wx →
        (((uz R.⊕ vz) R.⊗ wx) R.⊕ (R.⊝ ((ux R.⊕ vx) R.⊗ wz)))
        R.⊜
        ((uz R.⊗ wx) R.⊕ (R.⊝ (ux R.⊗ wz)))
          R.⊕ ((vz R.⊗ wx) R.⊕ (R.⊝ (vx R.⊗ wz))))
      refl uz ux vz vx wz wx)
    (R.solve 6
      (λ ux uy vx vy wx wy →
        (((ux R.⊕ vx) R.⊗ wy) R.⊕ (R.⊝ ((uy R.⊕ vy) R.⊗ wx)))
        R.⊜
        ((ux R.⊗ wy) R.⊕ (R.⊝ (uy R.⊗ wx)))
          R.⊕ ((vx R.⊗ wy) R.⊕ (R.⊝ (vy R.⊗ wx))))
      refl ux uy vx vy wx wy)
  where module R = Ring.Solver F

crossAddRight :
  ∀ {r} {F : C3.RealField r}
    (u v w : C3.Complex3 F) →
  Cross.complex3Cross u (C3.complex3Add v w)
  ≡ C3.complex3Add (Cross.complex3Cross u v) (Cross.complex3Cross u w)
crossAddRight {F = F}
  (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) (C3.complex3 wx wy wz) =
  Algebra.complex3Ext
    (R.solve 6
      (λ uy uz vy vz wy wz →
        (uy R.⊗ (vz R.⊕ wz)) R.⊕ (R.⊝ (uz R.⊗ (vy R.⊕ wy)))
        R.⊜
        ((uy R.⊗ vz) R.⊕ (R.⊝ (uz R.⊗ vy)))
          R.⊕ ((uy R.⊗ wz) R.⊕ (R.⊝ (uz R.⊗ wy))))
      refl uy uz vy vz wy wz)
    (R.solve 6
      (λ uz ux vz vx wz wx →
        (uz R.⊗ (vx R.⊕ wx)) R.⊕ (R.⊝ (ux R.⊗ (vz R.⊕ wz)))
        R.⊜
        ((uz R.⊗ vx) R.⊕ (R.⊝ (ux R.⊗ vz)))
          R.⊕ ((uz R.⊗ wx) R.⊕ (R.⊝ (ux R.⊗ wz))))
      refl uz ux vz vx wz wx)
    (R.solve 6
      (λ ux uy vx vy wx wy →
        (ux R.⊗ (vy R.⊕ wy)) R.⊕ (R.⊝ (uy R.⊗ (vx R.⊕ wx)))
        R.⊜
        ((ux R.⊗ vy) R.⊕ (R.⊝ (uy R.⊗ vx)))
          R.⊕ ((ux R.⊗ wy) R.⊕ (R.⊝ (uy R.⊗ wx))))
      refl ux uy vx vy wx wy)
  where module R = Ring.Solver F

crossScaleLeft :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F) (u v : C3.Complex3 F) →
  Cross.complex3Cross (C3.complex3Scale scalar u) v
  ≡ C3.complex3Scale scalar (Cross.complex3Cross u v)
crossScaleLeft {F = F} scalar
  (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) =
  Algebra.complex3Ext
    (R.solve 5
      (λ s uy uz vy vz →
        ((s R.⊗ uy) R.⊗ vz) R.⊕ (R.⊝ ((s R.⊗ uz) R.⊗ vy))
        R.⊜ s R.⊗ ((uy R.⊗ vz) R.⊕ (R.⊝ (uz R.⊗ vy))))
      refl scalar uy uz vy vz)
    (R.solve 5
      (λ s uz ux vz vx →
        ((s R.⊗ uz) R.⊗ vx) R.⊕ (R.⊝ ((s R.⊗ ux) R.⊗ vz))
        R.⊜ s R.⊗ ((uz R.⊗ vx) R.⊕ (R.⊝ (ux R.⊗ vz))))
      refl scalar uz ux vz vx)
    (R.solve 5
      (λ s ux uy vx vy →
        ((s R.⊗ ux) R.⊗ vy) R.⊕ (R.⊝ ((s R.⊗ uy) R.⊗ vx))
        R.⊜ s R.⊗ ((ux R.⊗ vy) R.⊕ (R.⊝ (uy R.⊗ vx))))
      refl scalar ux uy vx vy)
  where module R = Ring.Solver F

crossScaleRight :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F) (u v : C3.Complex3 F) →
  Cross.complex3Cross u (C3.complex3Scale scalar v)
  ≡ C3.complex3Scale scalar (Cross.complex3Cross u v)
crossScaleRight {F = F} scalar
  (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) =
  Algebra.complex3Ext
    (R.solve 5
      (λ s uy uz vy vz →
        (uy R.⊗ (s R.⊗ vz)) R.⊕ (R.⊝ (uz R.⊗ (s R.⊗ vy)))
        R.⊜ s R.⊗ ((uy R.⊗ vz) R.⊕ (R.⊝ (uz R.⊗ vy))))
      refl scalar uy uz vy vz)
    (R.solve 5
      (λ s uz ux vz vx →
        (uz R.⊗ (s R.⊗ vx)) R.⊕ (R.⊝ (ux R.⊗ (s R.⊗ vz)))
        R.⊜ s R.⊗ ((uz R.⊗ vx) R.⊕ (R.⊝ (ux R.⊗ vz))))
      refl scalar uz ux vz vx)
    (R.solve 5
      (λ s ux uy vx vy →
        (ux R.⊗ (s R.⊗ vy)) R.⊕ (R.⊝ (uy R.⊗ (s R.⊗ vx)))
        R.⊜ s R.⊗ ((ux R.⊗ vy) R.⊕ (R.⊝ (uy R.⊗ vx))))
      refl scalar ux uy vx vy)
  where module R = Ring.Solver F

complexAmplitude :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
complexAmplitude uK uP uQ =
  C3.hermitianPairing3 uK (Cross.complex3Cross uP uQ)

amplitudeTangent :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
amplitudeTangent uK uP uQ dK dP dQ =
  C3.complexAdd
    (C3.complexAdd
      (C3.hermitianPairing3 dK (Cross.complex3Cross uP uQ))
      (C3.hermitianPairing3 uK (Cross.complex3Cross dP uQ)))
    (C3.hermitianPairing3 uK (Cross.complex3Cross uP dQ))

networkForcing :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
networkForcing = amplitudeTangent

negativeReal :
  ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Complex F
negativeReal {F = F} rho = C3.realEmbed F (C3.negate F rho)

dampedPlusForcing :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
dampedPlusForcing rho u f =
  C3.complex3Add (C3.complex3Scale (negativeReal rho) u) f

totalNegativeDecay :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Complex F
totalNegativeDecay {F = F} rhoK rhoP rhoQ =
  C3.complexAdd
    (C3.complexAdd (negativeReal rhoK) (negativeReal rhoP))
    (negativeReal rhoQ)

negativeRealConjugate :
  ∀ {r} {F : C3.RealField r} (rho : C3.Carrier F) →
  C3.complexConjugate (negativeReal rho) ≡ negativeReal rho
negativeRealConjugate {F = F} rho = C3.realEmbedConjugate F (C3.negate F rho)

amplitudeTangentDampedNetwork :
  ∀ {r} {F : C3.RealField r}
    (rhoK rhoP rhoQ : C3.Carrier F)
    (uK uP uQ fK fP fQ : C3.Complex3 F) →
  amplitudeTangent uK uP uQ
    (dampedPlusForcing rhoK uK fK)
    (dampedPlusForcing rhoP uP fP)
    (dampedPlusForcing rhoQ uQ fQ)
  ≡
  C3.complexAdd
    (C3.complexMultiply
      (totalNegativeDecay rhoK rhoP rhoQ)
      (complexAmplitude uK uP uQ))
    (networkForcing uK uP uQ fK fP fQ)
amplitudeTangentDampedNetwork {F = F}
  rhoK rhoP rhoQ uK uP uQ fK fP fQ =
  trans expanded regrouped
  where
  AK = complexAmplitude uK uP uQ
  sK = negativeReal rhoK
  sP = negativeReal rhoP
  sQ = negativeReal rhoQ

  firstSlot :
    C3.hermitianPairing3 (dampedPlusForcing rhoK uK fK)
      (Cross.complex3Cross uP uQ)
    ≡ C3.complexAdd
        (C3.complexMultiply sK AK)
        (C3.hermitianPairing3 fK (Cross.complex3Cross uP uQ))
  firstSlot =
    trans
      (Additive.hermitianPairingAddLeft
        (C3.complex3Scale sK uK) fK (Cross.complex3Cross uP uQ))
      (cong
        (λ head → C3.complexAdd head
          (C3.hermitianPairing3 fK (Cross.complex3Cross uP uQ)))
        (trans
          (Scaling.hermitianPairingScaleLeft sK uK (Cross.complex3Cross uP uQ))
          (cong
            (λ scalar → C3.complexMultiply scalar AK)
            (negativeRealConjugate rhoK))))

  secondSlot :
    C3.hermitianPairing3 uK
      (Cross.complex3Cross (dampedPlusForcing rhoP uP fP) uQ)
    ≡ C3.complexAdd
        (C3.complexMultiply sP AK)
        (C3.hermitianPairing3 uK (Cross.complex3Cross fP uQ))
  secondSlot =
    trans
      (cong (C3.hermitianPairing3 uK)
        (trans
          (crossAddLeft (C3.complex3Scale sP uP) fP uQ)
          (cong
            (λ head → C3.complex3Add head (Cross.complex3Cross fP uQ))
            (crossScaleLeft sP uP uQ))))
      (trans
        (Additive.hermitianPairingAddRight uK
          (C3.complex3Scale sP (Cross.complex3Cross uP uQ))
          (Cross.complex3Cross fP uQ))
        (cong
          (λ head → C3.complexAdd head
            (C3.hermitianPairing3 uK (Cross.complex3Cross fP uQ)))
          (Scaling.hermitianPairingScaleRight
            sP uK (Cross.complex3Cross uP uQ))))

  thirdSlot :
    C3.hermitianPairing3 uK
      (Cross.complex3Cross uP (dampedPlusForcing rhoQ uQ fQ))
    ≡ C3.complexAdd
        (C3.complexMultiply sQ AK)
        (C3.hermitianPairing3 uK (Cross.complex3Cross uP fQ))
  thirdSlot =
    trans
      (cong (C3.hermitianPairing3 uK)
        (trans
          (crossAddRight uP (C3.complex3Scale sQ uQ) fQ)
          (cong
            (λ head → C3.complex3Add head (Cross.complex3Cross uP fQ))
            (crossScaleRight sQ uP uQ))))
      (trans
        (Additive.hermitianPairingAddRight uK
          (C3.complex3Scale sQ (Cross.complex3Cross uP uQ))
          (Cross.complex3Cross uP fQ))
        (cong
          (λ head → C3.complexAdd head
            (C3.hermitianPairing3 uK (Cross.complex3Cross uP fQ)))
          (Scaling.hermitianPairingScaleRight
            sQ uK (Cross.complex3Cross uP uQ))))

  expanded :
    amplitudeTangent uK uP uQ
      (dampedPlusForcing rhoK uK fK)
      (dampedPlusForcing rhoP uP fP)
      (dampedPlusForcing rhoQ uQ fQ)
    ≡
    C3.complexAdd
      (C3.complexAdd
        (C3.complexAdd (C3.complexMultiply sK AK)
          (C3.hermitianPairing3 fK (Cross.complex3Cross uP uQ)))
        (C3.complexAdd (C3.complexMultiply sP AK)
          (C3.hermitianPairing3 uK (Cross.complex3Cross fP uQ))))
      (C3.complexAdd (C3.complexMultiply sQ AK)
        (C3.hermitianPairing3 uK (Cross.complex3Cross uP fQ)))
  expanded = cong₂ C3.complexAdd (cong₂ C3.complexAdd firstSlot secondSlot) thirdSlot

  regrouped :
    C3.complexAdd
      (C3.complexAdd
        (C3.complexAdd (C3.complexMultiply sK AK)
          (C3.hermitianPairing3 fK (Cross.complex3Cross uP uQ)))
        (C3.complexAdd (C3.complexMultiply sP AK)
          (C3.hermitianPairing3 uK (Cross.complex3Cross fP uQ))))
      (C3.complexAdd (C3.complexMultiply sQ AK)
        (C3.hermitianPairing3 uK (Cross.complex3Cross uP fQ)))
    ≡
    C3.complexAdd
      (C3.complexMultiply (totalNegativeDecay rhoK rhoP rhoQ) AK)
      (networkForcing uK uP uQ fK fP fQ)
  regrouped =
    R.solve 7
      (λ sK sP sQ A FK FP FQ →
        (((sK R.⊗ A) R.⊕ FK) R.⊕ ((sP R.⊗ A) R.⊕ FP))
          R.⊕ ((sQ R.⊗ A) R.⊕ FQ)
        R.⊜
        (((sK R.⊕ sP) R.⊕ sQ) R.⊗ A)
          R.⊕ (FK R.⊕ FP R.⊕ FQ))
      refl sK sP sQ AK
        (C3.hermitianPairing3 fK (Cross.complex3Cross uP uQ))
        (C3.hermitianPairing3 uK (Cross.complex3Cross fP uQ))
        (C3.hermitianPairing3 uK (Cross.complex3Cross uP fQ))
    where module R = Ring.Solver F

realAmplitudeTangentDampedNetwork :
  ∀ {r} {F : C3.RealField r}
    (rhoK rhoP rhoQ : C3.Carrier F)
    (uK uP uQ fK fP fQ : C3.Complex3 F) →
  C3.complexRealPart
    (amplitudeTangent uK uP uQ
      (dampedPlusForcing rhoK uK fK)
      (dampedPlusForcing rhoP uP fP)
      (dampedPlusForcing rhoQ uQ fQ))
  ≡
  C3.complexRealPart
    (C3.complexAdd
      (C3.complexMultiply
        (totalNegativeDecay rhoK rhoP rhoQ)
        (complexAmplitude uK uP uQ))
      (networkForcing uK uP uQ fK fP fQ))
realAmplitudeTangentDampedNetwork rhoK rhoP rhoQ uK uP uQ fK fP fQ =
  cong C3.complexRealPart
    (amplitudeTangentDampedNetwork rhoK rhoP rhoQ uK uP uQ fK fP fQ)

round94LiteralWaleffeAmplitudeDampedNetworkTangentClosed : Bool
round94LiteralWaleffeAmplitudeDampedNetworkTangentClosed = true

round94PhysicalGalerkinForcingIdentificationClosed : Bool
round94PhysicalGalerkinForcingIdentificationClosed = false

round94AdversePhaseResidenceBoundClosed : Bool
round94AdversePhaseResidenceBoundClosed = false

round94LiteralWaleffeAmplitudeDampedNetworkTangentClosedIsTrue :
  round94LiteralWaleffeAmplitudeDampedNetworkTangentClosed ≡ true
round94LiteralWaleffeAmplitudeDampedNetworkTangentClosedIsTrue = refl

round94PhysicalGalerkinForcingIdentificationClosedIsFalse :
  round94PhysicalGalerkinForcingIdentificationClosed ≡ false
round94PhysicalGalerkinForcingIdentificationClosedIsFalse = refl

round94AdversePhaseResidenceBoundClosedIsFalse :
  round94AdversePhaseResidenceBoundClosed ≡ false
round94AdversePhaseResidenceBoundClosedIsFalse = refl
