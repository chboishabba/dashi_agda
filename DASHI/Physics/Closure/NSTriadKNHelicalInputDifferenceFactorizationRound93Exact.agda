module DASHI.Physics.Closure.NSTriadKNHelicalInputDifferenceFactorizationRound93Exact where

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
-- ROUND93 / LITERAL INPUT-DIFFERENCE FACTORIZATION
--
-- The Waleffe signed-eigenvalue difference is already forced before any
-- statistical or shell argument.  If the two input Fourier modes satisfy
--
--      omega_p = a u_p,     omega_q = b u_q,
--
-- then their symmetrised rotational interaction obeys exactly
--
--      omega_p x u_q + omega_q x u_p
--        = (a-b) (u_p x u_q).
--
-- This is proved directly on the repository Complex3 carrier.  Therefore the
-- only remaining bridge from the literal convective coefficient to Waleffe's
-- common-amplitude form is the standard projected convective/rotational
-- identity plus testing the common cross product against the output helical
-- mode.  No sign/cascade conclusion is assumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross

symmetrisedRotationalInteraction :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F
symmetrisedRotationalInteraction omegaP uQ omegaQ uP =
  C3.complex3Add
    (Cross.complex3Cross omegaP uQ)
    (Cross.complex3Cross omegaQ uP)

helicalInputDifferenceFactorization :
  ∀ {r} {F : C3.RealField r}
    (a b : C3.Complex F)
    (uP uQ : C3.Complex3 F) →
  symmetrisedRotationalInteraction
    (C3.complex3Scale a uP) uQ
    (C3.complex3Scale b uQ) uP
  ≡
  C3.complex3Scale
    (C3.complexSubtract a b)
    (Cross.complex3Cross uP uQ)
helicalInputDifferenceFactorization {F = F} a b uP uQ =
  Algebra.complex3Ext xProof yProof zProof
  where
  module R = Ring.Solver F

  xProof :
    C3.x
      (symmetrisedRotationalInteraction
        (C3.complex3Scale a uP) uQ
        (C3.complex3Scale b uQ) uP)
    ≡
    C3.x
      (C3.complex3Scale
        (C3.complexSubtract a b)
        (Cross.complex3Cross uP uQ))
  xProof =
    R.solve 6
      (λ a b py pz qy qz →
        (((a R.⊗ py) R.⊗ qz)
          R.⊕ (R.⊝ ((a R.⊗ pz) R.⊗ qy))
          R.⊕ ((b R.⊗ qy) R.⊗ pz)
          R.⊕ (R.⊝ ((b R.⊗ qz) R.⊗ py)))
        R.⊜
        ((a R.⊕ (R.⊝ b))
          R.⊗ ((py R.⊗ qz) R.⊕ (R.⊝ (pz R.⊗ qy)))))
      refl
      a b (C3.y uP) (C3.z uP) (C3.y uQ) (C3.z uQ)

  yProof :
    C3.y
      (symmetrisedRotationalInteraction
        (C3.complex3Scale a uP) uQ
        (C3.complex3Scale b uQ) uP)
    ≡
    C3.y
      (C3.complex3Scale
        (C3.complexSubtract a b)
        (Cross.complex3Cross uP uQ))
  yProof =
    R.solve 6
      (λ a b pz px qz qx →
        (((a R.⊗ pz) R.⊗ qx)
          R.⊕ (R.⊝ ((a R.⊗ px) R.⊗ qz))
          R.⊕ ((b R.⊗ qz) R.⊗ px)
          R.⊕ (R.⊝ ((b R.⊗ qx) R.⊗ pz)))
        R.⊜
        ((a R.⊕ (R.⊝ b))
          R.⊗ ((pz R.⊗ qx) R.⊕ (R.⊝ (px R.⊗ qz)))))
      refl
      a b (C3.z uP) (C3.x uP) (C3.z uQ) (C3.x uQ)

  zProof :
    C3.z
      (symmetrisedRotationalInteraction
        (C3.complex3Scale a uP) uQ
        (C3.complex3Scale b uQ) uP)
    ≡
    C3.z
      (C3.complex3Scale
        (C3.complexSubtract a b)
        (Cross.complex3Cross uP uQ))
  zProof =
    R.solve 6
      (λ a b px py qx qy →
        (((a R.⊗ px) R.⊗ qy)
          R.⊕ (R.⊝ ((a R.⊗ py) R.⊗ qx))
          R.⊕ ((b R.⊗ qx) R.⊗ py)
          R.⊕ (R.⊝ ((b R.⊗ qy) R.⊗ px)))
        R.⊜
        ((a R.⊕ (R.⊝ b))
          R.⊗ ((px R.⊗ qy) R.⊕ (R.⊝ (py R.⊗ qx)))))
      refl
      a b (C3.x uP) (C3.y uP) (C3.x uQ) (C3.y uQ)

record TwoInputHelicalModes
    {r} {F : C3.RealField r} : Set r where
  constructor two-input-helical-modes
  field
    uP uQ omegaP omegaQ : C3.Complex3 F
    signedEigenP signedEigenQ : C3.Complex F
    curlEigenP : omegaP ≡ C3.complex3Scale signedEigenP uP
    curlEigenQ : omegaQ ≡ C3.complex3Scale signedEigenQ uQ

open TwoInputHelicalModes public

literalHelicalRotationalFactorization :
  ∀ {r} {F : C3.RealField r}
    (H : TwoInputHelicalModes {F = F}) →
  symmetrisedRotationalInteraction
    (omegaP H) (uQ H) (omegaQ H) (uP H)
  ≡
  C3.complex3Scale
    (C3.complexSubtract (signedEigenP H) (signedEigenQ H))
    (Cross.complex3Cross (uP H) (uQ H))
literalHelicalRotationalFactorization H =
  trans
    (cong
      (λ pair →
        symmetrisedRotationalInteraction
          (C3.x pair) (uQ H) (C3.y pair) (uP H))
      pairMeaning)
    (helicalInputDifferenceFactorization
      (signedEigenP H) (signedEigenQ H) (uP H) (uQ H))
  where
  pairMeaning :
    C3.complex3 (omegaP H) (omegaQ H) (omegaP H)
    ≡
    C3.complex3
      (C3.complex3Scale (signedEigenP H) (uP H))
      (C3.complex3Scale (signedEigenQ H) (uQ H))
      (omegaP H)
  pairMeaning
    rewrite curlEigenP H | curlEigenQ H = refl

round93HelicalInputDifferenceFactorizationClosed : Bool
round93HelicalInputDifferenceFactorizationClosed = true

round93ProjectedConvectiveEqualsRotationalOnLiteralTriad : Bool
round93ProjectedConvectiveEqualsRotationalOnLiteralTriad = false

round93HelicalInputDifferenceFactorizationClosedIsTrue :
  round93HelicalInputDifferenceFactorizationClosed ≡ true
round93HelicalInputDifferenceFactorizationClosedIsTrue = refl

round93ProjectedConvectiveEqualsRotationalOnLiteralTriadIsFalse :
  round93ProjectedConvectiveEqualsRotationalOnLiteralTriad ≡ false
round93ProjectedConvectiveEqualsRotationalOnLiteralTriadIsFalse = refl
