module DASHI.Physics.Closure.NSTriadKNLuoGalerkinFourierVorticityConvolutionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- This module derives the literal finite Fourier coefficient of the vorticity
-- nonlinearity.  For transverse nonzero modes p and r, the real carrier of the
-- Biot--Savart velocity is
--
--   u_p = |p|^-2 (p cross omega_p).
--
-- The ordered interaction contributing at output k=p+r is
--
--   F(p,r)
--     = (omega_p dot r) u_r
--       - (u_p dot r) omega_r.
--
-- The convolution sum contains both ordered pairs.  This module proves exactly
-- that the symmetrized coefficient
--
--   F(p,r) + F(r,p)
--
-- is transverse to p+r.  The cancellation uses only transversality of each
-- vorticity and velocity mode and dot-product commutativity.  Thus the finite
-- Galerkin curl equation is now connected to the repository's physical
-- Fourier-mode carrier rather than represented only by anonymous sources.
--
-- The common complex phase i is factored out.  Full finite mode enumeration,
-- reality pairing, dyadic support classification and critical source estimates
-- remain separate tasks.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (_≡_; cong; trans)

import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalDirectionalDefectExact as Physical
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicBiotSavartMultiplierExact as Biot

addVec : Gram.Vec3 → Gram.Vec3 → Gram.Vec3
addVec left right =
  Gram.vec3
    (Gram.x left + Gram.x right)
    (Gram.y left + Gram.y right)
    (Gram.z left + Gram.z right)

subtractVec : Gram.Vec3 → Gram.Vec3 → Gram.Vec3
subtractVec left right =
  Gram.vec3
    (Gram.x left - Gram.x right)
    (Gram.y left - Gram.y right)
    (Gram.z left - Gram.z right)

scaleVec : ℚ → Gram.Vec3 → Gram.Vec3
scaleVec = Physical.scaleVec3

velocityCarrier : Biot.NonzeroVorticityMode → Gram.Vec3
velocityCarrier mode =
  scaleVec
    (Biot.inverseRadiusSquared mode)
    (Biot.curlNumerator mode)

dotScaleRight :
  ∀ left scalar right →
  Gram.dot left (scaleVec scalar right)
  ≡ scalar * Gram.dot left right
dotScaleRight left scalar right =
  solve
    ( Gram.x left ∷ Gram.y left ∷ Gram.z left
    ∷ scalar
    ∷ Gram.x right ∷ Gram.y right ∷ Gram.z right
    ∷ [])

velocityTransverse :
  ∀ mode →
  Gram.dot (Biot.wavevector mode) (velocityCarrier mode) ≡ 0ℚ
velocityTransverse mode =
  trans
    (dotScaleRight
      (Biot.wavevector mode)
      (Biot.inverseRadiusSquared mode)
      (Biot.curlNumerator mode))
    (trans
      (cong
        (λ value → Biot.inverseRadiusSquared mode * value)
        (Biot.waveDotCurlNumeratorZero mode))
      (solve (Biot.inverseRadiusSquared mode ∷ [])))

orderedVorticityInteraction :
  Biot.NonzeroVorticityMode →
  Biot.NonzeroVorticityMode →
  Gram.Vec3
orderedVorticityInteraction left right =
  subtractVec
    (scaleVec
      (Gram.dot (Biot.vorticity left) (Biot.wavevector right))
      (velocityCarrier right))
    (scaleVec
      (Gram.dot (velocityCarrier left) (Biot.wavevector right))
      (Biot.vorticity right))

symmetrizedVorticityInteraction :
  Biot.NonzeroVorticityMode →
  Biot.NonzeroVorticityMode →
  Gram.Vec3
symmetrizedVorticityInteraction left right =
  addVec
    (orderedVorticityInteraction left right)
    (orderedVorticityInteraction right left)

outputWavevector :
  Biot.NonzeroVorticityMode →
  Biot.NonzeroVorticityMode →
  Gram.Vec3
outputWavevector left right =
  addVec (Biot.wavevector left) (Biot.wavevector right)

outputDotSymmetrizedExpansion :
  ∀ left right →
  Gram.dot
    (outputWavevector left right)
    (symmetrizedVorticityInteraction left right)
  ≡
  Gram.dot (Biot.vorticity left) (Biot.wavevector right)
    * ( Gram.dot (Biot.wavevector left) (velocityCarrier right)
      + Gram.dot (Biot.wavevector right) (velocityCarrier right) )
  -
  Gram.dot (velocityCarrier left) (Biot.wavevector right)
    * ( Gram.dot (Biot.wavevector left) (Biot.vorticity right)
      + Gram.dot (Biot.wavevector right) (Biot.vorticity right) )
  +
  Gram.dot (Biot.vorticity right) (Biot.wavevector left)
    * ( Gram.dot (Biot.wavevector left) (velocityCarrier left)
      + Gram.dot (Biot.wavevector right) (velocityCarrier left) )
  -
  Gram.dot (velocityCarrier right) (Biot.wavevector left)
    * ( Gram.dot (Biot.wavevector left) (Biot.vorticity left)
      + Gram.dot (Biot.wavevector right) (Biot.vorticity left) )
outputDotSymmetrizedExpansion left right =
  solve
    ( Gram.x (Biot.wavevector left)
    ∷ Gram.y (Biot.wavevector left)
    ∷ Gram.z (Biot.wavevector left)
    ∷ Gram.x (Biot.wavevector right)
    ∷ Gram.y (Biot.wavevector right)
    ∷ Gram.z (Biot.wavevector right)
    ∷ Gram.x (Biot.vorticity left)
    ∷ Gram.y (Biot.vorticity left)
    ∷ Gram.z (Biot.vorticity left)
    ∷ Gram.x (Biot.vorticity right)
    ∷ Gram.y (Biot.vorticity right)
    ∷ Gram.z (Biot.vorticity right)
    ∷ Gram.x (velocityCarrier left)
    ∷ Gram.y (velocityCarrier left)
    ∷ Gram.z (velocityCarrier left)
    ∷ Gram.x (velocityCarrier right)
    ∷ Gram.y (velocityCarrier right)
    ∷ Gram.z (velocityCarrier right)
    ∷ [])

symmetrizedVorticityInteractionTransverse :
  ∀ left right →
  Gram.dot
    (outputWavevector left right)
    (symmetrizedVorticityInteraction left right)
  ≡ 0ℚ
symmetrizedVorticityInteractionTransverse left right
  rewrite outputDotSymmetrizedExpansion left right
        | velocityTransverse left
        | velocityTransverse right
        | Biot.transverseVorticity left
        | Biot.transverseVorticity right =
  solve
    ( Gram.dot (Biot.vorticity left) (Biot.wavevector right)
    ∷ Gram.dot (Biot.vorticity right) (Biot.wavevector left)
    ∷ Gram.dot (velocityCarrier left) (Biot.wavevector right)
    ∷ Gram.dot (velocityCarrier right) (Biot.wavevector left)
    ∷ Gram.dot (Biot.wavevector left) (Biot.vorticity right)
    ∷ Gram.dot (Biot.wavevector right) (Biot.vorticity left)
    ∷ Gram.dot (Biot.wavevector left) (velocityCarrier right)
    ∷ Gram.dot (Biot.wavevector right) (velocityCarrier left)
    ∷ [])

record FourierConvolutionAuthorityBoundary : Set where
  constructor fourierConvolutionAuthorityBoundary
  field
    BiotSavartVelocityCarrierConstructed : Set
    orderedStretchMinusTransportCoefficientConstructed : Set
    symmetrizedOutputTransversalityProved : Set
    commonComplexPhaseRestored : Set
    finiteGalerkinModeEnumerationConstructed : Set
    dyadicSupportClassificationConnected : Set
    criticalFiveSourceBoundsProduced : Set

canonicalFourierConvolutionAuthorityBoundary :
  FourierConvolutionAuthorityBoundary
canonicalFourierConvolutionAuthorityBoundary =
  fourierConvolutionAuthorityBoundary ⊤ ⊤ ⊤ ⊥ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
