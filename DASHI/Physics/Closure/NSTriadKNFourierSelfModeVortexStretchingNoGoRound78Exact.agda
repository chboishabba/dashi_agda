module DASHI.Physics.Closure.NSTriadKNFourierSelfModeVortexStretchingNoGoRound78Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Thomas Y. Hou; Ruo Li.
-- Title: "Dynamic Depletion of Vortex Stretching and Non-Blowup of the 3-D
-- Incompressible Euler Equations".
-- DOI: 10.1007/s00332-006-0800-3.
--
-- Author: Thomas Y. Hou.
-- Title: "Blow-up or no blow-up? A unified computational and analytic
-- approach to 3D incompressible Euler and Navier-Stokes equations".
-- DOI: 10.1017/S0962492906420018.
--
-- ROUND78 / EXACT SELF-MODE NO-GO
--
-- The repository already proved the exact nonzero Fourier strain multiplier
--
--   S_k(source)
--
-- and the geometric factorization
--
--   target . S_k(source) target
--     = - |k|^-2 (k.target) k.(source x target).
--
-- Setting source=target=omega makes the cross product omega x omega vanish.
-- Therefore ONE Fourier vorticity mode cannot stretch itself through its own
-- strain mode:
--
--   omega . S_k(omega) omega = 0.
--
-- This is a source-native obstruction to interpreting restricted-Euler local
-- self-amplification as the missing Round77 B2 gain on a single Fourier child.
-- Any positive physical B2 surplus on this carrier must involve cross-mode
-- strain / nonlocal interaction (or a different already-declared physical
-- sector), not same-mode multiplicity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (0ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact as BS
import DASHI.Physics.Closure.NSTriadKNFourierStrainMultiplierRound38Exact as Strain

crossSelfZero : (omega : V.Vector3) → BS.cross omega omega ≡ V.v3 0ℚ 0ℚ 0ℚ
crossSelfZero (V.v3 wx wy wz) =
  V.vectorExt
    (solve (wx ∷ wy ∷ wz ∷ []))
    (solve (wx ∷ wy ∷ wz ∷ []))
    (solve (wx ∷ wy ∷ wz ∷ []))

dotModeCrossSelfZero :
  (mode omega : V.Vector3) →
  V.dot mode (BS.cross omega omega) ≡ 0ℚ
dotModeCrossSelfZero mode omega =
  trans
    (cong (V.dot mode) (crossSelfZero omega))
    (case mode of λ where
      (V.v3 kx ky kz) → solve (kx ∷ ky ∷ kz ∷ []))

fourierSelfModeStretchingVanishes :
  (modeData : V.ProjectionMode) →
  (omega : V.Vector3) →
  Strain.fourierStretchingScalar modeData omega omega ≡ 0ℚ
fourierSelfModeStretchingVanishes modeData omega =
  trans
    (Strain.fourierStretchingMisalignmentExact modeData omega omega)
    (trans
      (cong
        (λ crossPairing →
          (- V.inverseNormSquared modeData)
            * V.dot (V.mode modeData) omega
            * crossPairing)
        (dotModeCrossSelfZero (V.mode modeData) omega))
      (solve
        ( V.inverseNormSquared modeData
        ∷ V.dot (V.mode modeData) omega
        ∷ [])))

round78SameFourierModeCanSelfStretch : Bool
round78SameFourierModeCanSelfStretch = false

round78PositiveB2GainMustUseCrossModeOrNonlocalInteraction : Bool
round78PositiveB2GainMustUseCrossModeOrNonlocalInteraction = true

round78SameFourierModeCanSelfStretchIsFalse :
  round78SameFourierModeCanSelfStretch ≡ false
round78SameFourierModeCanSelfStretchIsFalse = refl

round78PositiveB2GainMustUseCrossModeOrNonlocalInteractionIsTrue :
  round78PositiveB2GainMustUseCrossModeOrNonlocalInteraction ≡ true
round78PositiveB2GainMustUseCrossModeOrNonlocalInteractionIsTrue = refl
