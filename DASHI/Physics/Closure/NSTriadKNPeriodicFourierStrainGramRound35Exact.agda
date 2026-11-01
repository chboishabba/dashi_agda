module DASHI.Physics.Closure.NSTriadKNPeriodicFourierStrainGramRound35Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- Indiana University Mathematics Journal 42 (1993), 775--789.
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Peter Constantin; Charles Fefferman; Andrew J. Majda.
-- Title: "Geometric Constraints on Potentially Singular Solutions for the
-- 3-D Euler Equations".
-- Communications in Partial Differential Equations 21 (1996), 559--571.
-- DOI: 10.1080/03605309608821197.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Polarize the exact Round-34 Fourier strain identity instead of treating it
-- merely as an L2 bound.  For two mode fibres k,l, with
--
--   a = k cross omega,  b = l cross eta,
--
-- the Frobenius Gram kernel is proved exactly:
--
--   <S_k omega , S_l eta>_F
--     = (1/2)|k|^-2 |l|^-2
--       [ (k.l)(a.b) + (k.b)(a.l) ].
--
-- On one transverse fibre this collapses to
--
--   <S_k omega , S_k eta>_F = (1/2)(omega.eta),
--
-- hence, without introducing sqrt(2),
--
--   2 <S_k omega , S_k eta>_F = omega.eta.
--
-- This is the exact rational partial-isometry statement implicit in Round 34.
-- It also exposes the cross-fibre interference terms that must be controlled
-- by angular/coherence information in a physical HH-good estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; trans)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierBiotSavartExact as BS
import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as Matrix
import DASHI.Physics.Closure.NSTriadKNPeriodicFourierStrainMultiplierRound34Exact as Strain

frobeniusInner : Matrix.Matrix3 → Matrix.Matrix3 → ℚ
frobeniusInner left right =
  Matrix.m11 left * Matrix.m11 right
  + Matrix.m12 left * Matrix.m12 right
  + Matrix.m13 left * Matrix.m13 right
  + Matrix.m21 left * Matrix.m21 right
  + Matrix.m22 left * Matrix.m22 right
  + Matrix.m23 left * Matrix.m23 right
  + Matrix.m31 left * Matrix.m31 right
  + Matrix.m32 left * Matrix.m32 right
  + Matrix.m33 left * Matrix.m33 right

frobeniusInnerDiagonal :
  ∀ matrix →
  frobeniusInner matrix matrix ≡ Strain.frobeniusSquared matrix
frobeniusInnerDiagonal matrix = refl

crossMixedLagrange :
  (k omega eta : V.Vector3) →
  V.dot (BS.cross k omega) (BS.cross k eta)
  ≡ V.normSquared k * V.dot omega eta
    - V.dot k omega * V.dot k eta
crossMixedLagrange
    (V.v3 kx ky kz)
    (V.v3 wx wy wz)
    (V.v3 ex ey ez) =
  solve (kx ∷ ky ∷ kz ∷ wx ∷ wy ∷ wz ∷ ex ∷ ey ∷ ez ∷ [])

fourierStrainCrossFibreGramExact :
  ∀ leftMode rightMode omega eta →
  frobeniusInner
    (Strain.fourierStrain leftMode omega)
    (Strain.fourierStrain rightMode eta)
  ≡ Strain.half
      * V.inverseNormSquared leftMode
      * V.inverseNormSquared rightMode
      * ( V.dot (V.mode leftMode) (V.mode rightMode)
            * V.dot
                (BS.cross (V.mode leftMode) omega)
                (BS.cross (V.mode rightMode) eta)
        + V.dot
            (V.mode leftMode)
            (BS.cross (V.mode rightMode) eta)
            * V.dot
                (BS.cross (V.mode leftMode) omega)
                (V.mode rightMode))
fourierStrainCrossFibreGramExact leftMode rightMode omega eta
  with V.mode leftMode
     | V.mode rightMode
     | BS.cross (V.mode leftMode) omega
     | BS.cross (V.mode rightMode) eta
... | V.v3 kx ky kz
    | V.v3 lx ly lz
    | V.v3 ax ay az
    | V.v3 bx by bz =
  solve
    ( kx ∷ ky ∷ kz
    ∷ lx ∷ ly ∷ lz
    ∷ ax ∷ ay ∷ az
    ∷ bx ∷ by ∷ bz
    ∷ V.inverseNormSquared leftMode
    ∷ V.inverseNormSquared rightMode
    ∷ [])

fourierStrainSameFibreCrossExact :
  ∀ modeData omega eta →
  frobeniusInner
    (Strain.fourierStrain modeData omega)
    (Strain.fourierStrain modeData eta)
  ≡ Strain.half * V.inverseNormSquared modeData
      * V.dot
          (BS.cross (V.mode modeData) omega)
          (BS.cross (V.mode modeData) eta)
fourierStrainSameFibreCrossExact modeData omega eta =
  let
    inv = V.inverseNormSquared modeData
    k = V.mode modeData
    k2 = V.normSquared k
    a = BS.cross k omega
    b = BS.cross k eta
    ab = V.dot a b

    kbZero : V.dot k b ≡ 0ℚ
    kbZero = BS.crossOrthogonalLeft k eta

    akZero : V.dot a k ≡ 0ℚ
    akZero = trans (V.dotCommutative a k) (BS.crossOrthogonalLeft k omega)
  in
  begin
    frobeniusInner
      (Strain.fourierStrain modeData omega)
      (Strain.fourierStrain modeData eta)
  ≡⟨ fourierStrainCrossFibreGramExact
       modeData modeData omega eta ⟩
    Strain.half * inv * inv
      * (V.dot k k * ab + V.dot k b * V.dot a k)
  ≡⟨ cong
       (λ rightPair →
         Strain.half * inv * inv
           * (V.dot k k * ab + rightPair * V.dot a k))
       kbZero ⟩
    Strain.half * inv * inv
      * (V.dot k k * ab + 0ℚ * V.dot a k)
  ≡⟨ cong
       (λ leftPair →
         Strain.half * inv * inv
           * (V.dot k k * ab + 0ℚ * leftPair))
       akZero ⟩
    Strain.half * inv * inv
      * (V.dot k k * ab + 0ℚ * 0ℚ)
  ≡⟨ solve (inv ∷ k2 ∷ ab ∷ []) ⟩
    (Strain.half * inv * ab) * (inv * k2)
  ≡⟨ cong ((Strain.half * inv * ab) *_)
       (V.inverseLaw modeData) ⟩
    (Strain.half * inv * ab) * 1ℚ
  ≡⟨ solve (inv ∷ ab ∷ []) ⟩
    Strain.half * inv * ab
  ∎

fourierStrainTransversePolarization :
  ∀ modeData omega eta →
  V.dot (V.mode modeData) omega ≡ 0ℚ →
  V.dot (V.mode modeData) eta ≡ 0ℚ →
  frobeniusInner
    (Strain.fourierStrain modeData omega)
    (Strain.fourierStrain modeData eta)
  ≡ Strain.half * V.dot omega eta
fourierStrainTransversePolarization
    modeData omega eta omegaTransverse etaTransverse =
  let
    inv = V.inverseNormSquared modeData
    k = V.mode modeData
    k2 = V.normSquared k
    pairing = V.dot omega eta
    crossPair =
      V.dot (BS.cross k omega) (BS.cross k eta)

    crossPairMeaning : crossPair ≡ k2 * pairing
    crossPairMeaning =
      trans
        (crossMixedLagrange k omega eta)
        (trans
          (cong
            (λ leftPair →
              k2 * pairing - leftPair * V.dot k eta)
            omegaTransverse)
          (trans
            (cong
              (λ rightPair →
                k2 * pairing - 0ℚ * rightPair)
              etaTransverse)
            (solve (k2 ∷ pairing ∷ []))))
  in
  begin
    frobeniusInner
      (Strain.fourierStrain modeData omega)
      (Strain.fourierStrain modeData eta)
  ≡⟨ fourierStrainSameFibreCrossExact modeData omega eta ⟩
    Strain.half * inv * crossPair
  ≡⟨ cong (Strain.half * inv *_) crossPairMeaning ⟩
    Strain.half * inv * (k2 * pairing)
  ≡⟨ solve (inv ∷ k2 ∷ pairing ∷ []) ⟩
    Strain.half * (inv * k2) * pairing
  ≡⟨ cong (λ product → Strain.half * product * pairing)
       (V.inverseLaw modeData) ⟩
    Strain.half * 1ℚ * pairing
  ≡⟨ solve (pairing ∷ []) ⟩
    Strain.half * pairing
  ∎

twiceFourierStrainTransversePolarization :
  ∀ modeData omega eta →
  V.dot (V.mode modeData) omega ≡ 0ℚ →
  V.dot (V.mode modeData) eta ≡ 0ℚ →
  Strain.two * frobeniusInner
    (Strain.fourierStrain modeData omega)
    (Strain.fourierStrain modeData eta)
  ≡ V.dot omega eta
twiceFourierStrainTransversePolarization
    modeData omega eta omegaTransverse etaTransverse =
  trans
    (cong (Strain.two *_)
      (fourierStrainTransversePolarization
        modeData omega eta omegaTransverse etaTransverse))
    (solve (V.dot omega eta ∷ []))

record FourierStrainHalfIsometry (modeData : V.ProjectionMode) : Set where
  field
    image : V.Vector3 → Matrix.Matrix3
    imageExact : ∀ omega → image omega ≡ Strain.fourierStrain modeData omega
    preservesTransverseInnerProduct :
      ∀ omega eta →
      V.dot (V.mode modeData) omega ≡ 0ℚ →
      V.dot (V.mode modeData) eta ≡ 0ℚ →
      Strain.two * frobeniusInner (image omega) (image eta)
      ≡ V.dot omega eta

open FourierStrainHalfIsometry public

fourierStrainHalfIsometry :
  (modeData : V.ProjectionMode) → FourierStrainHalfIsometry modeData
fourierStrainHalfIsometry modeData = record
  { image = Strain.fourierStrain modeData
  ; imageExact = λ omega → refl
  ; preservesTransverseInnerProduct =
      twiceFourierStrainTransversePolarization modeData
  }

periodicFourierStrainGramClosed : Bool
periodicFourierStrainGramClosed = true

crossFibreStrainInterferenceFormulaClosed : Bool
crossFibreStrainInterferenceFormulaClosed = true

physicalHHGoodCrossFibreEstimateConstructed : Bool
physicalHHGoodCrossFibreEstimateConstructed = false

periodicFourierStrainGramClosedIsTrue :
  periodicFourierStrainGramClosed ≡ true
periodicFourierStrainGramClosedIsTrue = refl

crossFibreStrainInterferenceFormulaClosedIsTrue :
  crossFibreStrainInterferenceFormulaClosed ≡ true
crossFibreStrainInterferenceFormulaClosedIsTrue = refl

physicalHHGoodCrossFibreEstimateConstructedIsFalse :
  physicalHHGoodCrossFibreEstimateConstructed ≡ false
physicalHHGoodCrossFibreEstimateConstructedIsFalse = refl
