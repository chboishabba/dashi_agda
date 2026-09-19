module DASHI.Physics.Closure.NSTriadKNEuclideanProjectedCellOutputQExact where

------------------------------------------------------------------------
-- A / PROJECTED NONLINEAR CELL CARRIES ONE OUTPUT q
--
-- Reuse the exact continuous divergence-form cell
--
--   N_raw(xi;u,v) = i (xi . u) v
--
-- and the Bishop-real Leray contraction.
--
-- First, apply the R^3 directional Cauchy theorem separately to the real and
-- imaginary parts of u:
--
--   |xi . u|^2 <= |xi|^2 ||u||^2.
--
-- Since scalar multiplication of v multiplies its C^3 norm-square by the
-- scalar modulus-square,
--
--   ||N_raw||^2
--     = |xi.u|^2 ||v||^2
--     <= |xi|^2 ||u||^2 ||v||^2.
--
-- Leray is contractive, hence the SAME q factor survives projection.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanDivergenceFormOutputFactorExact as Output
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Physics.Closure.NSWholeSpaceR3DirectionalSecondMomentQGainExact as Directional
import DASHI.Physics.Closure.NSTriadKNEuclideanBishopLerayPythagorasExact as Leray

realVector :
  Physical.BishopComplex3 → Euclidean.R3Frequency
realVector u =
  Euclidean.r3-frequency
    (Physical.realPart (Physical.cx u))
    (Physical.realPart (Physical.cy u))
    (Physical.realPart (Physical.cz u))

imaginaryVector :
  Physical.BishopComplex3 → Euclidean.R3Frequency
imaginaryVector u =
  Euclidean.r3-frequency
    (Physical.imaginaryPart (Physical.cx u))
    (Physical.imaginaryPart (Physical.cy u))
    (Physical.imaginaryPart (Physical.cz u))

realDotMeaning :
  (output : Euclidean.R3Frequency) →
  (u : Physical.BishopComplex3) →
  BishopReal._≃_
    (Physical.realPart (Output.frequencyDot output u))
    (Directional.dot output (realVector u))
realDotMeaning output u =
  BishopP.≃-refl
    (Directional.dot output (realVector u))

imaginaryDotMeaning :
  (output : Euclidean.R3Frequency) →
  (u : Physical.BishopComplex3) →
  BishopReal._≃_
    (Physical.imaginaryPart (Output.frequencyDot output u))
    (Directional.dot output (imaginaryVector u))
imaginaryDotMeaning output u =
  BishopP.≃-refl
    (Directional.dot output (imaginaryVector u))

realImagNormSum :
  (u : Physical.BishopComplex3) →
  BishopReal._≃_
    (BishopReal._+_
      (Heat.frequencyNormSquared (realVector u))
      (Heat.frequencyNormSquared (imaginaryVector u)))
    (Leray.complex3NormSquared u)
realImagNormSum
    (Physical.bishop-complex3
      (Physical.bishop-complex xr xi)
      (Physical.bishop-complex yr yi)
      (Physical.bishop-complex zr zi)) =
  let open BishopP.ℝ-Solver
  in
  solve 6
    (λ xr' xi' yr' yi' zr' zi' →
      ((xr' ⊗ xr') ⊕ ((yr' ⊗ yr') ⊕ (zr' ⊗ zr')))
      ⊕
      ((xi' ⊗ xi') ⊕ ((yi' ⊗ yi') ⊕ (zi' ⊗ zi')))
      ⊜
      ((xr' ⊗ xr' ⊕ xi' ⊗ xi')
       ⊕
       ((yr' ⊗ yr' ⊕ yi' ⊗ yi')
        ⊕
        (zr' ⊗ zr' ⊕ zi' ⊗ zi'))))
    BishopP.≃-refl
    xr xi yr yi zr zi

complexDirectionalCauchy :
  (output : Euclidean.R3Frequency) →
  (u : Physical.BishopComplex3) →
  BishopReal._≤_
    (Leray.complexModulusSquared
      (Output.frequencyDot output u))
    (BishopReal._*_
      (Heat.frequencyNormSquared output)
      (Leray.complex3NormSquared u))
complexDirectionalCauchy output u =
  let
    realBound =
      Directional.directionalSquareBelowNormProduct
        output (realVector u)

    imagBound =
      Directional.directionalSquareBelowNormProduct
        output (imaginaryVector u)

    added :
      BishopReal._≤_
        (BishopReal._+_
          (BishopReal._*_
            (Physical.realPart (Output.frequencyDot output u))
            (Physical.realPart (Output.frequencyDot output u)))
          (BishopReal._*_
            (Physical.imaginaryPart (Output.frequencyDot output u))
            (Physical.imaginaryPart (Output.frequencyDot output u))))
        (BishopReal._+_
          (BishopReal._*_
            (Heat.frequencyNormSquared output)
            (Heat.frequencyNormSquared (realVector u)))
          (BishopReal._*_
            (Heat.frequencyNormSquared output)
            (Heat.frequencyNormSquared (imaginaryVector u))))
    added =
      BishopP.+-mono-≤
        (BishopP.≤-respˡ-≃
          (BishopP.*-cong
            (realDotMeaning output u)
            (realDotMeaning output u))
          realBound)
        (BishopP.≤-respˡ-≃
          (BishopP.*-cong
            (imaginaryDotMeaning output u)
            (imaginaryDotMeaning output u))
          imagBound)

    factorOutput :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal._*_
            (Heat.frequencyNormSquared output)
            (Heat.frequencyNormSquared (realVector u)))
          (BishopReal._*_
            (Heat.frequencyNormSquared output)
            (Heat.frequencyNormSquared (imaginaryVector u))))
        (BishopReal._*_
          (Heat.frequencyNormSquared output)
          (Leray.complex3NormSquared u))
    factorOutput =
      let open BishopP.ℝ-Solver
      in
      BishopP.≃-trans
        (solve 3
          (λ q r i →
            q ⊗ r ⊕ q ⊗ i
            ⊜ q ⊗ (r ⊕ i))
          BishopP.≃-refl
          (Heat.frequencyNormSquared output)
          (Heat.frequencyNormSquared (realVector u))
          (Heat.frequencyNormSquared (imaginaryVector u)))
        (BishopP.*-congˡ (realImagNormSum u))
  in
  BishopP.≤-respʳ-≃ factorOutput added

rawCellNormFactorization :
  (output : Euclidean.R3Frequency) →
  (uEta uZeta : Physical.BishopComplex3) →
  BishopReal._≃_
    (Leray.complex3NormSquared
      (Output.divergenceFormRawCell output uEta uZeta))
    (BishopReal._*_
      (Leray.complexModulusSquared
        (Output.frequencyDot output uEta))
      (Leray.complex3NormSquared uZeta))
rawCellNormFactorization
    output
    (Physical.bishop-complex3 ux uy uz)
    (Physical.bishop-complex3
      (Physical.bishop-complex vxr vxi)
      (Physical.bishop-complex vyr vyi)
      (Physical.bishop-complex vzr vzi)) =
  let
    d = Output.frequencyDot output
          (Physical.bishop-complex3 ux uy uz)
    dr = Physical.realPart d
    di = Physical.imaginaryPart d
    open BishopP.ℝ-Solver
  in
  solve 8
    (λ dr' di' vxr' vxi' vyr' vyi' vzr' vzi' →
      (((((BishopReal.0ℝ ⊗ dr' ⊖ BishopReal.1ℝ ⊗ di')
          ⊗ vxr')
         ⊖
         ((BishopReal.0ℝ ⊗ di' ⊕ BishopReal.1ℝ ⊗ dr')
          ⊗ vxi'))
        ⊗
        (((BishopReal.0ℝ ⊗ dr' ⊖ BishopReal.1ℝ ⊗ di')
          ⊗ vxr')
         ⊖
         ((BishopReal.0ℝ ⊗ di' ⊕ BishopReal.1ℝ ⊗ dr')
          ⊗ vxi')))
       ⊕
       ((((BishopReal.0ℝ ⊗ dr' ⊖ BishopReal.1ℝ ⊗ di')
          ⊗ vxi')
         ⊕
         ((BishopReal.0ℝ ⊗ di' ⊕ BishopReal.1ℝ ⊗ dr')
          ⊗ vxr'))
        ⊗
        (((BishopReal.0ℝ ⊗ dr' ⊖ BishopReal.1ℝ ⊗ di')
          ⊗ vxi')
         ⊕
         ((BishopReal.0ℝ ⊗ di' ⊕ BishopReal.1ℝ ⊗ dr')
          ⊗ vxr'))))
      ⊕
      (((((BishopReal.0ℝ ⊗ dr' ⊖ BishopReal.1ℝ ⊗ di')
          ⊗ vyr')
         ⊖
         ((BishopReal.0ℝ ⊗ di' ⊕ BishopReal.1ℝ ⊗ dr')
          ⊗ vyi'))
        ⊗
        (((BishopReal.0ℝ ⊗ dr' ⊖ BishopReal.1ℝ ⊗ di')
          ⊗ vyr')
         ⊖
         ((BishopReal.0ℝ ⊗ di' ⊕ BishopReal.1ℝ ⊗ dr')
          ⊗ vyi')))
       ⊕
       ((((BishopReal.0ℝ ⊗ dr' ⊖ BishopReal.1ℝ ⊗ di')
          ⊗ vyi')
         ⊕
         ((BishopReal.0ℝ ⊗ di' ⊕ BishopReal.1ℝ ⊗ dr')
          ⊗ vyr'))
        ⊗
        (((BishopReal.0ℝ ⊗ dr' ⊖ BishopReal.1ℝ ⊗ di')
          ⊗ vyi')
         ⊕
         ((BishopReal.0ℝ ⊗ di' ⊕ BishopReal.1ℝ ⊗ dr')
          ⊗ vyr')))
       ⊕
       ((((BishopReal.0ℝ ⊗ dr' ⊖ BishopReal.1ℝ ⊗ di')
          ⊗ vzr')
         ⊖
         ((BishopReal.0ℝ ⊗ di' ⊕ BishopReal.1ℝ ⊗ dr')
          ⊗ vzi'))
        ⊗
        (((BishopReal.0ℝ ⊗ dr' ⊖ BishopReal.1ℝ ⊗ di')
          ⊗ vzr')
         ⊖
         ((BishopReal.0ℝ ⊗ di' ⊕ BishopReal.1ℝ ⊗ dr')
          ⊗ vzi')))
       ⊕
       ((((BishopReal.0ℝ ⊗ dr' ⊖ BishopReal.1ℝ ⊗ di')
          ⊗ vzi')
         ⊕
         ((BishopReal.0ℝ ⊗ di' ⊕ BishopReal.1ℝ ⊗ dr')
          ⊗ vzr'))
        ⊗
        (((BishopReal.0ℝ ⊗ dr' ⊖ BishopReal.1ℝ ⊗ di')
          ⊗ vzi')
         ⊕
         ((BishopReal.0ℝ ⊗ di' ⊕ BishopReal.1ℝ ⊗ dr')
          ⊗ vzr'))))
      ⊜
      (dr' ⊗ dr' ⊕ di' ⊗ di')
      ⊗
      ((vxr' ⊗ vxr' ⊕ vxi' ⊗ vxi')
       ⊕
       ((vyr' ⊗ vyr' ⊕ vyi' ⊗ vyi')
        ⊕
        (vzr' ⊗ vzr' ⊕ vzi' ⊗ vzi'))))
    BishopP.≃-refl
    dr di vxr vxi vyr vyi vzr vzi

rawCellOutputQBound :
  (output : Euclidean.R3Frequency) →
  (uEta uZeta : Physical.BishopComplex3) →
  BishopReal._≤_
    (Leray.complex3NormSquared
      (Output.divergenceFormRawCell output uEta uZeta))
    (BishopReal._*_
      (Heat.frequencyNormSquared output)
      (BishopReal._*_
        (Leray.complex3NormSquared uEta)
        (Leray.complex3NormSquared uZeta)))
rawCellOutputQBound output uEta uZeta =
  let
    zetaNN = Leray.complex3NormSquaredNonnegative uZeta

    scaled =
      BishopP.*-monoʳ-≤-nonNeg
        (complexDirectionalCauchy output uEta)
        zetaNN

    reassociate :
      BishopReal._≃_
        (BishopReal._*_
          (BishopReal._*_
            (Heat.frequencyNormSquared output)
            (Leray.complex3NormSquared uEta))
          (Leray.complex3NormSquared uZeta))
        (BishopReal._*_
          (Heat.frequencyNormSquared output)
          (BishopReal._*_
            (Leray.complex3NormSquared uEta)
            (Leray.complex3NormSquared uZeta)))
    reassociate =
      let open BishopP.ℝ-Solver
      in solve 3
        (λ q a b → (q ⊗ a) ⊗ b ⊜ q ⊗ (a ⊗ b))
        BishopP.≃-refl
        (Heat.frequencyNormSquared output)
        (Leray.complex3NormSquared uEta)
        (Leray.complex3NormSquared uZeta)
  in
  BishopP.≤-respˡ-≃
    (rawCellNormFactorization output uEta uZeta)
    (BishopP.≤-respʳ-≃ reassociate scaled)

projectedCellOutputQBound :
  (output : Euclidean.R3Frequency) →
  (inverseData : Leray.ContinuousLerayInverse output) →
  (uEta uZeta : Physical.BishopComplex3) →
  BishopReal._≤_
    (Leray.complex3NormSquared
      (Leray.lerayProject
        output inverseData
        (Output.divergenceFormRawCell output uEta uZeta)))
    (BishopReal._*_
      (Heat.frequencyNormSquared output)
      (BishopReal._*_
        (Leray.complex3NormSquared uEta)
        (Leray.complex3NormSquared uZeta)))
projectedCellOutputQBound output inverseData uEta uZeta =
  BishopP.≤-trans
    (Leray.lerayNormSquaredContraction
      output inverseData
      (Output.divergenceFormRawCell output uEta uZeta))
    (rawCellOutputQBound output uEta uZeta)

projectedCellOutputQGainClosed : Bool
projectedCellOutputQGainClosed = true

projectedCellMajorant :
  Physical.BishopComplex3 →
  Physical.BishopComplex3 →
  BishopReal.ℝ
projectedCellMajorant uEta uZeta =
  BishopReal._*_
    (Leray.complex3NormSquared uEta)
    (Leray.complex3NormSquared uZeta)

periodicLerayContractionReusedStructurally : Bool
periodicLerayContractionReusedStructurally = true

physicalEuclideanProjectedInteractionWeldClosedHere : Bool
physicalEuclideanProjectedInteractionWeldClosedHere = false

clayPromotion : Bool
clayPromotion = false

projectedCellOutputQGainClosedIsTrue :
  projectedCellOutputQGainClosed ≡ true
projectedCellOutputQGainClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
