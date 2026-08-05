module DASHI.Physics.Closure.NSTriadKNCherevanPacketScaleAuditExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Pylyp Cherevan.
-- Title: "Log-free estimate for the resonant paraproduct in the 3D
-- Navier--Stokes equations".
-- arXiv DOI: 10.48550/arXiv.2510.06246.
--
-- Related wave-packet reference:
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Audit the packet/tile normalizations at the concrete shell lambda=4.
-- An angular aperture lambda^-1/2=1/2 on a radius-four shell has transverse
-- frequency width
--
--   lambda * lambda^-1/2 = 2,
--
-- not 1/2.  With dyadic radial width lambda=4 the frequency volume is 16,
-- so the diagonal TT* kernel has size 16, not lambda^(3/2)=8.  The physical
-- packet volume is 1/16.  L2 normalization therefore requires amplitude 4;
-- the source's displayed amplitude 8 gives squared L2 mass 4 rather than 1.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_; _<_)
open import Data.Rational.Properties as ℚₚ using (_<?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary.Decidable.Core using (toWitness)

lambda aperture actualTransverseWidth claimedTileWidth : ℚ
lambda = Int.+ 4 / 1
aperture = Int.+ 1 / 2
actualTransverseWidth = lambda * aperture
claimedTileWidth = aperture

actualTransverseWidthIsTwo :
  actualTransverseWidth ≡ Int.+ 2 / 1
actualTransverseWidthIsTwo = solve []

claimedTileIsStrictlyTooSmall :
  claimedTileWidth < actualTransverseWidth
claimedTileIsStrictlyTooSmall =
  toWitness {a? = claimedTileWidth ℚₚ.<? actualTransverseWidth} _

radialFrequencyWidth actualFrequencyVolume claimedKernelPrefactor : ℚ
radialFrequencyWidth = lambda
actualFrequencyVolume =
  actualTransverseWidth * actualTransverseWidth * radialFrequencyWidth
claimedKernelPrefactor = Int.+ 8 / 1

actualFrequencyVolumeIsSixteen :
  actualFrequencyVolume ≡ Int.+ 16 / 1
actualFrequencyVolumeIsSixteen = solve []

claimedKernelPrefactorIsTooSmall :
  claimedKernelPrefactor < actualFrequencyVolume
claimedKernelPrefactorIsTooSmall =
  toWitness {a? = claimedKernelPrefactor ℚₚ.<? actualFrequencyVolume} _

physicalTransverseWidth physicalLongitudinalWidth physicalPacketVolume : ℚ
physicalTransverseWidth = aperture
physicalLongitudinalWidth = Int.+ 1 / 4
physicalPacketVolume =
  physicalTransverseWidth * physicalTransverseWidth
  * physicalLongitudinalWidth

correctL2Amplitude sourceDisplayedAmplitude : ℚ
correctL2Amplitude = lambda
sourceDisplayedAmplitude = claimedKernelPrefactor

correctPacketSquaredMass sourcePacketSquaredMass : ℚ
correctPacketSquaredMass =
  correctL2Amplitude * correctL2Amplitude * physicalPacketVolume
sourcePacketSquaredMass =
  sourceDisplayedAmplitude * sourceDisplayedAmplitude * physicalPacketVolume

correctPacketIsUnitMass :
  correctPacketSquaredMass ≡ Int.+ 1 / 1
correctPacketIsUnitMass = solve []

sourcePacketSquaredMassIsFour :
  sourcePacketSquaredMass ≡ Int.+ 4 / 1
sourcePacketSquaredMassIsFour = solve []
