module DASHI.Physics.Closure.NSTriadKNLuoGalerkinFourierModePairExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "A Unified Approach to Regularity Problems for the 3D Navier-Stokes
-- and Euler Equations: The Use of Kolmogorov's Dissipation Range".
-- DOI: 10.1007/s00021-014-0167-4.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- This module connects the abstract pair-frequency damping cell to the actual
-- periodic Fourier-mode carrier already used by the Biot--Savart symbol.
-- For two transverse nonzero vorticity modes k and l, it defines
--
--   A(k,l) = |omega_k cross omega_l|^2,
--
-- uses |k|^2 and |l|^2 as the two Laplacian eigenvalues, and constructs the
-- exact PairFrequencyDefectCell.  Thus
--
--   2 nu kappa A(k,l)
--     <= nu (|k|^2 + |l|^2) A(k,l)
--
-- is now a theorem about literal periodic mode pairs rather than anonymous
-- rational eigenvalues.
--
-- An explicit pair k=e1, l=-e1, omega_k=e2, omega_l=e3 has zero convolution
-- output wavevector but defect amplitude one and pair diffusion two.  This is
-- the concrete high-high-to-zero-output witness motivating the input-frequency
-- F3 repair.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _≤_)
import Data.Rational.Properties as RationalProperties
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalDirectionalDefectExact as Physical
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicBiotSavartMultiplierExact as Biot
import DASHI.Physics.Closure.NSTriadKNLuoPairFrequencyDefectDiffusionExact as Pair

addVec : Gram.Vec3 → Gram.Vec3 → Gram.Vec3
addVec left right =
  Gram.vec3
    (Gram.x left + Gram.x right)
    (Gram.y left + Gram.y right)
    (Gram.z left + Gram.z right)

record GalerkinVorticityModePair : Set where
  constructor galerkinVorticityModePair
  field
    leftMode rightMode : Biot.NonzeroVorticityMode
    viscosity shellFloor : ℚ

    viscosityNonnegative : 0ℚ ≤ viscosity
    shellFloorNonnegative : 0ℚ ≤ shellFloor

    leftInShell :
      shellFloor ≤ Gram.normSquared (Biot.wavevector leftMode)
    rightInShell :
      shellFloor ≤ Gram.normSquared (Biot.wavevector rightMode)

open GalerkinVorticityModePair public

pairDefectAmplitude : GalerkinVorticityModePair → ℚ
pairDefectAmplitude pair =
  Gram.crossNormSquared
    (Biot.vorticity (leftMode pair))
    (Biot.vorticity (rightMode pair))

pairDefectAmplitudeNonnegative :
  ∀ pair → 0ℚ ≤ pairDefectAmplitude pair
pairDefectAmplitudeNonnegative pair =
  Gram.crossNormSquaredNonnegative
    (Biot.vorticity (leftMode pair))
    (Biot.vorticity (rightMode pair))

asPairFrequencyCell :
  GalerkinVorticityModePair → Pair.PairFrequencyDefectCell
asPairFrequencyCell pair =
  Pair.pairFrequencyDefectCell
    (viscosity pair)
    (shellFloor pair)
    (Gram.normSquared (Biot.wavevector (leftMode pair)))
    (Gram.normSquared (Biot.wavevector (rightMode pair)))
    (pairDefectAmplitude pair)
    (viscosityNonnegative pair)
    (shellFloorNonnegative pair)
    (Gram.normSquaredNonnegative (Biot.wavevector (leftMode pair)))
    (Gram.normSquaredNonnegative (Biot.wavevector (rightMode pair)))
    (pairDefectAmplitudeNonnegative pair)
    (leftInShell pair)
    (rightInShell pair)

fourierModePairShellDamping :
  ∀ pair →
  Pair.shellDefectDamping (asPairFrequencyCell pair)
  ≤ Pair.pairFrequencyDiffusion (asPairFrequencyCell pair)
fourierModePairShellDamping pair =
  Pair.pairFrequencyShellDamping (asPairFrequencyCell pair)

outputWavevector : GalerkinVorticityModePair → Gram.Vec3
outputWavevector pair =
  addVec
    (Biot.wavevector (leftMode pair))
    (Biot.wavevector (rightMode pair))

e1 e2 e3 negativeE1 zeroVec : Gram.Vec3
e1 = Gram.vec3 1ℚ 0ℚ 0ℚ
e2 = Gram.vec3 0ℚ 1ℚ 0ℚ
e3 = Gram.vec3 0ℚ 0ℚ 1ℚ
negativeE1 = Gram.vec3 (- 1ℚ) 0ℚ 0ℚ
zeroVec = Gram.vec3 0ℚ 0ℚ 0ℚ

leftWitnessMode : Biot.NonzeroVorticityMode
leftWitnessMode =
  Biot.nonzeroVorticityMode
    e1 e2 1ℚ
    (solve [])
    (solve [])

rightWitnessMode : Biot.NonzeroVorticityMode
rightWitnessMode =
  Biot.nonzeroVorticityMode
    negativeE1 e3 1ℚ
    (solve [])
    (solve [])

oppositeHighHighPair : GalerkinVorticityModePair
oppositeHighHighPair =
  galerkinVorticityModePair
    leftWitnessMode rightWitnessMode
    1ℚ 1ℚ
    RationalProperties.≤-refl
    RationalProperties.≤-refl
    RationalProperties.≤-refl
    RationalProperties.≤-refl

oppositePairOutputZero :
  outputWavevector oppositeHighHighPair ≡ zeroVec
oppositePairOutputZero =
  Physical.vec3Ext (solve []) (solve []) (solve [])

oppositePairDefectAmplitudeOne :
  pairDefectAmplitude oppositeHighHighPair ≡ 1ℚ
oppositePairDefectAmplitudeOne = solve []

oppositePairInputDiffusionTwo :
  Pair.pairFrequencyDiffusion
    (asPairFrequencyCell oppositeHighHighPair)
  ≡ 2
oppositePairInputDiffusionTwo = solve []

oppositePairShellDampingTwo :
  Pair.shellDefectDamping
    (asPairFrequencyCell oppositeHighHighPair)
  ≡ 2
oppositePairShellDampingTwo = solve []

record FourierModePairAuthorityBoundary : Set where
  constructor fourierModePairAuthorityBoundary
  field
    physicalModePairToFrequencyCellProved : Set
    transverseOppositeModeWitnessConstructed : Set
    highHighZeroOutputWithPositiveDefectProved : Set
    fullGalerkinConvolutionEnumerationConstructed : Set
    BonySupportExhaustivenessProved : Set
    NavierStokesFiveSourceCoefficientsDerived : Set

canonicalFourierModePairAuthorityBoundary : FourierModePairAuthorityBoundary
canonicalFourierModePairAuthorityBoundary =
  fourierModePairAuthorityBoundary ⊤ ⊤ ⊤ ⊥ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
