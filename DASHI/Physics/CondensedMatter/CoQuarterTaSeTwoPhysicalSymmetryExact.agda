module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoPhysicalSymmetryExact where

------------------------------------------------------------------------
-- CRYSTALLOGRAPHY / MAGNETISM PRIMARY SOURCES (distinct observations):
--
-- H. C. Mandujano et al., "Itinerant A-type antiferromagnetic order
-- in Co1/4TaSe2", Physical Review B 110, 144420 (2024).
-- DOI: 10.1103/PhysRevB.110.144420
--   Nuclear space group P63/mmc (No. 194), two Co environments in
--   opposite-spin A-type planes, axial ordered moment 1.35(11) mu_B.
--   Magnetic transition reported at 173 K.
--
-- M. Sprague et al., "Observation of Altermagnetic Spin-Splitting in an
-- Intercalated Transition Metal Dichalcogenide", Nat Commun (2026).
-- DOI: 10.1038/s41467-026-76784-x
--   Co on 2a Wyckoff site, 2x2 in-plane supercell; 178 K transition.
--   Nodal planes kz = 0 and pi/c, symmetry plane Gamma-K-H-A,
--   off-plane Gamma'-M' splitting at kz ~ pi/(2c).
--   ARPES photon energies 48 eV (near kz=0) and 55 eV
--   (near kz=pi/(2c)), measured low T = 7 K.
--
-- DASHI CONTRIBUTION:
--   A discrete reciprocal-axis mirror, its fixed-momentum theorem,
--   and a fully explicit symmetry-covariant example with an off-nodal
--   spin splitting.  This is a *symmetry-identified k-space skeleton*.
--
-- LIMITATION:
--   A real-space 6_3 screw with its fractional translation phase,
--   nonsymmorphic band representation, full magnetic space group,
--   Bloch eigenvectors, SOC, k_z broadening and raw ARPES counts are
--   NOT computed here.  In particular the 48/55 eV -> kz mapping is
--   an experimental assignment, not derived from a final-state model.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

import DASHI.Physics.CondensedMatter.AltermagnetCoQuarterTaSeTwo as NativeSpin

-- Discrete representatives of the physical reciprocal-axis classes.
-- top and bottom are distinct non-fixed momenta; kz=pi/c is fixed
-- under mirror reflection *modulo* a reciprocal lattice vector 2pi/c.
data Kz : Set where
  zeroPlane positiveHalf piPlane negativeHalf : Kz

reflectZ : Kz → Kz
reflectZ zeroPlane = zeroPlane
reflectZ positiveHalf = negativeHalf
reflectZ piPlane = piPlane
reflectZ negativeHalf = positiveHalf

reflectZInvolution : (k : Kz) → reflectZ (reflectZ k) ≡ k
reflectZInvolution zeroPlane = refl
reflectZInvolution positiveHalf = refl
reflectZInvolution piPlane = refl
reflectZInvolution negativeHalf = refl

data InPlane : Set where
  gammaToK gammaToM : InPlane

-- A point on a mirror-invariant in-plane high-symmetry line and an
-- off-line point.  The paper's g-wave pattern needs more in-plane
-- angles than this quotient: no full g-wave harmonic is claimed here.
data Channel : Set where
  mirrorLine genericLine : Channel

record KPoint : Set where
  constructor point
  field
    kz : Kz
    inPlane : InPlane
    channel : Channel
open KPoint public

mirrorK : KPoint → KPoint
mirrorK (point z d h) = point (reflectZ z) d h

mirrorKInvolution : (k : KPoint) →
  mirrorK (mirrorK k) ≡ k
mirrorKInvolution (point zeroPlane d h) = refl
mirrorKInvolution (point positiveHalf d h) = refl
mirrorKInvolution (point piPlane d h) = refl
mirrorKInvolution (point negativeHalf d h) = refl

-- Abstract physical symmetry law in the SOC-free spin-conserving limit.
-- This is an assumption on a candidate E, not automatically true for
-- arbitrary numerical bands or the fully relativistic Hamiltonian.
SpinMirrorLaw : (KPoint → NativeSpin.Spin → Nat) → Set
SpinMirrorLaw E =
  (k : KPoint) (s : NativeSpin.Spin) →
    E (mirrorK k) (NativeSpin.reverseSpin s) ≡ E k s

-- Fixed momentum + spin exchange covariance FORCE local spin
-- degeneracy.  The fixed-point proof is explicitly supplied.
fixedMomentumDegeneracy :
  (E : KPoint → NativeSpin.Spin → Nat) →
  SpinMirrorLaw E →
  (k : KPoint) → mirrorK k ≡ k →
  E k NativeSpin.up ≡ E k NativeSpin.down
fixedMomentumDegeneracy E law k fixed =
  trans
    (sym (law k NativeSpin.down))
    (cong (λ q → E q NativeSpin.up) fixed)

kzZeroFixed : (d : InPlane) (h : Channel) →
  mirrorK (point zeroPlane d h) ≡ point zeroPlane d h
kzZeroFixed d h = refl

kzPiFixed : (d : InPlane) (h : Channel) →
  mirrorK (point piPlane d h) ≡ point piPlane d h
kzPiFixed d h = refl

-- Physical high-symmetry planes identified by the cited measurements.
nodalZero :
  (E : KPoint → NativeSpin.Spin → Nat) → SpinMirrorLaw E →
  (d : InPlane) (h : Channel) →
  E (point zeroPlane d h) NativeSpin.up ≡
  E (point zeroPlane d h) NativeSpin.down
nodalZero E law d h =
  fixedMomentumDegeneracy E law (point zeroPlane d h)
    (kzZeroFixed d h)

nodalPi :
  (E : KPoint → NativeSpin.Spin → Nat) → SpinMirrorLaw E →
  (d : InPlane) (h : Channel) →
  E (point piPlane d h) NativeSpin.up ≡
  E (point piPlane d h) NativeSpin.down
nodalPi E law d h =
  fixedMomentumDegeneracy E law (point piPlane d h)
    (kzPiFixed d h)

-- Finite spectral realisation.  These are NOT energies in meV:
-- all bands at nodal planes and on the nominated in-plane mirror
-- line are degenerate; an off-nodal/off-line pair is spin-split.
sampleBand : KPoint → NativeSpin.Spin → Nat
sampleBand (point zeroPlane d h) s = zero
sampleBand (point piPlane d h) s = zero
sampleBand (point positiveHalf d mirrorLine) s = zero
sampleBand (point negativeHalf d mirrorLine) s = zero
sampleBand (point positiveHalf d genericLine) NativeSpin.up = zero
sampleBand (point positiveHalf d genericLine) NativeSpin.down = suc zero
sampleBand (point negativeHalf d genericLine) NativeSpin.up = suc zero
sampleBand (point negativeHalf d genericLine) NativeSpin.down = zero

sampleSpinMirrorLaw : SpinMirrorLaw sampleBand
sampleSpinMirrorLaw (point zeroPlane d mirrorLine) NativeSpin.up = refl
sampleSpinMirrorLaw (point zeroPlane d mirrorLine) NativeSpin.down = refl
sampleSpinMirrorLaw (point zeroPlane d genericLine) NativeSpin.up = refl
sampleSpinMirrorLaw (point zeroPlane d genericLine) NativeSpin.down = refl
sampleSpinMirrorLaw (point piPlane d mirrorLine) NativeSpin.up = refl
sampleSpinMirrorLaw (point piPlane d mirrorLine) NativeSpin.down = refl
sampleSpinMirrorLaw (point piPlane d genericLine) NativeSpin.up = refl
sampleSpinMirrorLaw (point piPlane d genericLine) NativeSpin.down = refl
sampleSpinMirrorLaw (point positiveHalf d mirrorLine) NativeSpin.up = refl
sampleSpinMirrorLaw (point positiveHalf d mirrorLine) NativeSpin.down = refl
sampleSpinMirrorLaw (point negativeHalf d mirrorLine) NativeSpin.up = refl
sampleSpinMirrorLaw (point negativeHalf d mirrorLine) NativeSpin.down = refl
sampleSpinMirrorLaw (point positiveHalf d genericLine) NativeSpin.up = refl
sampleSpinMirrorLaw (point positiveHalf d genericLine) NativeSpin.down = refl
sampleSpinMirrorLaw (point negativeHalf d genericLine) NativeSpin.up = refl
sampleSpinMirrorLaw (point negativeHalf d genericLine) NativeSpin.down = refl

sampleNodalZero : (d : InPlane) (h : Channel) →
  sampleBand (point zeroPlane d h) NativeSpin.up ≡
  sampleBand (point zeroPlane d h) NativeSpin.down
sampleNodalZero = nodalZero sampleBand sampleSpinMirrorLaw

sampleNodalPi : (d : InPlane) (h : Channel) →
  sampleBand (point piPlane d h) NativeSpin.up ≡
  sampleBand (point piPlane d h) NativeSpin.down
sampleNodalPi = nodalPi sampleBand sampleSpinMirrorLaw

sampleOffNodalSplit :
  sampleBand (point positiveHalf gammaToM genericLine) NativeSpin.up
  ≡ sampleBand (point positiveHalf gammaToM genericLine) NativeSpin.down
  → ⊥
sampleOffNodalSplit ()

-- The observable and the associated measurement geometry remain
-- DISTINCT.  Spin polarization cannot be inferred from equal-energy
-- photospectra alone without the spin-sensitive observation channel.
data PhotonCondition : Set where
  eV48 eV55 : PhotonCondition

experimentalKzAssignment : PhotonCondition → Kz
experimentalKzAssignment eV48 = zeroPlane
experimentalKzAssignment eV55 = positiveHalf

data SampleTemperature : Set where
  kelvin7 kelvin200 : SampleTemperature

data EvidenceType : Set where
  neutronMagnetism spinARPES ordinaryARPES densityFunctionalTheory : EvidenceType

-- Source-grounded role labels: NOT a calibration pipeline.
data Experiment : Set where
  exp48At7K exp55At7K exp55At200K : Experiment

condition : Experiment → PhotonCondition
condition exp48At7K = eV48
condition exp55At7K = eV55
condition exp55At200K = eV55

temperature : Experiment → SampleTemperature
temperature exp48At7K = kelvin7
temperature exp55At7K = kelvin7
temperature exp55At200K = kelvin200

lowTemperatureNodalAssignment :
  experimentalKzAssignment (condition exp48At7K) ≡ zeroPlane
lowTemperatureNodalAssignment = refl

lowTemperatureOffNodalAssignment :
  experimentalKzAssignment (condition exp55At7K) ≡ positiveHalf
lowTemperatureOffNodalAssignment = refl
