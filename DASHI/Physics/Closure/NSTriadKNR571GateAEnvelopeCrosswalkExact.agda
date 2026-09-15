module DASHI.Physics.Closure.NSTriadKNR571GateAEnvelopeCrosswalkExact where

------------------------------------------------------------------------
-- R571 GATE-A ENVELOPE CROSSWALK
--
-- Post-PR #920 boundary.  The R571 -> paired second-order -> scoped finite
-- second-moment compiler is already source-written.  This owner does not add
-- another compiler.  It records the shortest existing donor for each physical
-- envelope and makes one useful canonical choice on the radial Taylor side.
--
-- Preferred Taylor choice:
--   L := m(k+y) - m(k).
--
-- Then the + remainder is definitionally zero.  All radial curvature debt is
-- concentrated in the opposite/centered remainder.  This avoids inventing an
-- independent derivative model merely to populate MultiplierTaylorPair.
--
-- Donor firewall:
-- * A1 geometry donor: resonant reverse-triangle / radial-gap machinery.
-- * G2 algebra donor: finite path difference -> gradient-energy theorem.
-- * G1 magnitude donor: exact modal-energy/Cauchy amplitude machinery.
--
-- None of those donor theorems by itself supplies the required cutoff- and
-- scale-uniform physical R571 family envelope.  Those same-object transports
-- remain explicit below.  A2 is isolated in
-- NSTriadKNR571RadialCurvatureBoundaryExact.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _-_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311
import DASHI.Physics.Closure.NSTriadKNR571HomochiralRadialIncrementSpecializationExact as Weld
import DASHI.Physics.Closure.NSTriadKNR571HomochiralPairedSecondMomentRealizationExact as R571Pair
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicMultiplierTaylorDifferenceExact as Taylor

-- Existing donors.  Importing them here is intentional: this is the typed
-- archaeology/crosswalk surface for the four Gate-A leaves.
import DASHI.Physics.Closure.NSTriadKNExternalHHOutputRadialGapRound124Exact as A1Donor
import DASHI.Physics.Closure.NSTriadKNRationalNormalizedDirectionUnitRound455Exact as RadiusDonor
import DASHI.Physics.Closure.NSTriadKNLuoFinitePathDifferenceDiffusionExact as G2Donor
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeEnergyProductRound105Exact as G1Donor

preferredLinearModel :
  R311.HelicitySign →
  Helical.HelicalModeScalars Weld.F →
  Z3.FourierMode → Z3.FourierMode → ℚ
preferredLinearModel sign S center plus =
  R571Pair.radialSymbol sign S plus - R571Pair.radialSymbol sign S center

preferredRadialTaylorPair :
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (center plus minus : Z3.FourierMode) →
  Taylor.MultiplierTaylorPair
preferredRadialTaylorPair sign S center plus minus =
  R571Pair.radialTaylorPair
    sign S center plus minus (preferredLinearModel sign S center plus)

preferredLinearIncrementIsPlusRadialDifference :
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (center plus minus : Z3.FourierMode) →
  Taylor.linearIncrement (preferredRadialTaylorPair sign S center plus minus)
  ≡ preferredLinearModel sign S center plus
preferredLinearIncrementIsPlusRadialDifference sign S center plus minus = refl

preferredPlusRemainderZero :
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (center plus minus : Z3.FourierMode) →
  Taylor.plusRemainder (preferredRadialTaylorPair sign S center plus minus)
  ≡ 0ℚ
preferredPlusRemainderZero sign S center plus minus =
  solve
    ( R571Pair.radialSymbol sign S plus
    ∷ R571Pair.radialSymbol sign S center
    ∷ [])

-- A1: exact radial-gap/reverse-triangle geometry already exists, and R455 owns
-- the rational modeNorm^2/radius crosswalk.  What remains is the explicit
-- transport from the chosen R571 +y displacement to the scalar stepMagnitude
-- used by the physical sample family.
r571GateAPreferredLinearizationClosed : Bool
r571GateAPreferredLinearizationClosed = true

r571GateAA1ReverseTriangleDonorLocated : Bool
r571GateAA1ReverseTriangleDonorLocated = true

r571GateAA1RadiusSquareCrosswalkLocated : Bool
r571GateAA1RadiusSquareCrosswalkLocated = true

r571GateAA1PhysicalFamilyUniformBoundClosed : Bool
r571GateAA1PhysicalFamilyUniformBoundClosed = false

-- G2: the finite vector path/Jensen inequality is already theorem-bearing.
-- The remaining work is same-object identification of the transported physical
-- Fourier coefficient difference with a torus path/gradient family carrying a
-- scale-uniform coefficient.
r571GateAG2FinitePathDonorLocated : Bool
r571GateAG2FinitePathDonorLocated = true

r571GateAG2PhysicalGradientCrosswalkClosed : Bool
r571GateAG2PhysicalGradientCrosswalkClosed = false

-- G1: exact Cauchy/Lagrange modal-energy majorants already exist.  The remaining
-- work is the least-privilege shifted-state coefficient envelope on the actual
-- R571 family, with the desired scale/cutoff uniformity.
r571GateAG1ModalEnergyDonorLocated : Bool
r571GateAG1ModalEnergyDonorLocated = true

r571GateAG1ShiftedCoefficientEnvelopeClosed : Bool
r571GateAG1ShiftedCoefficientEnvelopeClosed = false

r571GateAA2DelegatedToRadialCurvatureBoundary : Bool
r571GateAA2DelegatedToRadialCurvatureBoundary = true

r571GateAFullPhysicalEnvelopePackageClosed : Bool
r571GateAFullPhysicalEnvelopePackageClosed = false

r571GateAClosesR568 : Bool
r571GateAClosesR568 = false
