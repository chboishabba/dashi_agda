module DASHI.Physics.Closure.NSTriadKNR571GateAEnvelopeCrosswalkExact where

------------------------------------------------------------------------
-- R571 GATE-A ENVELOPE CROSSWALK
--
-- Post-PR #920 boundary.  The R571 -> paired second-order -> scoped finite
-- second-moment compiler is already source-written.  This owner does not add
-- another compiler.  It records the shortest existing donor for each physical
-- envelope, the theorem-bearing Lean radial receipts, and the local Hermitian
-- vector->scalar weld used by the old centered pair.
--
-- Preferred Taylor choice:
--   L := m(k+y) - m(k).
--
-- Then the + remainder is definitionally zero.  All radial curvature debt is
-- concentrated in the opposite/centered remainder.  This avoids inventing an
-- independent derivative model merely to populate MultiplierTaylorPair.
--
-- Donor / receipt firewall:
-- * A1 geometry donor: resonant reverse-triangle / radial-gap machinery.
-- * A1/A2 theorem-bearing Lean receipts: dedicated periodic-B Aristotle task.
-- * G0': existing R291 real-Hermitian scalarization into the old R27 pair.
-- * G2 algebra donor: finite path difference -> gradient-energy theorem.
-- * G1 local scalar envelope: exact rational Hermitian Young on G0' carrier.
--
-- The Lean radial receipts do not themselves construct the rational Agda
-- family/sample weld.  G0' plus the local G1 theorem still do not pay G2 or a
-- cutoff-uniform family envelope.  Those remain live state-side obligations.
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
import DASHI.Physics.Closure.NSTriadKNR571LeanGateAEnvelopeReceiptExact as LeanReceipt
import DASHI.Physics.Closure.NSTriadKNR571HermitianScalarizedOppositePairExact as G0
import DASHI.Physics.Closure.NSTriadKNR571HermitianStateAmplitudeEnvelopeExact as G1Local
import DASHI.Physics.Closure.NSTriadKNR571HermitianStateDifferenceRound613Exact as G2Local

-- Existing donors.  Importing them here is intentional: this is the typed
-- archaeology/crosswalk surface for the four Gate-A leaves.
import DASHI.Physics.Closure.NSTriadKNExternalHHOutputRadialGapRound124Exact as A1Donor
import DASHI.Physics.Closure.NSTriadKNRationalNormalizedDirectionUnitRound455Exact as RadiusDonor
import DASHI.Physics.Closure.NSTriadKNLuoFinitePathDifferenceDiffusionExact as G2Donor

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

------------------------------------------------------------------------
-- A1/A2 radial side.
------------------------------------------------------------------------

r571GateAPreferredLinearizationClosed : Bool
r571GateAPreferredLinearizationClosed = true

r571GateAA1ReverseTriangleDonorLocated : Bool
r571GateAA1ReverseTriangleDonorLocated = true

r571GateAA1RadiusSquareCrosswalkLocated : Bool
r571GateAA1RadiusSquareCrosswalkLocated = true

-- Dedicated Lean theorem receipts now pay the radial mathematics on the
-- periodic-B real carrier.  These are receipt coordinates, not Agda proof
-- inhabitants.
r571GateAA1LeanTheoremReceiptObserved : Bool
r571GateAA1LeanTheoremReceiptObserved =
  LeanReceipt.leanGateAA1ReceiptObserved LeanReceipt.currentR571LeanGateAReceipt

r571GateAA2LeanTheoremReceiptObserved : Bool
r571GateAA2LeanTheoremReceiptObserved =
  LeanReceipt.leanGateAA2ReceiptObserved LeanReceipt.currentR571LeanGateAReceipt

r571GateAA1AgdaSampleTransportObserved : Bool
r571GateAA1AgdaSampleTransportObserved =
  LeanReceipt.agdaGateAA1SampleTransportObserved LeanReceipt.currentR571LeanGateAReceipt

r571GateAA2AgdaSampleTransportObserved : Bool
r571GateAA2AgdaSampleTransportObserved =
  LeanReceipt.agdaGateAA2SampleTransportObserved LeanReceipt.currentR571LeanGateAReceipt

-- Historical field retained with its original meaning: the rational Agda
-- physical-family/sample theorem is not manufactured by the Lean receipt.
r571GateAA1PhysicalFamilyUniformBoundClosed : Bool
r571GateAA1PhysicalFamilyUniformBoundClosed = false

------------------------------------------------------------------------
-- G0'/G2/G1 state side.
------------------------------------------------------------------------

-- The local vector->scalar bridge is source-written: two literal rational C^3
-- samples are paired against the existing spectator via the R291
-- real-Hermitian functional and packaged into the old opposite R27 pair.
r571GateAG0HermitianScalarizedPairClosed : Bool
r571GateAG0HermitianScalarizedPairClosed =
  G0.r571HermitianScalarizedOppositePairClosed

r571GateAGlobalPhysicalScalarStateRequired : Bool
r571GateAGlobalPhysicalScalarStateRequired =
  G0.r571GlobalPhysicalScalarStateRequired

r571GateAG2ScalarDifferenceSameObjectClosed : Bool
r571GateAG2ScalarDifferenceSameObjectClosed =
  G2Local.round613G2ScalarDifferenceSameObjectClosed

r571GateAG2ReducedToLiteralVectorDifference : Bool
r571GateAG2ReducedToLiteralVectorDifference =
  G2Local.round613G2ReducedToLiteralVectorDifference

r571GateAG2FinitePathDonorLocated : Bool
r571GateAG2FinitePathDonorLocated = true

r571GateAG2PhysicalGradientCrosswalkClosed : Bool
r571GateAG2PhysicalGradientCrosswalkClosed = false

-- R579 now pays the local G1 magnitude step directly on the same G0'
-- Hermitian scalarization.  This is intentionally weaker than a cutoff-uniform
-- shifted-coefficient family envelope: it introduces no fibre sum or scale
-- constant, and leaves G2 untouched.
r571GateAG1LocalHermitianEnvelopeClosed : Bool
r571GateAG1LocalHermitianEnvelopeClosed =
  G1Local.r571LocalHermitianG1EnvelopeClosed

r571GateAG1LocalHermitianEnvelopeUsesSquareRoot : Bool
r571GateAG1LocalHermitianEnvelopeUsesSquareRoot =
  G1Local.r571LocalHermitianG1UsesSquareRoot

r571GateAG1ShiftedCoefficientEnvelopeClosed : Bool
r571GateAG1ShiftedCoefficientEnvelopeClosed = false

r571GateAStateDerivativeEnvelopeClosed : Bool
r571GateAStateDerivativeEnvelopeClosed = false

r571GateAA2DelegatedToRadialCurvatureBoundary : Bool
r571GateAA2DelegatedToRadialCurvatureBoundary = true

r571GateAFullPhysicalEnvelopePackageClosed : Bool
r571GateAFullPhysicalEnvelopePackageClosed = false

r571GateAClosesR568 : Bool
r571GateAClosesR568 = false
