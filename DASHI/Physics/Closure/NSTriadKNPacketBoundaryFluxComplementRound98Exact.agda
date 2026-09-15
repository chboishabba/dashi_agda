module DASHI.Physics.Closure.NSTriadKNPacketBoundaryFluxComplementRound98Exact where

------------------------------------------------------------------------
-- STRICT B-PHASE S2b2a / PACKET-COMPLEMENT FLUX ANTISYMMETRY
--
-- The live S2b1 layer-cake is written with upper-shell selectors, while the
-- existing R98 spectral cross-dissipation coercivity is oriented toward a
-- low-frequency selected packet whose complement is higher frequency.
--
-- This file pays only the finite sign bridge between those orientations.
-- For any Boolean selector chi, exact three-leg physical energy cancellation
-- gives
--
--   F(chi) + F(not chi) = 0,
--
-- hence F(not chi) = -F(chi), for the SAME normalized R98 boundary flux.
-- Specializing chi to upperShellPacket produces the complementary lower-shell
-- selector needed by the R98 coercive route.  No inequality, positivity,
-- residence estimate, Schur bound, or R406 payment is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; -_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalTriadEnergyRound37Exact as TriadEnergy
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as Round38
import DASHI.Physics.Closure.NSTriadKNPhysicalPacketBoundaryFluxRound96Exact as R96
import DASHI.Physics.Closure.NSTriadKNPacketBoundaryFluxNormalizationRound98Exact as R98
import DASHI.Physics.Closure.NSTriadKNLiteralUpperShellPacketSelectorExact as Upper

F : C3.RealField _
F = Rational.rationalRealField

boolNot : Bool → Bool
boolNot true = false
boolNot false = true

complementSelector :
  (Z3.FourierMode → Bool) → Z3.FourierMode → Bool
complementSelector selected mode = boolNot (selected mode)

lowerShellPacket : Nat → Z3.FourierMode → Bool
lowerShellPacket shell = complementSelector (Upper.upperShellPacket shell)

threeLegOrderedPowerZero :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  (tau : Physical.PhysicalTriadIncidence) →
  Round38.orderedPairPower E I tau velocity
    + Round38.orderedPairPower E I (Orbit.pEnergyLeg tau) velocity
    + Round38.orderedPairPower E I (Orbit.qEnergyLeg tau) velocity
  ≡ 0ℚ
threeLegOrderedPowerZero E I velocity reality divergenceFree tau =
  trans
    (sym (Round38.threeLegPowerIsPairOrbitSum E I tau velocity))
    (TriadEnergy.literalPhysicalTriadPowerZero
      E I tau velocity reality divergenceFree)

boundaryTriadComplementSumZero :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  (tau : Physical.PhysicalTriadIncidence) →
  R96.boundaryTriadTransfer E I selected velocity tau
    + R96.boundaryTriadTransfer E I
        (complementSelector selected) velocity tau
  ≡ 0ℚ
boundaryTriadComplementSumZero
    E I selected velocity reality divergenceFree tau
  with selected (Physical.k tau)
     | selected (Physical.p tau)
     | selected (Physical.q tau)
... | true | true | true = refl
... | false | false | false = refl
... | true | true | false = normalizeThenCancel
... | true | false | true = normalizeThenCancel
... | false | true | true = normalizeThenCancel
... | true | false | false = normalizeThenCancel
... | false | true | false = normalizeThenCancel
... | false | false | true = normalizeThenCancel
  where
  a = Round38.orderedPairPower E I tau velocity
  b = Round38.orderedPairPower E I (Orbit.pEnergyLeg tau) velocity
  c = Round38.orderedPairPower E I (Orbit.qEnergyLeg tau) velocity

  normalizeThenCancel :
    R96.boundaryTriadTransfer E I selected velocity tau
      + R96.boundaryTriadTransfer E I
          (complementSelector selected) velocity tau
    ≡ 0ℚ
  normalizeThenCancel =
    trans
      (solve (a ∷ b ∷ c ∷ []))
      (threeLegOrderedPowerZero E I velocity reality divergenceFree tau)

sumBoundaryComplementZero :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  (triads : List Physical.PhysicalTriadIncidence) →
  R96.sumBoundaryTransfer E I selected velocity triads
    + R96.sumBoundaryTransfer E I
        (complementSelector selected) velocity triads
  ≡ 0ℚ
sumBoundaryComplementZero
    E I selected velocity reality divergenceFree [] = refl
sumBoundaryComplementZero
    E I selected velocity reality divergenceFree (tau ∷ rest) =
  let
    head = boundaryTriadComplementSumZero
      E I selected velocity reality divergenceFree tau
    tail = sumBoundaryComplementZero
      E I selected velocity reality divergenceFree rest
  in
  rewrite head | tail = solve []

normalizedBoundaryComplementSumZero :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  (cutoff : Nat) →
  R98.normalizedBoundaryTransfer E I selected velocity cutoff
    + R98.normalizedBoundaryTransfer E I
        (complementSelector selected) velocity cutoff
  ≡ 0ℚ
normalizedBoundaryComplementSumZero
    E I selected velocity reality divergenceFree cutoff =
  let
    triads = Physical.physicalTriadEnumeration cutoff
    leftRaw = R96.sumBoundaryTransfer E I selected velocity triads
    rightRaw = R96.sumBoundaryTransfer E I
      (complementSelector selected) velocity triads
    rawZero : leftRaw + rightRaw ≡ 0ℚ
    rawZero = sumBoundaryComplementZero
      E I selected velocity reality divergenceFree triads
    factor :
      R98.oneSixth * leftRaw + R98.oneSixth * rightRaw
      ≡ R98.oneSixth * (leftRaw + rightRaw)
    factor = solve (leftRaw ∷ rightRaw ∷ [])
  in
  trans factor
    (trans
      (cong (R98.oneSixth *_) rawZero)
      (solve []))

sumZeroGivesRightNegative :
  (left right : ℚ) → left + right ≡ 0ℚ → right ≡ - left
sumZeroGivesRightNegative left right zero =
  let shifted = cong (λ value → value + (- left)) zero
  in
  trans
    (solve (left ∷ right ∷ []))
    (trans shifted (solve (left ∷ [])))

normalizedBoundaryComplementAntisymmetry :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  (cutoff : Nat) →
  R98.normalizedBoundaryTransfer E I
      (complementSelector selected) velocity cutoff
  ≡ - R98.normalizedBoundaryTransfer E I selected velocity cutoff
normalizedBoundaryComplementAntisymmetry
    E I selected velocity reality divergenceFree cutoff =
  sumZeroGivesRightNegative
    (R98.normalizedBoundaryTransfer E I selected velocity cutoff)
    (R98.normalizedBoundaryTransfer E I
      (complementSelector selected) velocity cutoff)
    (normalizedBoundaryComplementSumZero
      E I selected velocity reality divergenceFree cutoff)

lowerShellBoundaryFluxIsNegativeUpperShellFlux :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (shell : Nat) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  (cutoff : Nat) →
  R98.normalizedBoundaryTransfer E I
      (lowerShellPacket shell) velocity cutoff
  ≡ - R98.normalizedBoundaryTransfer E I
      (Upper.upperShellPacket shell) velocity cutoff
lowerShellBoundaryFluxIsNegativeUpperShellFlux
    E I shell velocity reality divergenceFree cutoff =
  normalizedBoundaryComplementAntisymmetry
    E I (Upper.upperShellPacket shell) velocity
    reality divergenceFree cutoff

packetComplementAntisymmetryClosed : Bool
packetComplementAntisymmetryClosed = true

upperLowerShellBoundaryFluxOppositionClosed : Bool
upperLowerShellBoundaryFluxOppositionClosed = true

s2b2QuantitativePacketFluxEstimateClosed : Bool
s2b2QuantitativePacketFluxEstimateClosed = false

packetComplementAntisymmetryClosedIsTrue :
  packetComplementAntisymmetryClosed ≡ true
packetComplementAntisymmetryClosedIsTrue = refl

upperLowerShellBoundaryFluxOppositionClosedIsTrue :
  upperLowerShellBoundaryFluxOppositionClosed ≡ true
upperLowerShellBoundaryFluxOppositionClosedIsTrue = refl

s2b2QuantitativePacketFluxEstimateClosedIsFalse :
  s2b2QuantitativePacketFluxEstimateClosed ≡ false
s2b2QuantitativePacketFluxEstimateClosedIsFalse = refl
