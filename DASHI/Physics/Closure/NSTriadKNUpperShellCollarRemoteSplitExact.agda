module DASHI.Physics.Closure.NSTriadKNUpperShellCollarRemoteSplitExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S2b2b / EXACT COLLAR-REMOTE PACKET SPLIT
--
-- After S2b1, the literal critical-production layer-cake is written on the
-- exact R98 upper-shell packet
--
--   upper_j(k) = [k /= 0] AND [j <= shellIndex(k)].
--
-- The adjacent-shell spectral-gap route is false on this max-norm shell
-- geometry.  The correct next move is therefore to split the SAME packet into
--
--   upper_j = collar_j disjoint-union upper_{j+1},
--
-- and hence, on the SAME normalized physical R98 boundary-flux carrier,
--
--   F_{>=j} = F_{=j} + F_{>=j+1}.
--
-- This file proves only that finite same-object decomposition.  It introduces
-- no estimate, positivity, Euclidean shell identification, Schur majorant, or
-- R406 payment.  The remote and collar quantitative estimates remain S2b2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Properties using (_≤?_; n≤1+n; ≤-trans)
open import Data.Rational.Base using (ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLiteralUpperShellPacketSelectorExact as Upper
import DASHI.Physics.Closure.NSTriadKNSelectedPacketProjectedPairingRound98Exact as R98
import DASHI.Physics.Closure.NSTriadKNPacketBoundaryFluxNormalizationRound98Exact as Norm
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- Exact-shell collar selector.
------------------------------------------------------------------------

collarShellPacket : Nat → Z3.FourierMode → Bool
collarShellPacket threshold mode
  with Upper.upperShellPacket threshold mode
     | Upper.upperShellPacket (suc threshold) mode
... | true | false = true
... | _ | _ = false

-- The only monotonicity fact needed by the partition: membership in the
-- successor upper packet implies membership in the current upper packet.
upperSuccessorTrueImpliesUpperTrue :
  (threshold : Nat) →
  (mode : Z3.FourierMode) →
  Upper.upperShellPacket (suc threshold) mode ≡ true →
  Upper.upperShellPacket threshold mode ≡ true
upperSuccessorTrueImpliesUpperTrue threshold mode successorTrue
  with Output.modeEqual mode Z3.zeroMode
     | threshold ≤? Shell.shellIndex mode
     | suc threshold ≤? Shell.shellIndex mode
... | true | _ | _ = ⊥-elim (Output.falseNotTrue successorTrue)
... | false | yes threshold≤ | yes successor≤ = refl
... | false | yes threshold≤ | no successor≰ =
  ⊥-elim (successor≰ (Output.falseNotTrue successorTrue))
... | false | no threshold≰ | yes successor≤ =
  ⊥-elim
    (threshold≰
      (≤-trans (n≤1+n threshold) successor≤))
... | false | no threshold≰ | no successor≰ =
  ⊥-elim (successor≰ (Output.falseNotTrue successorTrue))

------------------------------------------------------------------------
-- Pointwise and finite selected-pairing split.
------------------------------------------------------------------------

selectedProjectedOutputPowerCollarRemoteSplit :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (threshold : Nat) →
  (output : Z3.FourierMode) →
  R98.selectedProjectedOutputPower
      system (Upper.upperShellPacket threshold) output
  ≡ R98.selectedProjectedOutputPower
      system (collarShellPacket threshold) output
    + R98.selectedProjectedOutputPower
      system (Upper.upperShellPacket (suc threshold)) output
selectedProjectedOutputPowerCollarRemoteSplit
    system threshold output
  with Upper.upperShellPacket threshold output in currentEq
     | Upper.upperShellPacket (suc threshold) output in successorEq
... | false | false = solve []
... | true | false =
  solve
    (R98.OutputPairing.realHermitianPower
      (Audit.velocity system output)
      (Audit.projectedNonlinearity system output) ∷ [])
... | true | true =
  solve
    (R98.OutputPairing.realHermitianPower
      (Audit.velocity system output)
      (Audit.projectedNonlinearity system output) ∷ [])
... | false | true =
  ⊥-elim
    (Output.falseNotTrue
      (trans (sym currentEq)
        (upperSuccessorTrueImpliesUpperTrue
          threshold output successorEq)))

sumSelectedProjectedPairingsCollarRemoteSplit :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (threshold : Nat) →
  (outputs : List Z3.FourierMode) →
  R98.sumSelectedProjectedPairings
      system (Upper.upperShellPacket threshold) outputs
  ≡ R98.sumSelectedProjectedPairings
      system (collarShellPacket threshold) outputs
    + R98.sumSelectedProjectedPairings
      system (Upper.upperShellPacket (suc threshold)) outputs
sumSelectedProjectedPairingsCollarRemoteSplit system threshold [] = solve []
sumSelectedProjectedPairingsCollarRemoteSplit
    system threshold (output ∷ rest) =
  let
    head = selectedProjectedOutputPowerCollarRemoteSplit
      system threshold output
    tail = sumSelectedProjectedPairingsCollarRemoteSplit
      system threshold rest
  in
  rewrite head | tail =
    solve
      ( R98.selectedProjectedOutputPower
          system (collarShellPacket threshold) output
      ∷ R98.selectedProjectedOutputPower
          system (Upper.upperShellPacket (suc threshold)) output
      ∷ R98.sumSelectedProjectedPairings
          system (collarShellPacket threshold) rest
      ∷ R98.sumSelectedProjectedPairings
          system (Upper.upperShellPacket (suc threshold)) rest
      ∷ [])

literalSelectedProjectedPairingCollarRemoteSplit :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (threshold : Nat) →
  R98.literalSelectedProjectedPairing
      system (Upper.upperShellPacket threshold)
  ≡ R98.literalSelectedProjectedPairing
      system (collarShellPacket threshold)
    + R98.literalSelectedProjectedPairing
      system (Upper.upperShellPacket (suc threshold))
literalSelectedProjectedPairingCollarRemoteSplit system threshold =
  sumSelectedProjectedPairingsCollarRemoteSplit
    system threshold (Cube.cutoffModes (Audit.cutoff system))

------------------------------------------------------------------------
-- SAME normalized physical boundary-flux split.
------------------------------------------------------------------------

normalizedBoundaryFluxCollarRemoteSplit :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (threshold : Nat) →
  Reality.RealityCondition (Audit.velocity system) →
  Reality.DivergenceFreeCondition E (Audit.velocity system) →
  Norm.normalizedBoundaryTransfer
      E I (Upper.upperShellPacket threshold)
      (Audit.velocity system) (Audit.cutoff system)
  ≡ Norm.normalizedBoundaryTransfer
      E I (collarShellPacket threshold)
      (Audit.velocity system) (Audit.cutoff system)
    + Norm.normalizedBoundaryTransfer
      E I (Upper.upperShellPacket (suc threshold))
      (Audit.velocity system) (Audit.cutoff system)
normalizedBoundaryFluxCollarRemoteSplit
    {E} {I} system threshold reality divergenceFree =
  let
    whole = R98.literalSelectedProjectedPairingIsNormalizedBoundaryFlux
      system (Upper.upperShellPacket threshold) reality divergenceFree
    collar = R98.literalSelectedProjectedPairingIsNormalizedBoundaryFlux
      system (collarShellPacket threshold) reality divergenceFree
    remote = R98.literalSelectedProjectedPairingIsNormalizedBoundaryFlux
      system (Upper.upperShellPacket (suc threshold)) reality divergenceFree
    split = literalSelectedProjectedPairingCollarRemoteSplit system threshold
  in
  trans (sym whole)
    (trans split (cong₂ _+_ collar remote))

------------------------------------------------------------------------
-- Status: decomposition closed, quantitative theorem still open.
------------------------------------------------------------------------

collarRemoteSelectorSplitClosed : Bool
collarRemoteSelectorSplitClosed = true

collarRemoteBoundaryFluxSplitClosed : Bool
collarRemoteBoundaryFluxSplitClosed = true

s2b2QuantitativeEstimateStillOpen : Bool
s2b2QuantitativeEstimateStillOpen = true

collarRemoteSelectorSplitClosedIsTrue :
  collarRemoteSelectorSplitClosed ≡ true
collarRemoteSelectorSplitClosedIsTrue = refl

collarRemoteBoundaryFluxSplitClosedIsTrue :
  collarRemoteBoundaryFluxSplitClosed ≡ true
collarRemoteBoundaryFluxSplitClosedIsTrue = refl

s2b2QuantitativeEstimateStillOpenIsTrue :
  s2b2QuantitativeEstimateStillOpen ≡ true
s2b2QuantitativeEstimateStillOpenIsTrue = refl
