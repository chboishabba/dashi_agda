module DASHI.Physics.Closure.NSTriadKNSelectedPacketNonzeroCutoffBridgeExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S2b1b0 / R98 FULL-CUTOFF -> LIVE NONZERO-CUTOFF BRIDGE
--
-- R98's literal selected projected pairing is intentionally stated over the
-- complete concrete cutoff cube, while the canonical R34/R240 finite system
-- retains exactly the nonzero cutoff modes.  For any selector that rejects the
-- zero mode, those two selected folds are exactly the same: R34.removeZero
-- deletes only terms whose R98 selectTransfer is already zero.
--
-- This is finite same-object plumbing only.  It introduces no replacement
-- production scalar, no radial estimate, and no assumption that max-norm
-- shells equal Euclidean-squared packets.  S2b1b still has to identify a
-- literal radial suffix selector with the corresponding selected nonzero fold.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as R34
import DASHI.Physics.Closure.NSTriadKNSelectedPacketProjectedPairingRound98Exact as R98

F : C3.RealField _
F = Rational.rationalRealField

RejectsZero : (Z3.FourierMode → Bool) → Set
RejectsZero selected = selected Z3.zeroMode ≡ false

selectedProjectedPowerAtRemovedZeroIsZero :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (selected : Z3.FourierMode → Bool) →
  RejectsZero selected →
  (mode : Z3.FourierMode) →
  Output.modeEqual mode Z3.zeroMode ≡ true →
  R98.selectedProjectedOutputPower system selected mode ≡ 0ℚ
selectedProjectedPowerAtRemovedZeroIsZero
    system selected rejectsZero mode modeIsZero =
  let
    selectedModeIsFalse : selected mode ≡ false
    selectedModeIsFalse =
      trans
        (cong selected (Output.modeEqualSound modeIsZero))
        rejectsZero
  in
  rewrite selectedModeIsFalse = refl

sumSelectedProjectedPairingsRemoveZero :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (selected : Z3.FourierMode → Bool) →
  RejectsZero selected →
  (modes : List Z3.FourierMode) →
  R98.sumSelectedProjectedPairings system selected modes
  ≡ R98.sumSelectedProjectedPairings system selected (R34.removeZero modes)
sumSelectedProjectedPairingsRemoveZero system selected rejectsZero [] = refl
sumSelectedProjectedPairingsRemoveZero
    system selected rejectsZero (mode ∷ rest)
  with Output.modeEqual mode Z3.zeroMode in modeEqual
... | true =
  trans
    (cong₂ _+_
      (selectedProjectedPowerAtRemovedZeroIsZero
        system selected rejectsZero mode modeEqual)
      (sumSelectedProjectedPairingsRemoveZero
        system selected rejectsZero rest))
    (solve
      ( R98.sumSelectedProjectedPairings
          system selected (R34.removeZero rest)
      ∷ [] ))
... | false =
  cong
    (R98.selectedProjectedOutputPower system selected mode +_)
    (sumSelectedProjectedPairingsRemoveZero
      system selected rejectsZero rest)

literalSelectedProjectedPairingEqualsNonzeroCutoffPairing :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (selected : Z3.FourierMode → Bool) →
  RejectsZero selected →
  R98.literalSelectedProjectedPairing system selected
  ≡ R98.sumSelectedProjectedPairings system selected
      (R34.nonzeroCutoffModes (Audit.cutoff system))
literalSelectedProjectedPairingEqualsNonzeroCutoffPairing
    system selected rejectsZero =
  sumSelectedProjectedPairingsRemoveZero
    system selected rejectsZero
    (Cube.cutoffModes (Audit.cutoff system))

rejectZeroSelectorFullToNonzeroCutoffClosed : Bool
rejectZeroSelectorFullToNonzeroCutoffClosed = true

nonzeroCutoffBridgeIntroducesNoNewProductionScalar : Bool
nonzeroCutoffBridgeIntroducesNoNewProductionScalar = true

rejectZeroSelectorFullToNonzeroCutoffClosedIsTrue :
  rejectZeroSelectorFullToNonzeroCutoffClosed ≡ true
rejectZeroSelectorFullToNonzeroCutoffClosedIsTrue = refl

nonzeroCutoffBridgeIntroducesNoNewProductionScalarIsTrue :
  nonzeroCutoffBridgeIntroducesNoNewProductionScalar ≡ true
nonzeroCutoffBridgeIntroducesNoNewProductionScalarIsTrue = refl
