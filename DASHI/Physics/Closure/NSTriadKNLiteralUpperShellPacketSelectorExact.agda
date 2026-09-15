module DASHI.Physics.Closure.NSTriadKNLiteralUpperShellPacketSelectorExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S2b1b1 / LITERAL UPPER-SHELL SELECTOR -> R98 FLUX
--
-- The S0/S2b route uses the executable dyadic max-norm shellIndex.  R98 does
-- not require the older Euclidean-squared packet selector: its physical
-- packet/boundary-flux theorem accepts an arbitrary Boolean mode selector.
--
-- Define the literal upper-shell packet directly by
--
--   selected_j(k) = (k /= 0) AND (j <= shellIndex k).
--
-- The explicit nonzero guard makes the selector compatible with both R98's
-- full cutoffModes list and the live R34/R240 nonzeroCutoffModes list.  Using
-- the S2b1a permutation theorem, the same selected pairing may then be read on
-- the radially sorted live carrier and transported by R98 to normalized
-- physical boundary flux.
--
-- This file still does NOT prove that a structural tail of R104's sorted band
-- list is exactly this selector fold at each positive radial increment.  That
-- finite tail/selector identity is the remaining S2b1b representation seam.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Properties using (_≤?_)
open import Data.Rational.Base using (ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as R34
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNSelectedPacketProjectedPairingRound98Exact as R98
import DASHI.Physics.Closure.NSTriadKNPacketBoundaryFluxNormalizationRound98Exact as Norm
import DASHI.Physics.Closure.NSTriadKNSelectedPacketNonzeroCutoffBridgeExact as Nonzero
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionRadialOrderExact as Radial

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- Literal dyadic upper-shell selector.
------------------------------------------------------------------------

upperShellPacket : Nat → Z3.FourierMode → Bool
upperShellPacket threshold mode
  with Output.modeEqual mode Z3.zeroMode
     | threshold ≤? Shell.shellIndex mode
... | true | _ = false
... | false | yes proof = true
... | false | no refutation = false

upperShellPacketRejectsZero :
  (threshold : Nat) →
  Nonzero.RejectsZero (upperShellPacket threshold)
upperShellPacketRejectsZero threshold
  rewrite Output.modeEqualRefl Z3.zeroMode = refl

------------------------------------------------------------------------
-- Selected projected-pairing folds respect exact finite reindexing.
------------------------------------------------------------------------

sumSelectedProjectedPairingsRespPermutation :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (selected : Z3.FourierMode → Bool) →
  {left right : List Z3.FourierMode} →
  left Perm.↭ right →
  R98.sumSelectedProjectedPairings system selected left
  ≡ R98.sumSelectedProjectedPairings system selected right
sumSelectedProjectedPairingsRespPermutation system selected Perm.refl = refl
sumSelectedProjectedPairingsRespPermutation system selected
    (Perm.prep mode permutation) =
  cong
    (R98.selectedProjectedOutputPower system selected mode +_)
    (sumSelectedProjectedPairingsRespPermutation
      system selected permutation)
sumSelectedProjectedPairingsRespPermutation system selected
    (Perm.swap {xs = xs} left right permutation) =
  let
    leftPower = R98.selectedProjectedOutputPower system selected left
    rightPower = R98.selectedProjectedOutputPower system selected right
    tailRight = R98.sumSelectedProjectedPairings system selected _
  in
  trans
    (cong
      (λ tail → leftPower + (rightPower + tail))
      (sumSelectedProjectedPairingsRespPermutation
        system selected permutation))
    (solve
      ( leftPower ∷ rightPower
      ∷ R98.sumSelectedProjectedPairings system selected _ ∷ [] ))
sumSelectedProjectedPairingsRespPermutation system selected
    (Perm.trans first second) =
  trans
    (sumSelectedProjectedPairingsRespPermutation system selected first)
    (sumSelectedProjectedPairingsRespPermutation system selected second)

------------------------------------------------------------------------
-- R98 full cutoff -> live nonzero cutoff -> S2b1a radial order.
------------------------------------------------------------------------

literalUpperShellPacketEqualsSortedNonzeroFold :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (threshold : Nat) →
  R98.literalSelectedProjectedPairing system (upperShellPacket threshold)
  ≡ R98.sumSelectedProjectedPairings system (upperShellPacket threshold)
      (Radial.sortByShell
        (R34.nonzeroCutoffModes (Audit.cutoff system)))
literalUpperShellPacketEqualsSortedNonzeroFold system threshold =
  let
    selected = upperShellPacket threshold
    nonzeroModes = R34.nonzeroCutoffModes (Audit.cutoff system)
  in
  trans
    (Nonzero.literalSelectedProjectedPairingEqualsNonzeroCutoffPairing
      system selected (upperShellPacketRejectsZero threshold))
    (sym
      (sumSelectedProjectedPairingsRespPermutation
        system selected (Radial.sortByShellPermutation nonzeroModes)))

sortedNonzeroUpperShellFoldIsNormalizedBoundaryFlux :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (threshold : Nat) →
  Reality.RealityCondition (Audit.velocity system) →
  Reality.DivergenceFreeCondition E (Audit.velocity system) →
  R98.sumSelectedProjectedPairings system (upperShellPacket threshold)
      (Radial.sortByShell
        (R34.nonzeroCutoffModes (Audit.cutoff system)))
  ≡ Norm.normalizedBoundaryTransfer
      E I (upperShellPacket threshold)
      (Audit.velocity system) (Audit.cutoff system)
sortedNonzeroUpperShellFoldIsNormalizedBoundaryFlux
    {E} {I} system threshold reality divergenceFree =
  trans
    (sym (literalUpperShellPacketEqualsSortedNonzeroFold system threshold))
    (R98.literalSelectedProjectedPairingIsNormalizedBoundaryFlux
      system (upperShellPacket threshold) reality divergenceFree)

------------------------------------------------------------------------
-- Status / remaining exact seam.
------------------------------------------------------------------------

literalUpperShellSelectorConstructed : Bool
literalUpperShellSelectorConstructed = true

literalUpperShellSelectorRejectsZeroClosed : Bool
literalUpperShellSelectorRejectsZeroClosed = true

selectedProjectedPairingPermutationInvariantClosed : Bool
selectedProjectedPairingPermutationInvariantClosed = true

literalUpperShellSelectorR98TransportClosed : Bool
literalUpperShellSelectorR98TransportClosed = true

r104StructuralSuffixEqualsUpperShellSelectorClosed : Bool
r104StructuralSuffixEqualsUpperShellSelectorClosed = false

literalUpperShellSelectorConstructedIsTrue :
  literalUpperShellSelectorConstructed ≡ true
literalUpperShellSelectorConstructedIsTrue = refl

literalUpperShellSelectorRejectsZeroClosedIsTrue :
  literalUpperShellSelectorRejectsZeroClosed ≡ true
literalUpperShellSelectorRejectsZeroClosedIsTrue = refl

selectedProjectedPairingPermutationInvariantClosedIsTrue :
  selectedProjectedPairingPermutationInvariantClosed ≡ true
selectedProjectedPairingPermutationInvariantClosedIsTrue = refl

literalUpperShellSelectorR98TransportClosedIsTrue :
  literalUpperShellSelectorR98TransportClosed ≡ true
literalUpperShellSelectorR98TransportClosedIsTrue = refl

r104StructuralSuffixEqualsUpperShellSelectorClosedIsFalse :
  r104StructuralSuffixEqualsUpperShellSelectorClosed ≡ false
r104StructuralSuffixEqualsUpperShellSelectorClosedIsFalse = refl
