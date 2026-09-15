module DASHI.Physics.Closure.NSTriadKNLiteralUpperShellCanonicalSuffixExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S2b1b2a / UPPER-SHELL SELECTOR -> CANONICAL SORTED SUFFIX
--
-- S2b1b1 transports the literal upperShellPacket selector through R98 to
-- normalized physical boundary flux.  The remaining finite question is which
-- part of the sorted nonzero carrier that selector sums.
--
-- This file defines the canonical suffix by dropping every leading sorted mode
-- whose shell index is below the threshold.  On a ShellOrdered, all-nonzero
-- list it proves exactly
--
--   selectedPairing(upperShellPacket j, modes)
--     = rawProjectedPairing(dropBelowShell j modes).
--
-- Specializing to sortByShell(nonzeroCutoffModes N) and composing with S2b1b1
-- therefore identifies that canonical suffix with R98 normalized physical
-- boundary flux.  No estimate, absolute value, Euclidean/max-norm conversion,
-- or replacement scalar is introduced.
--
-- One representation seam remains: prove that every structural suffix used by
-- R104.radialLayerCake at a genuine shell jump is this canonical drop-suffix.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (_≤_)
open import Data.Nat.Properties using (_≤?_; ≤-trans)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as R34
import DASHI.Physics.Closure.NSTriadKNLiteralNonzeroCutoffSupportRound404Exact as R404
import DASHI.Physics.Closure.NSTriadKNF4ProjectedOutputPairingRound39Exact as R39
import DASHI.Physics.Closure.NSTriadKNSelectedPacketProjectedPairingRound98Exact as R98
import DASHI.Physics.Closure.NSTriadKNPacketBoundaryFluxNormalizationRound98Exact as Norm
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionBandTransferExact as S2b0
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionRadialOrderExact as Radial
import DASHI.Physics.Closure.NSTriadKNLiteralUpperShellPacketSelectorExact as Upper
import DASHI.Physics.Closure.NSTriadKNCriticalProductionPacketLayerCakeRound104Exact as LayerCake

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- All-nonzero witness for literal/sorted carriers.
------------------------------------------------------------------------

data AllNonzero : List Z3.FourierMode → Set where
  allNonzero[] : AllNonzero []
  allNonzero∷ : ∀ {mode rest} →
    Z3.NonZeroMode mode →
    AllNonzero rest →
    AllNonzero (mode ∷ rest)

pointwiseNonzeroToAll :
  (modes : List Z3.FourierMode) →
  (∀ mode → mode Cube.∈ modes → Z3.NonZeroMode mode) →
  AllNonzero modes
pointwiseNonzeroToAll [] pointwise = allNonzero[]
pointwiseNonzeroToAll (mode ∷ rest) pointwise =
  allNonzero∷
    (pointwise mode (Cube.here refl))
    (pointwiseNonzeroToAll rest
      (λ selected member → pointwise selected (Cube.there member)))

literalNonzeroCutoffAllNonzero :
  (cutoff : Nat) → AllNonzero (R34.nonzeroCutoffModes cutoff)
literalNonzeroCutoffAllNonzero cutoff =
  pointwiseNonzeroToAll
    (R34.nonzeroCutoffModes cutoff)
    (λ mode member → R404.nonzeroCutoffMemberNonzero member)

insertPreservesAllNonzero :
  (mode : Z3.FourierMode) →
  Z3.NonZeroMode mode →
  ∀ {modes} → AllNonzero modes →
  AllNonzero (Radial.insertByShell mode modes)
insertPreservesAllNonzero mode modeNonzero allNonzero[] =
  allNonzero∷ modeNonzero allNonzero[]
insertPreservesAllNonzero mode modeNonzero
    (allNonzero∷ {mode = head} headNonzero restNonzero)
  with Shell.shellIndex mode ≤? Shell.shellIndex head
... | yes proof =
  allNonzero∷ modeNonzero (allNonzero∷ headNonzero restNonzero)
... | no refutation =
  allNonzero∷ headNonzero
    (insertPreservesAllNonzero mode modeNonzero restNonzero)

sortPreservesAllNonzero :
  ∀ {modes} → AllNonzero modes → AllNonzero (Radial.sortByShell modes)
sortPreservesAllNonzero allNonzero[] = allNonzero[]
sortPreservesAllNonzero
    (allNonzero∷ {mode = mode} modeNonzero restNonzero) =
  insertPreservesAllNonzero mode modeNonzero
    (sortPreservesAllNonzero restNonzero)

allNonzeroTail :
  ∀ {mode rest} → AllNonzero (mode ∷ rest) → AllNonzero rest
allNonzeroTail (allNonzero∷ modeNonzero restNonzero) = restNonzero

------------------------------------------------------------------------
-- Ordered lower/upper split.
------------------------------------------------------------------------

data AllAtOrAbove (threshold : Nat) : List Z3.FourierMode → Set where
  allAbove[] : AllAtOrAbove threshold []
  allAbove∷ : ∀ {mode rest} →
    threshold ≤ Shell.shellIndex mode →
    AllAtOrAbove threshold rest →
    AllAtOrAbove threshold (mode ∷ rest)

orderedAllAtOrAbove :
  ∀ {threshold mode rest} →
  threshold ≤ Shell.shellIndex mode →
  Radial.ShellOrdered (mode ∷ rest) →
  AllAtOrAbove threshold (mode ∷ rest)
orderedAllAtOrAbove threshold≤mode Radial.ordered1 =
  allAbove∷ threshold≤mode allAbove[]
orderedAllAtOrAbove threshold≤mode
    (Radial.ordered∷ mode≤next tailOrdered) =
  allAbove∷ threshold≤mode
    (orderedAllAtOrAbove
      (≤-trans threshold≤mode mode≤next)
      tailOrdered)

shellOrderedTail :
  ∀ {mode rest} →
  Radial.ShellOrdered (mode ∷ rest) →
  Radial.ShellOrdered rest
shellOrderedTail Radial.ordered1 = Radial.ordered[]
shellOrderedTail (Radial.ordered∷ mode≤next tailOrdered) = tailOrdered

upperShellPacketTrue :
  (threshold : Nat) →
  (mode : Z3.FourierMode) →
  Z3.NonZeroMode mode →
  threshold ≤ Shell.shellIndex mode →
  Upper.upperShellPacket threshold mode ≡ true
upperShellPacketTrue threshold mode modeNonzero threshold≤
  with Output.modeEqual mode Z3.zeroMode in zeroDecision
     | threshold ≤? Shell.shellIndex mode in shellDecision
... | true | _ =
  ⊥-elim (Z3.notZero modeNonzero (Output.modeEqualSound zeroDecision))
... | false | yes proof = refl
... | false | no refutation = ⊥-elim (refutation threshold≤)

upperShellPacketFalseBelow :
  (threshold : Nat) →
  (mode : Z3.FourierMode) →
  Z3.NonZeroMode mode →
  (threshold ≤ Shell.shellIndex mode → ⊥) →
  Upper.upperShellPacket threshold mode ≡ false
upperShellPacketFalseBelow threshold mode modeNonzero below
  with Output.modeEqual mode Z3.zeroMode in zeroDecision
     | threshold ≤? Shell.shellIndex mode in shellDecision
... | true | _ =
  ⊥-elim (Z3.notZero modeNonzero (Output.modeEqualSound zeroDecision))
... | false | yes proof = ⊥-elim (below proof)
... | false | no refutation = refl

------------------------------------------------------------------------
-- Raw unweighted projected pairing and R104 transfer meaning.
------------------------------------------------------------------------

rawProjectedPairing :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Z3.FourierMode → ℚ
rawProjectedPairing system [] = 0ℚ
rawProjectedPairing system (mode ∷ rest) =
  R39.realHermitianPower
    (Audit.velocity system mode)
    (Audit.projectedNonlinearity system mode)
  + rawProjectedPairing system rest

literalBandTotalTransferIsRawPairing :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (modes : List Z3.FourierMode) →
  LayerCake.totalTransfer (S2b0.literalBandTransfers system modes)
  ≡ rawProjectedPairing system modes
literalBandTotalTransferIsRawPairing system [] = refl
literalBandTotalTransferIsRawPairing system (mode ∷ rest) =
  cong
    (R39.realHermitianPower
      (Audit.velocity system mode)
      (Audit.projectedNonlinearity system mode) +_)
    (literalBandTotalTransferIsRawPairing system rest)

selectedAllAboveIsRawPairing :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (threshold : Nat) →
  (modes : List Z3.FourierMode) →
  AllNonzero modes →
  AllAtOrAbove threshold modes →
  R98.sumSelectedProjectedPairings system (Upper.upperShellPacket threshold) modes
  ≡ rawProjectedPairing system modes
selectedAllAboveIsRawPairing system threshold []
    allNonzero[] allAbove[] = refl
selectedAllAboveIsRawPairing system threshold (mode ∷ rest)
    (allNonzero∷ modeNonzero restNonzero)
    (allAbove∷ threshold≤mode restAbove)
  rewrite upperShellPacketTrue threshold mode modeNonzero threshold≤mode =
  cong
    (R39.realHermitianPower
      (Audit.velocity system mode)
      (Audit.projectedNonlinearity system mode) +_)
    (selectedAllAboveIsRawPairing
      system threshold rest restNonzero restAbove)

------------------------------------------------------------------------
-- Canonical sorted suffix selected by shell threshold.
------------------------------------------------------------------------

dropBelowShell : Nat → List Z3.FourierMode → List Z3.FourierMode
dropBelowShell threshold [] = []
dropBelowShell threshold (mode ∷ rest)
  with threshold ≤? Shell.shellIndex mode
... | yes proof = mode ∷ rest
... | no refutation = dropBelowShell threshold rest

upperShellSelectedFoldIsCanonicalSuffix :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (threshold : Nat) →
  (modes : List Z3.FourierMode) →
  Radial.ShellOrdered modes →
  AllNonzero modes →
  R98.sumSelectedProjectedPairings system (Upper.upperShellPacket threshold) modes
  ≡ rawProjectedPairing system (dropBelowShell threshold modes)
upperShellSelectedFoldIsCanonicalSuffix
    system threshold [] Radial.ordered[] allNonzero[] = refl
upperShellSelectedFoldIsCanonicalSuffix
    system threshold (mode ∷ rest) ordered
    (allNonzero∷ modeNonzero restNonzero)
  with threshold ≤? Shell.shellIndex mode in shellDecision
... | yes threshold≤mode =
  selectedAllAboveIsRawPairing
    system threshold (mode ∷ rest)
    (allNonzero∷ modeNonzero restNonzero)
    (orderedAllAtOrAbove threshold≤mode ordered)
... | no below =
  let
    selectedModeFalse =
      upperShellPacketFalseBelow threshold mode modeNonzero below
    tailIdentity =
      upperShellSelectedFoldIsCanonicalSuffix
        system threshold rest
        (shellOrderedTail ordered)
        restNonzero
  in
  rewrite selectedModeFalse | tailIdentity =
    solve
      ( rawProjectedPairing system
          (dropBelowShell threshold rest)
      ∷ [] )

sortedNonzeroUpperShellFoldIsCanonicalSuffix :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (threshold : Nat) →
  R98.sumSelectedProjectedPairings system (Upper.upperShellPacket threshold)
      (Radial.sortByShell
        (R34.nonzeroCutoffModes (Audit.cutoff system)))
  ≡ rawProjectedPairing system
      (dropBelowShell threshold
        (Radial.sortByShell
          (R34.nonzeroCutoffModes (Audit.cutoff system))))
sortedNonzeroUpperShellFoldIsCanonicalSuffix system threshold =
  upperShellSelectedFoldIsCanonicalSuffix
    system threshold
    (Radial.sortByShell
      (R34.nonzeroCutoffModes (Audit.cutoff system)))
    (Radial.sortByShellOrdered
      (R34.nonzeroCutoffModes (Audit.cutoff system)))
    (sortPreservesAllNonzero
      (literalNonzeroCutoffAllNonzero (Audit.cutoff system)))

canonicalUpperShellSuffixIsNormalizedBoundaryFlux :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (threshold : Nat) →
  Reality.RealityCondition (Audit.velocity system) →
  Reality.DivergenceFreeCondition E (Audit.velocity system) →
  rawProjectedPairing system
      (dropBelowShell threshold
        (Radial.sortByShell
          (R34.nonzeroCutoffModes (Audit.cutoff system))))
  ≡ Norm.normalizedBoundaryTransfer
      E I (Upper.upperShellPacket threshold)
      (Audit.velocity system) (Audit.cutoff system)
canonicalUpperShellSuffixIsNormalizedBoundaryFlux
    {E} {I} system threshold reality divergenceFree =
  trans
    (sym (sortedNonzeroUpperShellFoldIsCanonicalSuffix system threshold))
    (Upper.sortedNonzeroUpperShellFoldIsNormalizedBoundaryFlux
      system threshold reality divergenceFree)

literalCanonicalUpperShellSuffixConstructed : Bool
literalCanonicalUpperShellSuffixConstructed = true

upperShellSelectorEqualsCanonicalSuffixFoldClosed : Bool
upperShellSelectorEqualsCanonicalSuffixFoldClosed = true

canonicalUpperShellSuffixBoundaryFluxClosed : Bool
canonicalUpperShellSuffixBoundaryFluxClosed = true

r104StructuralTailEqualsCanonicalSuffixClosed : Bool
r104StructuralTailEqualsCanonicalSuffixClosed = false

literalCanonicalUpperShellSuffixConstructedIsTrue :
  literalCanonicalUpperShellSuffixConstructed ≡ true
literalCanonicalUpperShellSuffixConstructedIsTrue = refl

upperShellSelectorEqualsCanonicalSuffixFoldClosedIsTrue :
  upperShellSelectorEqualsCanonicalSuffixFoldClosed ≡ true
upperShellSelectorEqualsCanonicalSuffixFoldClosedIsTrue = refl

canonicalUpperShellSuffixBoundaryFluxClosedIsTrue :
  canonicalUpperShellSuffixBoundaryFluxClosed ≡ true
canonicalUpperShellSuffixBoundaryFluxClosedIsTrue = refl

r104StructuralTailEqualsCanonicalSuffixClosedIsFalse :
  r104StructuralTailEqualsCanonicalSuffixClosed ≡ false
r104StructuralTailEqualsCanonicalSuffixClosedIsFalse = refl
