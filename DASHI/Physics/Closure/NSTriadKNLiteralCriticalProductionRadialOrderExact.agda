module DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionRadialOrderExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S2b1a / RADIAL ORDER OF THE LITERAL BAND CARRIER
--
-- S2b0 embeds each live Fourier mode as the exact R104 band
--
--   ( w(k) , Re <u_k,N_k(u)> )
--
-- but deliberately preserves the incoming finite mode order. R104's Abel
-- layer-cake needs a radial ordering before its suffixes can be interpreted as
-- physical upper packets.
--
-- This owner performs only the finite ordering step. It insertion-sorts the
-- SAME literal mode list by the repository's executable `shellIndex`, proves
-- the resulting shell indices are nondecreasing, and proves the S2a weighted
-- projected-pairing fold is invariant under that reorder. Consequently S0's
-- critical production is exactly twice R104.weightedTransfer on the radially
-- ordered band list.
--
-- This still does NOT identify a suffix with R98's physical upper-packet
-- selector and does NOT prove the quantitative S2 estimate. Those remain the
-- next same-object and analytic seams respectively.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNF4ProjectedOutputPairingRound39Exact as R39
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as S0
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionProjectedPairingExact as S2a
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionBandTransferExact as S2b0
import DASHI.Physics.Closure.NSTriadKNCriticalProductionPacketLayerCakeRound104Exact as LayerCake

F : C3.RealField _
F = Rational.rationalRealField

insertByShell : Z3.FourierMode → List Z3.FourierMode → List Z3.FourierMode
insertByShell mode [] = mode ∷ []
insertByShell mode (head ∷ rest)
  with Shell.shellIndex mode NatP.≤? Shell.shellIndex head
... | yes proof = mode ∷ head ∷ rest
... | no refutation = head ∷ insertByShell mode rest

sortByShell : List Z3.FourierMode → List Z3.FourierMode
sortByShell [] = []
sortByShell (mode ∷ rest) = insertByShell mode (sortByShell rest)

data ShellOrdered : List Z3.FourierMode → Set where
  ordered[] : ShellOrdered []
  ordered1 : ∀ {mode} → ShellOrdered (mode ∷ [])
  ordered∷ : ∀ {a b rest} →
    Shell.shellIndex a ≤ Shell.shellIndex b →
    ShellOrdered (b ∷ rest) →
    ShellOrdered (a ∷ b ∷ rest)

notLeGivesReverseLe : ∀ {m n : Nat} → ¬ (m ≤ n) → n ≤ m
notLeGivesReverseLe notLe = NatP.<⇒≤ (NatP.≰⇒> notLe)

insertPreservesShellOrder :
  (mode : Z3.FourierMode) →
  ∀ {modes} → ShellOrdered modes →
  ShellOrdered (insertByShell mode modes)
insertPreservesShellOrder mode ordered[] = ordered1
insertPreservesShellOrder mode (ordered1 {mode = head})
  with Shell.shellIndex mode NatP.≤? Shell.shellIndex head
... | yes mode≤head = ordered∷ mode≤head ordered1
... | no notMode≤Head =
  ordered∷ (notLeGivesReverseLe notMode≤Head) ordered1
insertPreservesShellOrder mode
    (ordered∷ {a = head} {b = next} {rest = rest} head≤next tailOrdered)
  with Shell.shellIndex mode NatP.≤? Shell.shellIndex head
... | yes mode≤head =
  ordered∷ mode≤head (ordered∷ head≤next tailOrdered)
... | no notMode≤Head
  with Shell.shellIndex mode NatP.≤? Shell.shellIndex next
... | yes mode≤next =
  ordered∷
    (notLeGivesReverseLe notMode≤Head)
    (ordered∷ mode≤next tailOrdered)
... | no notMode≤Next =
  ordered∷ head≤next
    (insertPreservesShellOrder mode tailOrdered)

sortByShellOrdered : (modes : List Z3.FourierMode) → ShellOrdered (sortByShell modes)
sortByShellOrdered [] = ordered[]
sortByShellOrdered (mode ∷ rest) =
  insertPreservesShellOrder mode (sortByShellOrdered rest)

modeTerm :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → ℚ
modeTerm system mode =
  S0.dyadicCriticalWeight mode
    * R39.realHermitianPower
        (Audit.velocity system mode)
        (Audit.projectedNonlinearity system mode)

insertPreservesWeightedProjectedPairing :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (mode : Z3.FourierMode) →
  (modes : List Z3.FourierMode) →
  S2a.weightedProjectedPairing system (insertByShell mode modes)
  ≡ modeTerm system mode + S2a.weightedProjectedPairing system modes
insertPreservesWeightedProjectedPairing system mode [] = refl
insertPreservesWeightedProjectedPairing system mode (head ∷ rest)
  with Shell.shellIndex mode NatP.≤? Shell.shellIndex head
... | yes proof = refl
... | no refutation
  rewrite insertPreservesWeightedProjectedPairing system mode rest =
  solve
    ( modeTerm system mode
    ∷ modeTerm system head
    ∷ S2a.weightedProjectedPairing system rest
    ∷ [] )

sortPreservesWeightedProjectedPairing :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (modes : List Z3.FourierMode) →
  S2a.weightedProjectedPairing system (sortByShell modes)
  ≡ S2a.weightedProjectedPairing system modes
sortPreservesWeightedProjectedPairing system [] = refl
sortPreservesWeightedProjectedPairing system (mode ∷ rest) =
  trans
    (insertPreservesWeightedProjectedPairing
      system mode (sortByShell rest))
    (cong (modeTerm system mode +_)
      (sortPreservesWeightedProjectedPairing system rest))

radialBandTransfers :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Z3.FourierMode →
  List LayerCake.BandTransfer
radialBandTransfers system modes =
  S2b0.literalBandTransfers system (sortByShell modes)

radialWeightedTransferIsLiteralWeightedPairing :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (modes : List Z3.FourierMode) →
  LayerCake.weightedTransfer (radialBandTransfers system modes)
  ≡ S2a.weightedProjectedPairing system modes
radialWeightedTransferIsLiteralWeightedPairing system modes =
  trans
    (S2b0.weightedTransferIsWeightedProjectedPairing
      system (sortByShell modes))
    (sortPreservesWeightedProjectedPairing system modes)

literalCriticalProductionIsTwiceRadialWeightedTransfer :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  S0.criticalProductionRate system
  ≡ S0.two * LayerCake.weightedTransfer
      (radialBandTransfers system (Audit.modes system))
literalCriticalProductionIsTwiceRadialWeightedTransfer system =
  trans
    (S2a.literalCriticalProductionIsTwiceWeightedProjectedPairing system)
    (cong (S0.two *_)
      (sym
        (radialWeightedTransferIsLiteralWeightedPairing
          system (Audit.modes system))))

literalRadialShellSortConstructed : Bool
literalRadialShellSortConstructed = true

literalRadialShellOrderProved : Bool
literalRadialShellOrderProved = true

literalWeightedProductionInvariantUnderRadialSort : Bool
literalWeightedProductionInvariantUnderRadialSort = true

radialSuffixPhysicalPacketSameObjectClosed : Bool
radialSuffixPhysicalPacketSameObjectClosed = false

s2QuantitativePacketFluxEstimateClosed : Bool
s2QuantitativePacketFluxEstimateClosed = false

literalRadialShellSortConstructedIsTrue :
  literalRadialShellSortConstructed ≡ true
literalRadialShellSortConstructedIsTrue = refl

literalRadialShellOrderProvedIsTrue :
  literalRadialShellOrderProved ≡ true
literalRadialShellOrderProvedIsTrue = refl

literalWeightedProductionInvariantUnderRadialSortIsTrue :
  literalWeightedProductionInvariantUnderRadialSort ≡ true
literalWeightedProductionInvariantUnderRadialSortIsTrue = refl

radialSuffixPhysicalPacketSameObjectClosedIsFalse :
  radialSuffixPhysicalPacketSameObjectClosed ≡ false
radialSuffixPhysicalPacketSameObjectClosedIsFalse = refl

s2QuantitativePacketFluxEstimateClosedIsFalse :
  s2QuantitativePacketFluxEstimateClosed ≡ false
s2QuantitativePacketFluxEstimateClosedIsFalse = refl
