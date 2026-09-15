module DASHI.Physics.Closure.NSTriadKNR104StrictShellJumpTailExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S2b1b2b0 / LOCAL R104 TAIL AT A GENUINE SHELL JUMP
--
-- The per-mode radial carrier may contain adjacent modes in the same shell.
-- Those interfaces have zero radial increment and therefore are not physical
-- packet boundaries.  At a genuine shell jump
--
--   shellIndex left < shellIndex right
--
-- the structural R104 tail `(right ∷ rest)` is exactly the canonical suffix
-- selected by dropping all modes below `shellIndex right` from the current
-- recursive suffix `(left ∷ right ∷ rest)`.
--
-- This pays the local finite tail identity needed by the Abel recursion.  A
-- separate global-prefix induction still has to identify every active recursive
-- suffix with the canonical upper-shell suffix of the original sorted support.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (_<_)
open import Data.Nat.Properties using (_≤?_; ≤-refl; <⇒≱)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionBandTransferExact as S2b0
import DASHI.Physics.Closure.NSTriadKNLiteralUpperShellCanonicalSuffixExact as Canonical
import DASHI.Physics.Closure.NSTriadKNCriticalProductionPacketLayerCakeRound104Exact as LayerCake

F : C3.RealField _
F = Rational.rationalRealField

strictShellJumpDropBelow :
  (left right : Z3.FourierMode) →
  (rest : List Z3.FourierMode) →
  Shell.shellIndex left < Shell.shellIndex right →
  Canonical.dropBelowShell (Shell.shellIndex right) (left ∷ right ∷ rest)
  ≡ right ∷ rest
strictShellJumpDropBelow left right rest jump
  with Shell.shellIndex right ≤? Shell.shellIndex left in leftDecision
... | yes right≤left =
  ⊥-elim (<⇒≱ jump right≤left)
... | no notRight≤Left
  with Shell.shellIndex right ≤? Shell.shellIndex right in rightDecision
... | yes right≤right = refl
... | no notRight≤Right = ⊥-elim (notRight≤Right ≤-refl)

r104TailAtStrictShellJumpIsCanonicalSuffix :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (left right : Z3.FourierMode) →
  (rest : List Z3.FourierMode) →
  Shell.shellIndex left < Shell.shellIndex right →
  LayerCake.totalTransfer
      (S2b0.literalBandTransfers system (right ∷ rest))
  ≡ Canonical.rawProjectedPairing system
      (Canonical.dropBelowShell
        (Shell.shellIndex right)
        (left ∷ right ∷ rest))
r104TailAtStrictShellJumpIsCanonicalSuffix
    system left right rest jump =
  trans
    (Canonical.literalBandTotalTransferIsRawPairing
      system (right ∷ rest))
    (sym
      (cong (Canonical.rawProjectedPairing system)
        (strictShellJumpDropBelow left right rest jump)))

strictShellJumpCanonicalDropClosed : Bool
strictShellJumpCanonicalDropClosed = true

localR104StructuralTailCanonicalSuffixClosed : Bool
localR104StructuralTailCanonicalSuffixClosed = true

globalR104LayerCakePhysicalPacketWeldClosed : Bool
globalR104LayerCakePhysicalPacketWeldClosed = false

strictShellJumpCanonicalDropClosedIsTrue :
  strictShellJumpCanonicalDropClosed ≡ true
strictShellJumpCanonicalDropClosedIsTrue = refl

localR104StructuralTailCanonicalSuffixClosedIsTrue :
  localR104StructuralTailCanonicalSuffixClosed ≡ true
localR104StructuralTailCanonicalSuffixClosedIsTrue = refl

globalR104LayerCakePhysicalPacketWeldClosedIsFalse :
  globalR104LayerCakePhysicalPacketWeldClosed ≡ false
globalR104LayerCakePhysicalPacketWeldClosedIsFalse = refl
