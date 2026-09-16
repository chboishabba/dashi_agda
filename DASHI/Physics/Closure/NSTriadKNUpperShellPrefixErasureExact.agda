module DASHI.Physics.Closure.NSTriadKNUpperShellPrefixErasureExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S2b1b2b1 / BELOW-THRESHOLD PREFIX ERASURE
--
-- At a genuine radial jump the already-traversed prefix lies strictly below
-- the new shell threshold.  Such a prefix contributes neither to the literal
-- upperShellPacket selected pairing nor to the canonical dropBelowShell suffix.
--
-- This file proves those two finite erasure statements generically.  No
-- Fourier estimate, boundary-flux theorem or positivity argument appears here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (_<_)
open import Data.Nat.Properties using (_≤?_; <⇒≱)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNSelectedPacketProjectedPairingRound98Exact as R98
import DASHI.Physics.Closure.NSTriadKNLiteralUpperShellPacketSelectorExact as Upper
import DASHI.Physics.Closure.NSTriadKNLiteralUpperShellCanonicalSuffixExact as Canonical

F : C3.RealField _
F = Rational.rationalRealField

data AllBelow (threshold : Nat) : List Z3.FourierMode → Set where
  allBelow[] : AllBelow threshold []
  allBelow∷ : ∀ {mode rest} →
    Shell.shellIndex mode < threshold →
    AllBelow threshold rest →
    AllBelow threshold (mode ∷ rest)

append : ∀ {A : Set} → List A → List A → List A
append [] right = right
append (x ∷ xs) right = x ∷ append xs right

upperShellSelectedBelowPrefixErasure :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (threshold : Nat) →
  (prefix suffix : List Z3.FourierMode) →
  Canonical.AllNonzero prefix →
  AllBelow threshold prefix →
  R98.sumSelectedProjectedPairings system (Upper.upperShellPacket threshold)
      (append prefix suffix)
  ≡ R98.sumSelectedProjectedPairings system (Upper.upperShellPacket threshold)
      suffix
upperShellSelectedBelowPrefixErasure
    system threshold [] suffix Canonical.allNonzero[] allBelow[] = refl
upperShellSelectedBelowPrefixErasure
    system threshold (mode ∷ prefix) suffix
    (Canonical.allNonzero∷ modeNonzero prefixNonzero)
    (allBelow∷ modeBelow prefixBelow) =
  let
    selectedFalse =
      Canonical.upperShellPacketFalseBelow
        threshold mode modeNonzero (<⇒≱ modeBelow)
  in
  rewrite selectedFalse =
    upperShellSelectedBelowPrefixErasure
      system threshold prefix suffix prefixNonzero prefixBelow

upperShellDropBelowPrefixErasure :
  (threshold : Nat) →
  (prefix suffix : List Z3.FourierMode) →
  AllBelow threshold prefix →
  Canonical.dropBelowShell threshold (append prefix suffix)
  ≡ Canonical.dropBelowShell threshold suffix
upperShellDropBelowPrefixErasure threshold [] suffix allBelow[] = refl
upperShellDropBelowPrefixErasure threshold (mode ∷ prefix) suffix
    (allBelow∷ modeBelow prefixBelow)
  with threshold ≤? Shell.shellIndex mode in decision
... | yes threshold≤mode =
  ⊥-elim (<⇒≱ modeBelow threshold≤mode)
... | no notThreshold≤Mode =
  upperShellDropBelowPrefixErasure
    threshold prefix suffix prefixBelow

upperShellSelectedBelowPrefixErasureClosed : Bool
upperShellSelectedBelowPrefixErasureClosed = true

upperShellDropBelowPrefixErasureClosed : Bool
upperShellDropBelowPrefixErasureClosed = true

upperShellSelectedBelowPrefixErasureClosedIsTrue :
  upperShellSelectedBelowPrefixErasureClosed ≡ true
upperShellSelectedBelowPrefixErasureClosedIsTrue = refl

upperShellDropBelowPrefixErasureClosedIsTrue :
  upperShellDropBelowPrefixErasureClosed ≡ true
upperShellDropBelowPrefixErasureClosedIsTrue = refl
