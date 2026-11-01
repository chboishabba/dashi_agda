module DASHI.Physics.Closure.NSTriadKNS2b2AdjacentShellSpectralGapNoGoExact where

------------------------------------------------------------------------
-- STRICT B-PHASE S2b2 NEGATIVE CONTROL / ADJACENT SHELL != EUCLIDEAN GAP
--
-- The complementary low-packet orientation makes R98's spectral
-- cross-dissipation theorem superficially tempting.  That theorem, however,
-- needs a genuine Euclidean squared-frequency separation between the selected
-- packet and its complement.
--
-- The live S2b1 packet geometry is shellIndex = ceil(log2 ||k||_infinity).
-- Adjacent shellIndex separation does NOT imply the required Euclidean gap.
-- The finite witness at threshold j=2 is literal:
--
--   low  = (2,2,2),  shellIndex low  = 1, |low|_2^2  = 12;
--   high = (3,0,0),  shellIndex high = 2, |high|_2^2 = 9.
--
-- Thus the lower-shell selector contains a mode with larger Euclidean squared
-- frequency than a mode contained in the upper-shell selector.  Any use of
-- R98 positive spectral-gap coercivity therefore needs a stronger packet split
-- or a different coercive quantity; shellIndex adjacency alone cannot pay it.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (_<_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteIntegerModeNorm as ModeNorm
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNLiteralUpperShellPacketSelectorExact as Upper
import DASHI.Physics.Closure.NSTriadKNPacketBoundaryFluxComplementRound98Exact as Complement

lowWitness : Z3.FourierMode
lowWitness = Z3.mode (+ 2) (+ 2) (+ 2)

highWitness : Z3.FourierMode
highWitness = Z3.mode (+ 3) (+ 0) (+ 0)

lowWitnessShell : Shell.shellIndex lowWitness ≡ 1
lowWitnessShell = refl

highWitnessShell : Shell.shellIndex highWitness ≡ 2
highWitnessShell = refl

lowWitnessIsInLowerPacketAtTwo :
  Complement.lowerShellPacket 2 lowWitness ≡ true
lowWitnessIsInLowerPacketAtTwo = refl

highWitnessIsInUpperPacketAtTwo :
  Upper.upperShellPacket 2 highWitness ≡ true
highWitnessIsInUpperPacketAtTwo = refl

lowWitnessNormSquared :
  ModeNorm.modeNatNormSquared lowWitness ≡ 12
lowWitnessNormSquared = refl

highWitnessNormSquared :
  ModeNorm.modeNatNormSquared highWitness ≡ 9
highWitnessNormSquared = refl

StrictEuclideanSeparationAt : Nat → Set
StrictEuclideanSeparationAt threshold =
  (low high : Z3.FourierMode) →
  Complement.lowerShellPacket threshold low ≡ true →
  Upper.upperShellPacket threshold high ≡ true →
  ModeNorm.modeNatNormSquared low < ModeNorm.modeNatNormSquared high

twelveNotLessNine : 12 < 9 → ⊥
twelveNotLessNine ()

adjacentShellEuclideanGapFailsAtTwo :
  StrictEuclideanSeparationAt 2 → ⊥
adjacentShellEuclideanGapFailsAtTwo separated =
  twelveNotLessNine
    (separated
      lowWitness highWitness
      lowWitnessIsInLowerPacketAtTwo
      highWitnessIsInUpperPacketAtTwo)

adjacentShellEuclideanGapNoGoClosed : Bool
adjacentShellEuclideanGapNoGoClosed = true

r98PositiveGapCannotBeInstantiatedFromAdjacentShellIndexAlone : Bool
r98PositiveGapCannotBeInstantiatedFromAdjacentShellIndexAlone = true

s2b2StillRequiresDifferentCoerciveMechanismOrStrongerPacketSplit : Bool
s2b2StillRequiresDifferentCoerciveMechanismOrStrongerPacketSplit = true

adjacentShellEuclideanGapNoGoClosedIsTrue :
  adjacentShellEuclideanGapNoGoClosed ≡ true
adjacentShellEuclideanGapNoGoClosedIsTrue = refl

r98PositiveGapCannotBeInstantiatedFromAdjacentShellIndexAloneIsTrue :
  r98PositiveGapCannotBeInstantiatedFromAdjacentShellIndexAlone ≡ true
r98PositiveGapCannotBeInstantiatedFromAdjacentShellIndexAloneIsTrue = refl

s2b2StillRequiresDifferentCoerciveMechanismOrStrongerPacketSplitIsTrue :
  s2b2StillRequiresDifferentCoerciveMechanismOrStrongerPacketSplit ≡ true
s2b2StillRequiresDifferentCoerciveMechanismOrStrongerPacketSplitIsTrue = refl
