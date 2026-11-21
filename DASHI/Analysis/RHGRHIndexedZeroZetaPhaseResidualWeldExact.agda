module DASHI.Analysis.RHGRHIndexedZeroZetaPhaseResidualWeldExact where

-- P1 indexed zero/zeta/zetaSquared phase geometry.
-- Scalar zero != C3 exponent-zero (unity); cyclotomic zeta_3 != Riemann zeta.
-- k/time, sign and residual are retained even when observed value is zero.
-- Source-written; no Agda kernel check; no RH or physical acceptance claim.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)
import DASHI.Moonshine.Monster3BZeroZetaSquaredC3SeparationExact as Modes
import DASHI.Moonshine.C3FourierConjugationExact as Fourier

Mode : Set
Mode = Modes.ZeroOrRootOfUnity

zeroMode : Mode
zeroMode = Modes.scalarZero

zetaMode : Mode
zetaMode = Modes.nonzeroPhase Fourier.zeta

zetaSquaredMode : Mode
zetaSquaredMode = Modes.nonzeroPhase Fourier.zetaSquared

unitMode : Mode
unitMode = Modes.nonzeroPhase Fourier.one

zetaNotZero : zetaMode ≡ zeroMode → ⊥
zetaNotZero = Modes.zetaCannotBeScalarZero

zetaSquaredNotZero : zetaSquaredMode ≡ zeroMode → ⊥
zetaSquaredNotZero = Modes.zetaSquaredCannotBeScalarZero

unitNotZero : unitMode ≡ zeroMode → ⊥
unitNotZero = Modes.exponentZeroCannotBeScalarZero

reflectMode : Mode → Mode
reflectMode Modes.scalarZero = Modes.scalarZero
reflectMode (Modes.nonzeroPhase p) =
  Modes.nonzeroPhase (Fourier.inversePhase p)

reflectModeInvolutive : (m : Mode) →
  reflectMode (reflectMode m) ≡ m
reflectModeInvolutive Modes.scalarZero = refl
reflectModeInvolutive (Modes.nonzeroPhase p)
  rewrite Fourier.inversePhaseInvolutive p = refl

reflectZeta : reflectMode zetaMode ≡ zetaSquaredMode
reflectZeta = Fourier.inverseZetaIsZetaSquared

reflectZetaSquared : reflectMode zetaSquaredMode ≡ zetaMode
reflectZetaSquared = refl

record IndexedZeroPhaseFrame (Index Sign Residual : Set) : Set where
  constructor indexedZeroPhaseFrame
  field
    index : Index
    mode : Mode
    sign : Sign
    residual : Residual
    observedZero : Bool

open IndexedZeroPhaseFrame public

reflectFrame : ∀ {Index Sign Residual} →
  IndexedZeroPhaseFrame Index Sign Residual →
  IndexedZeroPhaseFrame Index Sign Residual
reflectFrame (indexedZeroPhaseFrame k m s r z) =
  indexedZeroPhaseFrame k (reflectMode m) s r z

reflectFrameInvolutive : ∀ {Index Sign Residual}
  (f : IndexedZeroPhaseFrame Index Sign Residual) →
  reflectFrame (reflectFrame f) ≡ f
reflectFrameInvolutive (indexedZeroPhaseFrame k m s r z)
  rewrite reflectModeInvolutive m = refl

-- Observed zero is an observation field, never proof that a mode is absent.
balancedObservedZeroWithZeta : IndexedZeroPhaseFrame Nat Bool Nat
balancedObservedZeroWithZeta =
  indexedZeroPhaseFrame 3 zetaMode true 9 true

balancedObservedZeroWithZetaSquared : IndexedZeroPhaseFrame Nat Bool Nat
balancedObservedZeroWithZetaSquared =
  reflectFrame balancedObservedZeroWithZeta

balancedZeroRetainsZeta :
  mode balancedObservedZeroWithZeta ≡ zetaMode
balancedZeroRetainsZeta = refl

balancedZeroRetainsConjugate :
  mode balancedObservedZeroWithZetaSquared ≡ zetaSquaredMode
balancedZeroRetainsConjugate = reflectZeta

balancedZeroPreservesResidual :
  residual balancedObservedZeroWithZetaSquared ≡
  residual balancedObservedZeroWithZeta
balancedZeroPreservesResidual = refl

balancedZeroPreservesSign :
  sign balancedObservedZeroWithZetaSquared ≡
  sign balancedObservedZeroWithZeta
balancedZeroPreservesSign = refl

balancedZeroNotScalarMode :
  mode balancedObservedZeroWithZeta ≡ zeroMode → ⊥
balancedZeroNotScalarMode = zetaNotZero

-- The consumer invariance is a genuine outstanding input, not inferred
-- from phase labels. A theta/Galois application must supply a source map.
record IndexedCommutingConsumer
  {Index Sign Residual Answer : Set}
  (consume : IndexedZeroPhaseFrame Index Sign Residual → Answer) : Set where
  field
    reflectedConsumer :
      (f : IndexedZeroPhaseFrame Index Sign Residual) →
      consume (reflectFrame f) ≡ consume f

commutingSquareAt :
  ∀ {Index Sign Residual Answer : Set}
  (consume : IndexedZeroPhaseFrame Index Sign Residual → Answer)
  (square : IndexedCommutingConsumer consume)
  (f : IndexedZeroPhaseFrame Index Sign Residual) →
  consume (reflectFrame (reflectFrame f)) ≡ consume f
commutingSquareAt consume square f =
  cong consume (reflectFrameInvolutive f)
