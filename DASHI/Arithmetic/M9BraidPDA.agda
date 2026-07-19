module DASHI.Arithmetic.M9BraidPDA where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Native 3-adic address surface.
--
-- Prefixes are least-significant-first residue addresses.  Extension is
-- refinement; no Euclidean order or interpolation is assumed.

data Digit3 : Set where
  d0 d1 d2 : Digit3

Prefix3 : Set
Prefix3 = List Digit3

extend3 : Digit3 → Prefix3 → Prefix3
extend3 d p = d ∷ p

record Ball3 : Set where
  constructor ball3
  field
    prefix : Prefix3
    depth  : Nat
open Ball3 public

childBall : Digit3 → Ball3 → Ball3
childBall d (ball3 p k) = ball3 (extend3 d p) (suc k)

------------------------------------------------------------------------
-- Three-valued kernel judgement.

data Verdict : Set where
  forbidden payable cleared : Verdict

------------------------------------------------------------------------
-- M9 braid vocabulary.
--
-- A factor carrier is deliberately not restricted to a pre-programmed list
-- of primes.  It is an arbitrary recursively generated hypothesis label.

record FactorCandidate : Set where
  constructor factor
  field
    code : Nat
open FactorCandidate public

data Event : Set where
  identity : Event
  push     : FactorCandidate → Event
  cross    : FactorCandidate → FactorCandidate → Event

BraidWord : Set
BraidWord = List Event

------------------------------------------------------------------------
-- PDA obligations and history.

record Obligation : Set where
  constructor obligation
  field
    candidate  : FactorCandidate
    introduced : Nat
    deadline   : Nat
open Obligation public

Stack : Set
Stack = List Obligation

record KernelState : Set where
  constructor kernelState
  field
    depth       : Nat
    stack       : Stack
    clearedSet  : List FactorCandidate
    alive       : Bool
    failStep    : Nat
open KernelState public

emptyState : KernelState
emptyState = kernelState zero [] [] true zero

------------------------------------------------------------------------
-- Fixed deadline width requested in the formalism: Δ = 3.

delta3 : Nat
delta3 = suc (suc (suc zero))

plus3 : Nat → Nat
plus3 zero = delta3
plus3 (suc n) = suc (plus3 n)

pushObligation : FactorCandidate → KernelState → KernelState
pushObligation m (kernelState k s c a f) =
  kernelState k (obligation m k (plus3 k) ∷ s) c a f

------------------------------------------------------------------------
-- Non-separable discharge.
--
-- Discharge is not unary.  It requires a genuine crossing between the
-- pending candidate and a distinct witness strand, together with a kernel
-- witness that the coupled evaluation is admissible.

record CoupledWitness (m w : FactorCandidate) (s : KernelState) : Set where
  field
    distinctStrands : Bool
    witnessAvailable : Bool
    depthGateOpen : Bool
    residuePasses : Bool
open CoupledWitness public

record DischargeResult : Set where
  constructor dischargeResult
  field
    nextState : KernelState
    verdict   : Verdict
    reading   : String
open DischargeResult public

nonSeparableDischarge :
  (m w : FactorCandidate) →
  (s : KernelState) →
  CoupledWitness m w s →
  DischargeResult
nonSeparableDischarge m w s cw with distinctStrands cw | witnessAvailable cw | depthGateOpen cw | residuePasses cw
... | true | true | true | true =
  dischargeResult s cleared "crossing discharged the pending factor obligation"
... | true | true | true | false =
  dischargeResult s forbidden "crossing exposed a factor witness"
... | _ | _ | _ | _ =
  dischargeResult s payable "obligation remains pending until a permitted crossing"

------------------------------------------------------------------------
-- π_B projection: history is part of legality.

piB : DischargeResult → Verdict
piB = verdict

crossingRequired :
  ∀ (m w : FactorCandidate) (s : KernelState) (cw : CoupledWitness m w s) →
  distinctStrands cw ≡ false →
  piB (nonSeparableDischarge m w s cw) ≡ payable
crossingRequired m w s cw p rewrite p = refl

witnessRequired :
  ∀ (m w : FactorCandidate) (s : KernelState) (cw : CoupledWitness m w s) →
  witnessAvailable cw ≡ false →
  piB (nonSeparableDischarge m w s cw) ≡ payable
witnessRequired m w s cw p rewrite p = refl

residueFailureForbids :
  ∀ (m w : FactorCandidate) (s : KernelState) (cw : CoupledWitness m w s) →
  distinctStrands cw ≡ true →
  witnessAvailable cw ≡ true →
  depthGateOpen cw ≡ true →
  residuePasses cw ≡ false →
  piB (nonSeparableDischarge m w s cw) ≡ forbidden
residueFailureForbids m w s cw p q r z rewrite p | q | r | z = refl

successfulCrossingClears :
  ∀ (m w : FactorCandidate) (s : KernelState) (cw : CoupledWitness m w s) →
  distinctStrands cw ≡ true →
  witnessAvailable cw ≡ true →
  depthGateOpen cw ≡ true →
  residuePasses cw ≡ true →
  piB (nonSeparableDischarge m w s cw) ≡ cleared
successfulCrossingClears m w s cw p q r z rewrite p | q | r | z = refl
