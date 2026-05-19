module Ontology.DNA.StreamingEncoderSurface where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Vec using (Vec)
open import Data.Vec.Base using ([]; _∷ʳ_)

open import Ontology.DNA.Supervoxel4Adic using (Base)
open import Ontology.DNA.ChemistryUVCoordinates using (UVCoordinates; encodeUV)
open import Ontology.DNA.ChemistryConcrete using
  (_&&_; countStrong; countHairpin6; countRCPal4;
   noImmediateRepeat; noImmediateComplement; noComplementSpan2;
   noExtremeGC4; noRCPal4; noHairpin6; gcStress3)
open import Ontology.DNA.ChemistryUVConcrete using
  (countUVDimer2; countPyrimidineTriple3)
open import Ontology.DNA.ChemistrySheetHamiltonian using (chemistryHamiltonianOf)

------------------------------------------------------------------------
-- Streaming encoder update surface.
-- This is the local owner for the finite-state DASHI codec spec:
-- prefix, admissible next base, and updated multiscale accumulators.

record EncoderState (n : Nat) : Set where
  constructor encoderState
  field
    prefix : Vec Base n
    uvState : UVCoordinates n
    thermoState : Nat
    uvRiskState : Nat
    hamiltonianState : Nat

stateOf : ∀ {n} → Vec Base n → EncoderState n
stateOf xs =
  encoderState xs (encodeUV xs)
    (countStrong xs + countRCPal4 xs + countHairpin6 xs)
    (countUVDimer2 xs + countPyrimidineTriple3 xs)
    (chemistryHamiltonianOf xs)

initState : EncoderState 0
initState = stateOf []

stepAdmissible : ∀ {n} → EncoderState n → Base → Bool
stepAdmissible {n} st b =
  ((noImmediateRepeat ys && noImmediateComplement ys) && noComplementSpan2 ys)
    && ((noExtremeGC4 ys && noRCPal4 ys) && (noHairpin6 ys && gcStress3 ys))
  where
  ys : Vec Base (suc n)
  ys = EncoderState.prefix st ∷ʳ b

streamUpdate : ∀ {n} → EncoderState n → Base → EncoderState (suc n)
streamUpdate st b = stateOf (EncoderState.prefix st ∷ʳ b)

stateOf-prefix : ∀ {n} (xs : Vec Base n) → EncoderState.prefix (stateOf xs) ≡ xs
stateOf-prefix xs = refl

streamUpdate-prefix :
  ∀ {n} (st : EncoderState n) (b : Base) →
  EncoderState.prefix (streamUpdate st b) ≡ EncoderState.prefix st ∷ʳ b
streamUpdate-prefix st b = refl

streamUpdate-thermo-consistent :
  ∀ {n} (st : EncoderState n) (b : Base) →
  EncoderState.thermoState (streamUpdate st b)
    ≡ countStrong (EncoderState.prefix st ∷ʳ b)
      + countRCPal4 (EncoderState.prefix st ∷ʳ b)
      + countHairpin6 (EncoderState.prefix st ∷ʳ b)
streamUpdate-thermo-consistent st b = refl

streamUpdate-hamiltonian-consistent :
  ∀ {n} (st : EncoderState n) (b : Base) →
  EncoderState.hamiltonianState (streamUpdate st b)
    ≡ chemistryHamiltonianOf (EncoderState.prefix st ∷ʳ b)
streamUpdate-hamiltonian-consistent st b = refl

record AdmissibleChoice (n : Nat) : Set where
  constructor admissibleChoice
  field
    base : Base
    allowed : Bool
    nextState : EncoderState (suc n)

choose : ∀ {n} → EncoderState n → Base → AdmissibleChoice n
choose st b =
  admissibleChoice b (stepAdmissible st b) (streamUpdate st b)

choose-nextState-consistent :
  ∀ {n} (st : EncoderState n) (b : Base) →
  AdmissibleChoice.nextState (choose st b) ≡ streamUpdate st b
choose-nextState-consistent st b = refl

record StreamingEncoderSurface : Set₁ where
  field
    State : Nat → Set
    initial : State 0
    admissibleNext : ∀ {n} → State n → Base → Bool
    update : ∀ {n} → State n → Base → State (suc n)
    checksumSurface : ∀ {n} → State n → Σ Nat (λ _ → Nat)

streamingEncoderSurface : StreamingEncoderSurface
streamingEncoderSurface = record
  { State = EncoderState
  ; initial = initState
  ; admissibleNext = stepAdmissible
  ; update = streamUpdate
  ; checksumSurface = λ st →
      EncoderState.thermoState st , EncoderState.hamiltonianState st
  }
