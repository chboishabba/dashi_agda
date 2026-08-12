module DASHI.Crypto.FiniteMLWEVectorLabExact where

------------------------------------------------------------------------
-- FINITE 2x2 MODULAR NOISY-LINEAR BLUE-TEAM LAB
--
-- This is deliberately not ML-KEM.  It is a finite executable regression model
-- with the same structural shape as the FIPS-203 public relation: t = A s + e.
-- It is large enough to exhibit a genuine public fibre with two distinct secret
-- states, exact residual testing, finite candidate cardinalities, coupled row
-- constraints, and strict shrinkage after one hidden-dependent observation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Crypto.FiniteCandidateFibreCardinalityExact as Count
import DASHI.Crypto.TranscriptProtectedLabelExact as Label

------------------------------------------------------------------------
-- Z/5Z arithmetic.
------------------------------------------------------------------------

data Z5 : Set where
  z0 z1 z2 z3 z4 : Z5

add5 : Z5 → Z5 → Z5
add5 z0 b = b
add5 z1 z0 = z1
add5 z1 z1 = z2
add5 z1 z2 = z3
add5 z1 z3 = z4
add5 z1 z4 = z0
add5 z2 z0 = z2
add5 z2 z1 = z3
add5 z2 z2 = z4
add5 z2 z3 = z0
add5 z2 z4 = z1
add5 z3 z0 = z3
add5 z3 z1 = z4
add5 z3 z2 = z0
add5 z3 z3 = z1
add5 z3 z4 = z2
add5 z4 z0 = z4
add5 z4 z1 = z0
add5 z4 z2 = z1
add5 z4 z3 = z2
add5 z4 z4 = z3

neg5 : Z5 → Z5
neg5 z0 = z0
neg5 z1 = z4
neg5 z2 = z3
neg5 z3 = z2
neg5 z4 = z1

sub5 : Z5 → Z5 → Z5
sub5 a b = add5 a (neg5 b)

double5 : Z5 → Z5
double5 x = add5 x x

embedBit : Bool → Z5
embedBit false = z0
embedBit true = z1

------------------------------------------------------------------------
-- Secret, error and public vectors.
------------------------------------------------------------------------

record Secret2 : Set where
  constructor secret2
  field s0 s1 : Bool
open Secret2 public

record Error2 : Set where
  constructor error2
  field e0 e1 : Z5
open Error2 public

record Public2 : Set where
  constructor public2
  field t0 t1 : Z5
open Public2 public

-- A = [[1,2],[2,1]] over Z5.
applyA : Secret2 → Public2
applyA s = public2
  (add5 (embedBit (s0 s)) (double5 (embedBit (s1 s))))
  (add5 (double5 (embedBit (s0 s))) (embedBit (s1 s)))

publish : Secret2 → Error2 → Public2
publish s e = public2
  (add5 (t0 (applyA s)) (e0 e))
  (add5 (t1 (applyA s)) (e1 e))

candidateResidual : Public2 → Secret2 → Error2
candidateResidual t s = error2
  (sub5 (t0 t) (t0 (applyA s)))
  (sub5 (t1 t) (t1 (applyA s)))

small : Z5 → Bool
small z0 = true
small z1 = true
small z2 = false
small z3 = false
small z4 = false

and : Bool → Bool → Bool
and true b = b
and false b = false

candidatePlausible : Public2 → Secret2 → Bool
candidatePlausible t s =
  and (small (e0 (candidateResidual t s)))
      (small (e1 (candidateResidual t s)))

residualScore : Z5 → Nat
residualScore z0 = 0
residualScore z1 = 0
residualScore z2 = 1
residualScore z3 = 1
residualScore z4 = 1

candidateScore : Public2 → Secret2 → Nat
candidateScore t s =
  residualScore (e0 (candidateResidual t s)) +
  residualScore (e1 (candidateResidual t s))

------------------------------------------------------------------------
-- Exact public collision.
------------------------------------------------------------------------

s00 s01 s10 s11 : Secret2
s00 = secret2 false false
s01 = secret2 false true
s10 = secret2 true false
s11 = secret2 true true

e01 e10 : Error2
e01 = error2 z0 z1
e10 = error2 z1 z0

public22 : Public2
public22 = public2 z2 z2

publish01Is22 : publish s01 e01 ≡ public22
publish01Is22 = refl

publish10Is22 : publish s10 e10 ≡ public22
publish10Is22 = refl

residual01 : candidateResidual public22 s01 ≡ e01
residual01 = refl

residual10 : candidateResidual public22 s10 ≡ e10
residual10 = refl

plausible00 : candidatePlausible public22 s00 ≡ false
plausible00 = refl

plausible01 : candidatePlausible public22 s01 ≡ true
plausible01 = refl

plausible10 : candidatePlausible public22 s10 ≡ true
plausible10 = refl

plausible11 : candidatePlausible public22 s11 ≡ false
plausible11 = refl

score00 : candidateScore public22 s00 ≡ 2
score00 = refl

score01 : candidateScore public22 s01 ≡ 0
score01 = refl

score10 : candidateScore public22 s10 ≡ 0
score10 = refl

score11 : candidateScore public22 s11 ≡ 2
score11 = refl

------------------------------------------------------------------------
-- Finite candidate fibre: exactly two of four secret candidates survive.
------------------------------------------------------------------------

public22CandidateMask : List Bool
public22CandidateMask = false ∷ true ∷ true ∷ false ∷ []

public22CandidateCount : Count.liveCount public22CandidateMask ≡ 2
public22CandidateCount = refl

-- A hidden-dependent observation exposing the first secret bit distinguishes
-- the two surviving candidates.  This is a lab observation, not an ML-KEM API.

afterFirstBitFalseMask : List Bool
afterFirstBitFalseMask = false ∷ true ∷ false ∷ false ∷ []

firstBitObservationRefines :
  Count.Refines public22CandidateMask afterFirstBitFalseMask
firstBitObservationRefines =
  Count.keepDead
    (Count.keepLive
      (Count.dropLive
        (Count.keepDead Count.empty)))

afterFirstBitFalseCount : Count.liveCount afterFirstBitFalseMask ≡ 1
afterFirstBitFalseCount = refl

------------------------------------------------------------------------
-- Public-fibre / protected-label theorem instance.
------------------------------------------------------------------------

record HiddenState : Set where
  constructor hiddenState
  field
    secret : Secret2
    error : Error2
open HiddenState public

hidden01 hidden10 : HiddenState
hidden01 = hiddenState s01 e01
hidden10 = hiddenState s10 e10

projectHidden : HiddenState → Public2
projectHidden h = publish (secret h) (error h)

labTranscriptLabelSystem : Label.TranscriptLabelSystem
labTranscriptLabelSystem =
  Label.transcriptLabelSystem HiddenState Public2 Secret2 projectHidden secret

secret01NotSecret10 : s01 ≡ s10 → ⊥
secret01NotSecret10 equality = bitImpossible (cong s0 equality)
  where
  bitImpossible : false ≡ true → ⊥
  bitImpossible ()

public22SecretLabelSplit :
  Label.TranscriptLabelFibreSplit labTranscriptLabelSystem
public22SecretLabelSplit =
  Label.transcriptLabelFibreSplit hidden01 hidden10 refl secret01NotSecret10

noExactSecretRecoveryFromPublic22 :
  Label.ExactTranscriptLabelRecovery labTranscriptLabelSystem → ⊥
noExactSecretRecoveryFromPublic22 =
  Label.transcriptLabelSplitRefutesExactRecovery public22SecretLabelSplit

------------------------------------------------------------------------
-- Coupling graph: both row residuals depend on the same two secret variables.
------------------------------------------------------------------------

data Row : Set where row0 row1 : Row

data SharesSecretCoordinates : Row → Row → Set where
  row0-row1 : SharesSecretCoordinates row0 row1
  row1-row0 : SharesSecretCoordinates row1 row0

rowsAreCoupled : SharesSecretCoordinates row0 row1
rowsAreCoupled = row0-row1

record FiniteMLWELabSummary : Set where
  constructor finiteMLWELabSummary
  field
    modulus : Nat
    secretCandidatesBefore : Nat
    candidatesAfterPublicResidualTest : Nat
    candidatesAfterOneHiddenObservation : Nat

open FiniteMLWELabSummary public

finiteMLWELabSummary : FiniteMLWELabSummary
finiteMLWELabSummary = finiteMLWELabSummary 5 4 2 1
