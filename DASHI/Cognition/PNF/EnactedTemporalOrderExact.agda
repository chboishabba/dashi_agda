-- Imported legacy owner is not declared --safe; this module contains no
-- postulates or holes but does not claim transitive Safe Agda certification.
module DASHI.Cognition.PNF.EnactedTemporalOrderExact where

-- Source: Jeremy Rodgers, "Experienced Temporal Passage: Enacted
-- Scaffolding and the Organization of Succession" (2026-10-23),
-- DOI 10.5281/zenodo.23591626, Proposition 1, Proposition 5,
-- and Appendix C. This is a DASHI reconstruction of finite mathematical
-- consequences, NOT a proof of the constitutive consciousness premises.
-- Reuses the existing DASHI.Core.IntersectionalNonFactorability theorem.
-- The original nonfactorability theorem is DASHI mathematics; neither
-- Rodgers nor the motivation cited by that owner is its proof author.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)
import DASHI.Core.IntersectionalNonFactorability as NF

-- The two opposing orientations have the same unordered note bag.
data DirectedHistory : Set where
  cThenE : DirectedHistory
  eThenC : DirectedHistory

data FeatureBag : Set where
  cAndE : FeatureBag

data OrientedReading : Set where
  cBeforeE : OrientedReading
  eBeforeC : OrientedReading

forgetOrder : DirectedHistory → FeatureBag
forgetOrder cThenE = cAndE
forgetOrder eThenC = cAndE

readOrder : DirectedHistory → OrientedReading
readOrder cThenE = cBeforeE
readOrder eThenC = eBeforeC

oppositeReadingsDiffer : cBeforeE ≡ eBeforeC → ⊥
oppositeReadingsDiffer ()

orderErasureWitness : NF.NonFactorabilityWitness forgetOrder readOrder
orderErasureWitness =
  NF.nonFactorabilityWitness cThenE eThenC refl oppositeReadingsDiffer

-- No deterministic reader of the unordered bag can always recover the
-- order. The corresponding stochastic statement needs a typed probability
-- kernel, and is NOT inferred from this deterministic theorem.
featureBagCannotRecoverDirectedOrder :
  NF.FactorsThrough forgetOrder readOrder → ⊥
featureBagCannotRecoverDirectedOrder =
  NF.witnessRulesOutEveryFlatFactorisation orderErasureWitness

-- Relabeling an already-erased observation cannot restore orientation.
relabelledBagCannotRecoverOrder :
  {MoreCoarse : Set} (relabel : FeatureBag → MoreCoarse) →
  NF.FactorsThrough (λ h → relabel (forgetOrder h)) readOrder → ⊥
relabelledBagCannotRecoverOrder relabel =
  NF.rechartingCannotRecoverErasedPhenomenon relabel orderErasureWitness

-- The actual on-line state update cannot inspect a later suffix in order
-- to compute a prefix. No psychic/future input is stipulated.
_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

runPrefix : {State Input : Set} →
  (State → Input → State) → State → List Input → State
runPrefix step s [] = s
runPrefix step s (input ∷ rest) =
  runPrefix step (step s input) rest

prefixSuffixLaw :
  {State Input : Set} →
  (step : State → Input → State) →
  (s : State) →
  (prefix suffix : List Input) →
  runPrefix step s (prefix ++ suffix) ≡
    runPrefix step (runPrefix step s prefix) suffix
prefixSuffixLaw step s [] suffix = refl
prefixSuffixLaw step s (input ∷ prefix) suffix =
  prefixSuffixLaw step (step s input) prefix suffix

-- U (actual uptake) and R_later (optional later retrieval) must not be
-- identified. The Boolean condition below merely formalizes the paper's
-- *stipulated* admission conjunction. It is not an empirical detector.
data RetrievalCapacity : Set where
  laterAvailable : RetrievalCapacity
  laterUnavailable : RetrievalCapacity

_&&_ : Bool → Bool → Bool
_ && false = false
true && true = true
false && true = false

record AdmissionInputs : Set where
  constructor admission
  field
    boundedUnit : Bool
    actualReception : Bool
    interpretation : Bool
    consolidation : Bool
    operativeRetention : Bool
    formativeHistory : Bool
    actualUptake : Bool
    laterRetrieval : RetrievalCapacity
open AdmissionInputs public

stipulatedAdmission : AdmissionInputs → Bool
stipulatedAdmission a =
  (((((boundedUnit a && actualReception a)
     && interpretation a)
     && consolidation a)
     && operativeRetention a)
     && formativeHistory a)
     && actualUptake a

laterRetrievalDoesNotChangeAdmission :
  (b d i c m h u : Bool) →
  stipulatedAdmission (admission b d i c m h u laterAvailable) ≡
  stipulatedAdmission (admission b d i c m h u laterUnavailable)
laterRetrievalDoesNotChangeAdmission b d i c m h u = refl

absentUptakeFailsStipulatedAdmission :
  (b d i c m h : Bool) →
  stipulatedAdmission
    (admission b d i c m h false laterAvailable) ≡ false
absentUptakeFailsStipulatedAdmission b d i c m h = refl

allPremisesSufficeWithinTheStipulation :
  stipulatedAdmission
    (admission true true true true true true true laterUnavailable) ≡ true
allPremisesSufficeWithinTheStipulation = refl


-- Rodgers Section 5.2: the original source-to-receiver model uses C at 0ms
-- with 80ms delay and E at 50ms with 10ms delay. Hence C occurs first but
-- E arrives first. We formalise the exact finite arithmetic without granting
-- a receiver an oracle for the actual source time. A physical consumer must
-- separately establish calibration and permissible local information.

_earlier?_ : Nat → Nat → Bool
zero earlier? zero = false
zero earlier? suc n = true
suc m earlier? zero = false
suc m earlier? suc n = m earlier? n

sourceC : Nat
sourceC = 0
sourceE : Nat
sourceE = 50
channelDelayC : Nat
channelDelayC = 80
channelDelayE : Nat
channelDelayE = 10
receivedC : Nat
receivedC = sourceC + channelDelayC
receivedE : Nat
receivedE = sourceE + channelDelayE

sourceCE : (sourceC earlier? sourceE) ≡ true
sourceCE = refl

receptionEC : (receivedE earlier? receivedC) ≡ true
receptionEC = refl

arrivalCEquals80ms : receivedC ≡ 80
arrivalCEquals80ms = refl

arrivalEEquals60ms : receivedE ≡ 60
arrivalEEquals60ms = refl

-- Conditional on *correct calibrated estimates* of source times, the local
-- reader recovers the source order. The present file does not supply a model
-- or empirical proof that a listener knows these estimates.
calibratedReadoutIfEstimatesCorrect :
  (estimatedC estimatedE : Nat) →
  estimatedC ≡ sourceC →
  estimatedE ≡ sourceE →
  (estimatedC earlier? estimatedE) ≡ true
calibratedReadoutIfEstimatesCorrect estimatedC estimatedE hC hE
  rewrite hC | hE = sourceCE
