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
zero earlier? (suc n) = true
(suc m) earlier? zero = false
(suc m) earlier? (suc n) = m earlier? n

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


------------------------------------------------------------------------
-- Generalized statement of the order-erasure collision.
--
-- Any function into a type of conditional response distributions receives
-- exactly the same input for CE and EC. This proves equality of *laws*
-- without asserting equality of separately sampled outputs. It is the
-- finite non-stochastic prerequisite, not a probability kernel formalization.
------------------------------------------------------------------------

sameKernelResponseUnderOrderErasure :
  {Distribution : Set} (kernel : FeatureBag → Distribution) →
  kernel (forgetOrder cThenE) ≡ kernel (forgetOrder eThenC)
sameKernelResponseUnderOrderErasure kernel = refl

------------------------------------------------------------------------
-- Future masking inspired by the related source-written TimesFM-3
-- noninterference work in dashi_lean4 PR #83 (2026-10-23). The latter
-- was NOT merged or copied as a theorem dependency. This generic
-- list-prefix theorem is a DASHI extension, motivated by Rodgers's
-- shared-prefix Proposition 5 and the existing demand-local PNF owners.
------------------------------------------------------------------------

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ rest) = suc (listLength rest)

prefixOfLength : {A : Set} → Nat → List A → List A
prefixOfLength zero xs = []
prefixOfLength (suc n) [] = []
prefixOfLength (suc n) (x ∷ xs) =
  x ∷ prefixOfLength n xs

prefixIgnoresFutureSuffix :
  {A : Set} (prefix suffix : List A) →
  prefixOfLength (listLength prefix) (prefix ++ suffix) ≡ prefix
prefixIgnoresFutureSuffix [] suffix = refl
prefixIgnoresFutureSuffix (x ∷ prefix) suffix
  rewrite prefixIgnoresFutureSuffix prefix suffix = refl

equalReceivedPrefixesGiveEqualOnlineStates :
  {State Input : Set} →
  (step : State → Input → State) →
  (start : State) →
  (prefix laterA laterB : List Input) →
  runPrefix step start
    (prefixOfLength (listLength prefix) (prefix ++ laterA))
  ≡
  runPrefix step start
    (prefixOfLength (listLength prefix) (prefix ++ laterB))
equalReceivedPrefixesGiveEqualOnlineStates step start prefix laterA laterB
  rewrite prefixIgnoresFutureSuffix prefix laterA
        | prefixIgnoresFutureSuffix prefix laterB = refl

-- The consumer may be a reported state, a prediction or a conditional
-- distribution: equality follows by applying the *same* observer to
-- the two same-prefix states. It does not give a future oracle.
equalReceivedPrefixesGiveEqualObservedOutputs :
  {State Input Output : Set} →
  (step : State → Input → State) →
  (observe : State → Output) →
  (start : State) →
  (prefix laterA laterB : List Input) →
  observe (runPrefix step start
    (prefixOfLength (listLength prefix) (prefix ++ laterA)))
  ≡
  observe (runPrefix step start
    (prefixOfLength (listLength prefix) (prefix ++ laterB)))
equalReceivedPrefixesGiveEqualObservedOutputs step observe start prefix laterA laterB
  rewrite prefixIgnoresFutureSuffix prefix laterA
        | prefixIgnoresFutureSuffix prefix laterB = refl

------------------------------------------------------------------------
-- ARRIVAL COLLISION AND THE MINIMAL EXTRA OBSERVATION (DASHI EXTENSION).
--
-- Rodgers (2026-10-23), Sect. 5.2, gives the first delay/arrival pattern.
-- We add a synthetic reversed-source world with different channel delays.
-- This is a countermodel, NOT another empirical observation in Rodgers.
--
-- World A: C@0 + delay80 = C-arrival80;
--          E@50 + delay10 = E-arrival60. Source order C,E.
-- World B: E@0 + delay60 = E-arrival60;
--          C@50 + delay30 = C-arrival80. Source order E,C.
--
-- Thus even the FULLY LABELLED receiver timestamps C80, E60 collide.
-- This is stronger than erasing source order to an unordered note bag.
-- The physical experimental discriminator is independent *calibration*
-- of delay profiles, with errors/confounders controlled.
------------------------------------------------------------------------

data ArrivalWorld : Set where
  cSourceFirstWithCrossingDelay : ArrivalWorld
  eSourceFirstWithOtherDelay : ArrivalWorld

record LabelledArrivals : Set where
  constructor labelledArrivals
  field
    receiverTimeC : Nat
    receiverTimeE : Nat
open LabelledArrivals public

data PhysicalSourceOrder : Set where
  sourceCFirst : PhysicalSourceOrder
  sourceEFirst : PhysicalSourceOrder

observedArrivals : ArrivalWorld → LabelledArrivals
observedArrivals cSourceFirstWithCrossingDelay =
  labelledArrivals 80 60
observedArrivals eSourceFirstWithOtherDelay =
  labelledArrivals 80 60

actualSourceOrder : ArrivalWorld → PhysicalSourceOrder
actualSourceOrder cSourceFirstWithCrossingDelay = sourceCFirst
actualSourceOrder eSourceFirstWithOtherDelay = sourceEFirst

twoSourcesSameLabelledArrival :
  observedArrivals cSourceFirstWithCrossingDelay ≡
  observedArrivals eSourceFirstWithOtherDelay
twoSourcesSameLabelledArrival = refl

sourceOrdersDiffer : sourceCFirst ≡ sourceEFirst → ⊥
sourceOrdersDiffer ()

arrivalCollisionWitness :
  NF.NonFactorabilityWitness observedArrivals actualSourceOrder
arrivalCollisionWitness =
  NF.nonFactorabilityWitness
    cSourceFirstWithCrossingDelay
    eSourceFirstWithOtherDelay
    twoSourcesSameLabelledArrival
    sourceOrdersDiffer

labelledArrivalCannotRecoverSourceOrder :
  NF.FactorsThrough observedArrivals actualSourceOrder → ⊥
labelledArrivalCannotRecoverSourceOrder =
  NF.witnessRulesOutEveryFlatFactorisation arrivalCollisionWitness

-- The proposed additional information is exactly the independently
-- determined delay profile, not an oracle revealing source event order.
data CalibratedDelayProfile : Set where
  delayC80E10 : CalibratedDelayProfile
  delayC30E60 : CalibratedDelayProfile

record CalibratedReceiverObservation : Set where
  constructor calibratedReceiverObservation
  field
    arrivalReadout : LabelledArrivals
    delayReadout : CalibratedDelayProfile

calibratedObserver : ArrivalWorld → CalibratedReceiverObservation
calibratedObserver cSourceFirstWithCrossingDelay =
  calibratedReceiverObservation (labelledArrivals 80 60) delayC80E10
calibratedObserver eSourceFirstWithOtherDelay =
  calibratedReceiverObservation (labelledArrivals 80 60) delayC30E60

readSourceOrderWithCalibration :
  CalibratedReceiverObservation → PhysicalSourceOrder
readSourceOrderWithCalibration
  (calibratedReceiverObservation _ delayC80E10) = sourceCFirst
readSourceOrderWithCalibration
  (calibratedReceiverObservation _ delayC30E60) = sourceEFirst

exactCalibrationRecoversOrderForTheseWorlds :
  (w : ArrivalWorld) →
  readSourceOrderWithCalibration (calibratedObserver w)
    ≡ actualSourceOrder w
exactCalibrationRecoversOrderForTheseWorlds
  cSourceFirstWithCrossingDelay = refl
exactCalibrationRecoversOrderForTheseWorlds
  eSourceFirstWithOtherDelay = refl

-- Explicitly records the arithmetic in the *synthetic* second world.
secondWorldCArrival : 50 + 30 ≡ 80
secondWorldCArrival = refl

secondWorldEArrival : 0 + 60 ≡ 60
secondWorldEArrival = refl

-- Source-first underidentified observer and calibrated observer are
-- different information carriers. Do not promote the latter to a
-- physically accessible measurement unless the delay data are actually
-- calibrated in a same-source experiment.
