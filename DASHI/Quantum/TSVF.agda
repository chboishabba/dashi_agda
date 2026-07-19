module DASHI.Quantum.TSVF where

open import DASHI.Core.Prelude
open import DASHI.Foundations.TwoBoundarySystem

------------------------------------------------------------------------
-- Abstract quantum surface
--
-- DASHI currently has no single repository-wide Hilbert-space interface that
-- this bridge can safely reuse.  Consequently the exact scalar, adjoint,
-- evolution, and normalization laws are parameters/obligations here rather
-- than fabricated concrete implementations.
------------------------------------------------------------------------

record QuantumSurface : Set₁ where
  field
    Scalar   : Set
    Weight   : Set
    Ket      : Set
    Bra      : Set
    Operator : Set
    Time     : Set

    evolveKet : Time → Time → Ket → Ket
    evolveBra : Time → Time → Bra → Bra
    apply     : Operator → Ket → Ket
    pair      : Bra → Ket → Scalar
    normSquared : Scalar → Weight
    divideWeight : Weight → Weight → Weight
    Positive : Weight → Set

------------------------------------------------------------------------
-- Pre/post-selected ensemble
------------------------------------------------------------------------

record TSVFEnsemble (Q : QuantumSurface) : Set where
  constructor prePostSelected
  field
    initialTime : QuantumSurface.Time Q
    middleTime  : QuantumSurface.Time Q
    finalTime   : QuantumSurface.Time Q

    initialKet : QuantumSurface.Ket Q
    finalBra   : QuantumSurface.Bra Q

open TSVFEnsemble public

forwardState :
  {Q : QuantumSurface} →
  TSVFEnsemble Q →
  QuantumSurface.Ket Q
forwardState {Q} E =
  QuantumSurface.evolveKet Q
    (initialTime E)
    (middleTime E)
    (initialKet E)

backwardState :
  {Q : QuantumSurface} →
  TSVFEnsemble Q →
  QuantumSurface.Bra Q
backwardState {Q} E =
  QuantumSurface.evolveBra Q
    (finalTime E)
    (middleTime E)
    (finalBra E)

record TwoStateVector (Q : QuantumSurface) : Set where
  constructor twoState
  field
    backward : QuantumSurface.Bra Q
    forward  : QuantumSurface.Ket Q

twoStateAt :
  {Q : QuantumSurface} →
  TSVFEnsemble Q →
  TwoStateVector Q
twoStateAt E = twoState (backwardState E) (forwardState E)

------------------------------------------------------------------------
-- Transition amplitudes and the ABL rule
------------------------------------------------------------------------

transitionAmplitude :
  {Q : QuantumSurface} →
  TSVFEnsemble Q →
  QuantumSurface.Operator Q →
  QuantumSurface.Scalar Q
transitionAmplitude {Q} E projector =
  QuantumSurface.pair Q
    (backwardState E)
    (QuantumSurface.apply Q projector (forwardState E))

transitionWeight :
  {Q : QuantumSurface} →
  TSVFEnsemble Q →
  QuantumSurface.Operator Q →
  QuantumSurface.Weight Q
transitionWeight {Q} E projector =
  QuantumSurface.normSquared Q (transitionAmplitude E projector)

-- A projective measurement supplies its outcome projectors and the exact sum
-- of all path weights.  Finiteness/orthogonality/completeness can be supplied
-- by a later concrete Hilbert-space layer.
record ProjectiveMeasurement (Q : QuantumSurface) : Set₁ where
  field
    Outcome : Set
    projector : Outcome → QuantumSurface.Operator Q

    totalPathWeight :
      TSVFEnsemble Q →
      QuantumSurface.Weight Q

record ABLContext
  (Q : QuantumSurface)
  (M : ProjectiveMeasurement Q)
  (E : TSVFEnsemble Q) : Set where
  constructor ablContext
  field
    denominatorPositive :
      QuantumSurface.Positive Q
        (ProjectiveMeasurement.totalPathWeight M E)

ablProbability :
  {Q : QuantumSurface}
  {M : ProjectiveMeasurement Q}
  {E : TSVFEnsemble Q} →
  ABLContext Q M E →
  ProjectiveMeasurement.Outcome M →
  QuantumSurface.Weight Q
ablProbability {Q} {M} {E} context outcome =
  QuantumSurface.divideWeight Q
    (transitionWeight E (ProjectiveMeasurement.projector M outcome))
    (ProjectiveMeasurement.totalPathWeight M E)

------------------------------------------------------------------------
-- Weak values
------------------------------------------------------------------------

record WeakValueSurface (Q : QuantumSurface) : Set₁ where
  field
    divideScalar :
      QuantumSurface.Scalar Q →
      QuantumSurface.Scalar Q →
      QuantumSurface.Scalar Q

    overlapAdmissible :
      QuantumSurface.Scalar Q →
      Set

weakOverlap :
  {Q : QuantumSurface} →
  TSVFEnsemble Q →
  QuantumSurface.Scalar Q
weakOverlap {Q} E =
  QuantumSurface.pair Q (backwardState E) (forwardState E)

record WeakValueContext
  (Q : QuantumSurface)
  (W : WeakValueSurface Q)
  (E : TSVFEnsemble Q) : Set where
  constructor weakContext
  field
    overlapIsAdmissible :
      WeakValueSurface.overlapAdmissible W (weakOverlap E)

weakValue :
  {Q : QuantumSurface}
  (W : WeakValueSurface Q) →
  (E : TSVFEnsemble Q) →
  WeakValueContext Q W E →
  QuantumSurface.Operator Q →
  QuantumSurface.Scalar Q
weakValue {Q} W E context observable =
  WeakValueSurface.divideScalar W
    (transitionAmplitude E observable)
    (weakOverlap E)

------------------------------------------------------------------------
-- Time reversal / TSVF fold
------------------------------------------------------------------------

record TSVFTimeReversal (Q : QuantumSurface) : Set₁ where
  field
    reverseKet : QuantumSurface.Ket Q → QuantumSurface.Ket Q
    reverseBra : QuantumSurface.Bra Q → QuantumSurface.Bra Q
    reverseTime : QuantumSurface.Time Q → QuantumSurface.Time Q

    reverseKet-involutive :
      (x : QuantumSurface.Ket Q) →
      reverseKet (reverseKet x) ≡ x

    reverseBra-involutive :
      (x : QuantumSurface.Bra Q) →
      reverseBra (reverseBra x) ≡ x

    reverseTime-involutive :
      (t : QuantumSurface.Time Q) →
      reverseTime (reverseTime t) ≡ t

    ketEvolutionCovariant :
      (from to : QuantumSurface.Time Q)
      (state : QuantumSurface.Ket Q) →
      reverseKet (QuantumSurface.evolveKet Q from to state)
      ≡
      QuantumSurface.evolveKet Q
        (reverseTime to)
        (reverseTime from)
        (reverseKet state)

    braEvolutionCovariant :
      (from to : QuantumSurface.Time Q)
      (state : QuantumSurface.Bra Q) →
      reverseBra (QuantumSurface.evolveBra Q from to state)
      ≡
      QuantumSurface.evolveBra Q
        (reverseTime to)
        (reverseTime from)
        (reverseBra state)

------------------------------------------------------------------------
-- Recovery of ordinary one-boundary quantum predictions
------------------------------------------------------------------------

record BornMarginalRecovery
  (Q : QuantumSurface)
  (M : ProjectiveMeasurement Q) : Set₁ where
  field
    ForwardPrediction : Set
    BackwardRetrodiction : Set

    marginalizeFinal :
      QuantumSurface.Ket Q →
      ForwardPrediction

    marginalizeInitial :
      QuantumSurface.Bra Q →
      BackwardRetrodiction

-- This record is the theorem surface on which a concrete implementation must
-- prove that summing/forgetting the post-selection recovers the Born rule,
-- and dually for retrodiction.  The abstract TSVF syntax alone cannot prove
-- those analytic facts without a concrete scalar sum and completeness law.

------------------------------------------------------------------------
-- Interpretation boundary
------------------------------------------------------------------------

-- TSVF provides time-symmetric two-boundary conditioning.  Neither
-- ABLContext nor TSVFTimeReversal entails controllable backward signalling.
-- Ontological retrocausality is a separate interpretation/promotion gate.
