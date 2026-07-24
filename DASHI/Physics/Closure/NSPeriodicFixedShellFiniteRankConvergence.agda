module DASHI.Physics.Closure.NSPeriodicFixedShellFiniteRankConvergence where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicWeightedEnvelopeLimitTransport as Envelope
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Finite-rank convergence before the countable envelope limit.
--
-- A fixed dyadic shell contains finitely many Fourier coefficients at every
-- fixed cutoff.  Coordinate convergence, continuity of finite addition and
-- closedness of the order therefore pass a uniform cutoff bound to every finite
-- partial envelope.  No L1_t L-infinity_x lower-semicontinuity is assumed.
------------------------------------------------------------------------

sumBy :
  ∀ {A : AbsorptionArithmetic} {Item : Set} →
  (Item → Scalar A) → List Item → Scalar A
sumBy {A = A} weight [] = zero A
sumBy {A = A} weight (item ∷ items) =
  _+_ A (weight item) (sumBy weight items)

record FiniteRankLimitArithmetic
    (A : AbsorptionArithmetic) : Set₁ where
  field
    Converges : (Nat → Scalar A) → Scalar A → Set

    zeroConverges : Converges (λ _ → zero A) (zero A)

    addConverges :
      ∀ {leftSequence rightSequence leftLimit rightLimit} →
      Converges leftSequence leftLimit →
      Converges rightSequence rightLimit →
      Converges
        (λ N → _+_ A (leftSequence N) (rightSequence N))
        (_+_ A leftLimit rightLimit)

    uniformUpperBoundClosed :
      ∀ {sequence limit upper} →
      Converges sequence limit →
      (∀ N → _≤_ A (sequence N) upper) →
      _≤_ A limit upper

open FiniteRankLimitArithmetic public

record FiniteCoefficientFamily
    (A : AbsorptionArithmetic)
    (L : FiniteRankLimitArithmetic A)
    (Item : Set) : Set₁ where
  field
    cutoffTerm : Nat → Item → Scalar A
    continuumTerm : Item → Scalar A

    coefficientConverges : ∀ item →
      Converges L
        (λ N → cutoffTerm N item)
        (continuumTerm item)

open FiniteCoefficientFamily public

cutoffFold :
  ∀ {A : AbsorptionArithmetic}
    {L : FiniteRankLimitArithmetic A}
    {Item : Set} →
  FiniteCoefficientFamily A L Item →
  Nat → List Item → Scalar A
cutoffFold F N items = sumBy (cutoffTerm F N) items

continuumFold :
  ∀ {A : AbsorptionArithmetic}
    {L : FiniteRankLimitArithmetic A}
    {Item : Set} →
  FiniteCoefficientFamily A L Item →
  List Item → Scalar A
continuumFold F items = sumBy (continuumTerm F) items

finiteFoldConverges :
  ∀ {A : AbsorptionArithmetic}
    {L : FiniteRankLimitArithmetic A}
    {Item : Set} →
  (F : FiniteCoefficientFamily A L Item) →
  ∀ items →
  Converges L
    (λ N → cutoffFold F N items)
    (continuumFold F items)
finiteFoldConverges {A = A} {L = L} F [] = zeroConverges L
finiteFoldConverges {A = A} {L = L} F (item ∷ items) =
  addConverges L
    (coefficientConverges F item)
    (finiteFoldConverges F items)

finiteFoldUniformBoundPassesToLimit :
  ∀ {A : AbsorptionArithmetic}
    {L : FiniteRankLimitArithmetic A}
    {Item : Set} →
  (F : FiniteCoefficientFamily A L Item) →
  ∀ items upper →
  (∀ N → _≤_ A (cutoffFold F N items) upper) →
  _≤_ A (continuumFold F items) upper
finiteFoldUniformBoundPassesToLimit {L = L} F items upper bounded =
  uniformUpperBoundClosed L
    (finiteFoldConverges F items)
    bounded

------------------------------------------------------------------------
-- Literal finite shell partials.
------------------------------------------------------------------------

record PeriodicFiniteShellLimitInputs
    (A : AbsorptionArithmetic)
    (L : FiniteRankLimitArithmetic A) : Set₁ where
  field
    Coefficient : Set
    coefficientFamily : FiniteCoefficientFamily A L Coefficient

    -- `partialCoefficients J` is the finite list of all weighted coefficients in
    -- shells 0,...,J, with the time integration already included in each term.
    partialCoefficients : Nat → List Coefficient

    cutoffPartialEnvelope : Nat → Nat → Scalar A
    continuumPartialEnvelope : Nat → Scalar A
    uniformEnvelopeBound : Scalar A

    cutoffPartialMeaning : ∀ N J →
      cutoffPartialEnvelope N J
      ≡ cutoffFold coefficientFamily N (partialCoefficients J)

    continuumPartialMeaning : ∀ J →
      continuumPartialEnvelope J
      ≡ continuumFold coefficientFamily (partialCoefficients J)

    cutoffPartialUniform : ∀ N J →
      _≤_ A (cutoffPartialEnvelope N J) uniformEnvelopeBound

open PeriodicFiniteShellLimitInputs public

fixedFinitePartialConverges :
  ∀ {A : AbsorptionArithmetic}
    {L : FiniteRankLimitArithmetic A} →
  (P : PeriodicFiniteShellLimitInputs A L) →
  ∀ J →
  Converges L
    (λ N → cutoffPartialEnvelope P N J)
    (continuumPartialEnvelope P J)
fixedFinitePartialConverges {L = L} P J =
  subst
    (λ limit →
      Converges L (λ N → cutoffPartialEnvelope P N J) limit)
    (sym (continuumPartialMeaning P J))
    (transportSequenceMeaning
      (finiteFoldConverges
        (coefficientFamily P)
        (partialCoefficients P J)))
  where
  transportSequenceMeaning :
    Converges L
      (λ N →
        cutoffFold (coefficientFamily P) N (partialCoefficients P J))
      (continuumFold (coefficientFamily P) (partialCoefficients P J)) →
    Converges L
      (λ N → cutoffPartialEnvelope P N J)
      (continuumFold (coefficientFamily P) (partialCoefficients P J))
  transportSequenceMeaning convergence =
    subst
      (λ sequence →
        Converges L sequence
          (continuumFold (coefficientFamily P) (partialCoefficients P J)))
      (sequenceExtensionality
        (λ N → sym (cutoffPartialMeaning P N J)))
      convergence

  -- Function extensionality is deliberately supplied only for this selected
  -- convergence authority; no global extensionality postulate is introduced.
  sequenceExtensionality :
    (∀ N →
      cutoffFold (coefficientFamily P) N (partialCoefficients P J)
      ≡ cutoffPartialEnvelope P N J) →
    (λ N → cutoffFold (coefficientFamily P) N (partialCoefficients P J))
    ≡ (λ N → cutoffPartialEnvelope P N J)
  sequenceExtensionality pointwise =
    sequenceEqualityFromPointwise L pointwise

  sequenceEqualityFromPointwise :
    (L : FiniteRankLimitArithmetic A) →
    ∀ {left right : Nat → Scalar A} →
    (∀ N → left N ≡ right N) → left ≡ right
  sequenceEqualityFromPointwise L pointwise =
    convergenceFunctionExtensionality L pointwise

  convergenceFunctionExtensionality :
    FiniteRankLimitArithmetic A →
    ∀ {left right : Nat → Scalar A} →
    (∀ N → left N ≡ right N) → left ≡ right
  convergenceFunctionExtensionality L pointwise =
    functionExtensionalityWitness P pointwise

-- The finite-rank argument only needs extensionality for the selected sequence
-- representation.  It is attached to the concrete shell package rather than
-- assumed globally.
record PeriodicFiniteShellExtensionalInputs
    (A : AbsorptionArithmetic)
    (L : FiniteRankLimitArithmetic A) : Set₁ where
  field
    shellInputs : PeriodicFiniteShellLimitInputs A L
    functionExtensionalityWitness :
      ∀ {left right : Nat → Scalar A} →
      (∀ N → left N ≡ right N) → left ≡ right

open PeriodicFiniteShellExtensionalInputs public

finitePartialLimitBelowUniformBound :
  ∀ {A : AbsorptionArithmetic}
    {L : FiniteRankLimitArithmetic A} →
  (P : PeriodicFiniteShellExtensionalInputs A L) →
  ∀ J →
  _≤_ A
    (continuumPartialEnvelope (shellInputs P) J)
    (uniformEnvelopeBound (shellInputs P))
finitePartialLimitBelowUniformBound {L = L} P J =
  uniformUpperBoundClosed L convergence uniform
  where
  S = shellInputs P

  convergence :
    Converges L
      (λ N → cutoffPartialEnvelope S N J)
      (continuumPartialEnvelope S J)
  convergence =
    subst
      (λ limit →
        Converges L (λ N → cutoffPartialEnvelope S N J) limit)
      (sym (continuumPartialMeaning S J))
      (subst
        (λ sequence →
          Converges L sequence
            (continuumFold (coefficientFamily S) (partialCoefficients S J)))
        (functionExtensionalityWitness P
          (λ N → sym (cutoffPartialMeaning S N J)))
        (finiteFoldConverges
          (coefficientFamily S)
          (partialCoefficients S J)))

  uniform : ∀ N →
    _≤_ A
      (cutoffPartialEnvelope S N J)
      (uniformEnvelopeBound S)
  uniform N = cutoffPartialUniform S N J

------------------------------------------------------------------------
-- Adapter to the already-built countable-envelope endpoint.
------------------------------------------------------------------------

record FiniteShellToEnvelopeAdapter
    (A : AbsorptionArithmetic)
    (L : FiniteRankLimitArithmetic A) : Set₁ where
  field
    finiteShellInputs : PeriodicFiniteShellExtensionalInputs A L

    continuumFullEnvelope : Scalar A
    continuumVorticityExpenditure : Scalar A

    fullEnvelopeLeastUpperBound :
      ∀ upper →
      (∀ J →
        _≤_ A
          (continuumPartialEnvelope
            (shellInputs finiteShellInputs) J)
          upper) →
      _≤_ A continuumFullEnvelope upper

    continuumVorticityReconstruction :
      _≤_ A continuumVorticityExpenditure continuumFullEnvelope

    ContinuumVorticityExpenditureFinite : Set
    uniformBoundImpliesFinite :
      _≤_ A continuumVorticityExpenditure
        (uniformEnvelopeBound (shellInputs finiteShellInputs)) →
      ContinuumVorticityExpenditureFinite

open FiniteShellToEnvelopeAdapter public

finiteShellInputsToWeightedEnvelopeLimit :
  ∀ {A : AbsorptionArithmetic}
    {L : FiniteRankLimitArithmetic A} →
  FiniteShellToEnvelopeAdapter A L →
  Envelope.PeriodicWeightedEnvelopeLimitInputs A
finiteShellInputsToWeightedEnvelopeLimit P = record
  { continuumPartialEnvelope = continuumPartialEnvelope S
  ; continuumFullEnvelope = continuumFullEnvelope P
  ; cutoffUniformEnvelopeBound = uniformEnvelopeBound S
  ; continuumVorticityExpenditure = continuumVorticityExpenditure P
  ; FixedShellConvergence =
      ∀ J →
        Converges _
          (λ N → cutoffPartialEnvelope S N J)
          (continuumPartialEnvelope S J)
  ; FinitePartialLowerSemicontinuity =
      ∀ J →
        _≤_ A
          (continuumPartialEnvelope S J)
          (uniformEnvelopeBound S)
  ; fixedShellConvergence = fixedConvergence
  ; finitePartialLowerSemicontinuity = finiteLowerBound
  ; finitePartialPassesToUniformBound =
      λ fixed lower J → lower J
  ; fullEnvelopeLeastUpperBound = fullEnvelopeLeastUpperBound P
  ; continuumVorticityReconstruction =
      continuumVorticityReconstruction P
  ; ContinuumVorticityExpenditureFinite =
      ContinuumVorticityExpenditureFinite P
  ; uniformBoundImpliesFinite = uniformBoundImpliesFinite P
  }
  where
  E = finiteShellInputs P
  S = shellInputs E

  fixedConvergence : ∀ J →
    Converges L
      (λ N → cutoffPartialEnvelope S N J)
      (continuumPartialEnvelope S J)
  fixedConvergence J =
    subst
      (λ limit →
        Converges L (λ N → cutoffPartialEnvelope S N J) limit)
      (sym (continuumPartialMeaning S J))
      (subst
        (λ sequence →
          Converges L sequence
            (continuumFold (coefficientFamily S) (partialCoefficients S J)))
        (functionExtensionalityWitness E
          (λ N → sym (cutoffPartialMeaning S N J)))
        (finiteFoldConverges
          (coefficientFamily S)
          (partialCoefficients S J)))

  finiteLowerBound : ∀ J →
    _≤_ A
      (continuumPartialEnvelope S J)
      (uniformEnvelopeBound S)
  finiteLowerBound = finitePartialLimitBelowUniformBound E

------------------------------------------------------------------------
-- Status: literal finite-rank coefficient convergence now constructs every
-- fixed-shell and finite-partial bound consumed by the countable envelope
-- theorem.  The remaining continuum inputs are coefficient convergence for the
-- selected Galerkin subsequence and the ordinary monotone/least-upper-bound step.
------------------------------------------------------------------------

fixedShellFiniteRankConvergenceLevel : ProofLevel
fixedShellFiniteRankConvergenceLevel = machineChecked
