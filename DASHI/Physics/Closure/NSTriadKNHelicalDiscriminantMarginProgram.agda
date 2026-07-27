module DASHI.Physics.Closure.NSTriadKNHelicalDiscriminantMarginProgram where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Peter J. Goulart; Sergei V. Chernyshenko.
-- Title: "Global stability analysis of fluid flows using sum-of-squares".
-- Venue/year: Physica D 241 (2012), 692--704.
-- DOI: 10.1016/j.physd.2011.12.008.
-- Uses: finite-dimensional polynomial/SOS certification methodology.
-- Relationship: formalises certificate soundness and the separate
-- finite-to-uniform core/tail bridge.  A fixed-cutoff certificate is never
-- promoted to a cutoff-uniform theorem by itself.
--
-- Corrected mathematical framing (2026-07): The modewise helicity balance
-- of the six-mode witness means that any SOS certificate must fail on the
-- restricted algebraic variety |u_k^+| = |u_k^-|, not just on the
-- isolated witness.  The remaining open obligations (cutoff-uniform
-- commutator, Schur and signed-class bounds) are the relevant leaves.
-- Physical-space flux locality (arXiv:1101.2193, Dascaliuc and Grujic)
-- provides methodological evidence for power-law decay in scale-disparity
-- but does not automatically yield: deterministic pointwise-in-state
-- Fourier multiplier commutator estimates, bounds uniform over all
-- Galerkin cutoffs N, the exact Sobolev-weighted Schur sums, or
-- favourable signs for each of the seven geometric classes and eight
-- helicity triples.  Substantial translation is required.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat.Base using (_≤_; _<_; _-_)

record CandidateExactReserves
    {c s : Level} : Set (lsuc (c ⊔ s)) where
  field
    Cutoff : Set c
    State : Set s

    quadraticReserve cubicContribution quarticReserve :
      Cutoff → State → Nat

    literalQuadraticReserve literalCubicContribution
      literalQuarticReserve :
      Cutoff → State → Nat

    candidateQuadraticReserveExact :
      ∀ cutoff state →
      quadraticReserve cutoff state
      ≡ literalQuadraticReserve cutoff state

    candidateCubicContributionExact :
      ∀ cutoff state →
      cubicContribution cutoff state
      ≡ literalCubicContribution cutoff state

    candidateQuarticReserveExact :
      ∀ cutoff state →
      quarticReserve cutoff state
      ≡ literalQuarticReserve cutoff state

    candidateQuadraticReserveNonnegative :
      ∀ cutoff state → 0 ≤ quadraticReserve cutoff state

    candidateQuarticReserveNonnegative :
      ∀ cutoff state → 0 ≤ quarticReserve cutoff state

    scaleState : Nat → State → State

    candidateQuadraticHomogeneous :
      ∀ cutoff amplitude state →
      quadraticReserve cutoff (scaleState amplitude state)
      ≡ amplitude * amplitude * quadraticReserve cutoff state

    candidateCubicHomogeneous :
      ∀ cutoff amplitude state →
      cubicContribution cutoff (scaleState amplitude state)
      ≡ amplitude * amplitude * amplitude * cubicContribution cutoff state

    candidateQuarticHomogeneous :
      ∀ cutoff amplitude state →
      quarticReserve cutoff (scaleState amplitude state)
      ≡ amplitude * amplitude * amplitude * amplitude
        * quarticReserve cutoff state

open CandidateExactReserves public

normalisedShapeDiscriminant :
  ∀ {c s} (R : CandidateExactReserves {c} {s}) →
  Cutoff R → State R → Nat
normalisedShapeDiscriminant R cutoff state =
  4 * quadraticReserve R cutoff state * quarticReserve R cutoff state

normalisedShapeDiscriminantDefect :
  ∀ {c s} (R : CandidateExactReserves {c} {s}) →
  Cutoff R → State R → Nat
normalisedShapeDiscriminantDefect R cutoff state =
  cubicContribution R cutoff state * cubicContribution R cutoff state

normalisedShapeDiscriminantDefinition :
  ∀ {c s} (R : CandidateExactReserves {c} {s})
    (cutoff : Cutoff R) (state : State R) →
  normalisedShapeDiscriminant R cutoff state
  ≡ 4 * quadraticReserve R cutoff state * quarticReserve R cutoff state
normalisedShapeDiscriminantDefinition R cutoff state = refl

record FixedCutoffSOSCertificate
    {c s p : Level}
    (R : CandidateExactReserves {c} {s}) : Set (lsuc (c ⊔ s ⊔ p)) where
  field
    fixedCutoff : Cutoff R
    Polynomial : Set p

    admissibleStateRationalCoordinateChart :
      State R → Polynomial
    normalisationConstraintPolynomial :
      State R → Polynomial
    boundaryConstraintPolynomial :
      State R → Polynomial
    candidateDiscriminantPolynomial :
      State R → Polynomial

    SOSCertificate : Set p
    certificate : SOSCertificate
    CertificateValid : SOSCertificate → Set p

    rationalSOSCertificateSound :
      CertificateValid certificate →
      ∀ state →
      normalisedShapeDiscriminantDefect R fixedCutoff state
      ≤ normalisedShapeDiscriminant R fixedCutoff state

    fixedCutoffPositiveDiscriminantMargin :
      ∀ state →
      normalisedShapeDiscriminantDefect R fixedCutoff state
      ≤ normalisedShapeDiscriminant R fixedCutoff state

open FixedCutoffSOSCertificate public

record NormalisedShapeCoreTailPromotion
    {c s : Level}
    (R : CandidateExactReserves {c} {s}) : Set (lsuc (c ⊔ s)) where
  field
    NormalisedShape : Cutoff R → State R → Set
    Core Tail : State R → State R
    combineState : State R → State R → State R

    normalisedShapeCoreTailDecomposition :
      ∀ cutoff state →
      NormalisedShape cutoff state →
      state ≡ combineState (Core state) (Tail state)

    coreTailReservesExactSplit :
      ∀ cutoff state →
      quadraticReserve R cutoff state ≡
      quadraticReserve R cutoff (Core state)
      + quadraticReserve R cutoff (Tail state)

    coreTailCubicExactSplit :
      ∀ cutoff state →
      cubicContribution R cutoff state ≡
      cubicContribution R cutoff (Core state)
      + cubicContribution R cutoff (Tail state)

    highTailDiscriminantReserve :
      (cutoff : Cutoff R) (state : State R) → Nat

    mixedCoreTailDiscriminantErrorBound :
      (cutoff : Cutoff R) (state : State R) → Nat

    mixedErrorAbsorbedByTailReserve :
      ∀ cutoff state →
      mixedCoreTailDiscriminantErrorBound cutoff state
      ≤ highTailDiscriminantReserve cutoff state

    finiteCoreMarginStableUnderTailPerturbation :
      ∀ cutoff state →
      NormalisedShape cutoff state →
      normalisedShapeDiscriminantDefect R cutoff (Core state)
      ≤ normalisedShapeDiscriminant R cutoff (Core state)

    etaNumerator etaDenominator : Nat
    etaPositive : 0 < etaNumerator
    etaLessThanOne : etaNumerator < etaDenominator

    uniformEtaIndependentOfChartAndCutoff :
      ∀ cutoff state → etaNumerator < etaDenominator

    uniformNormalisedShapeDiscriminantMargin :
      ∀ cutoff state →
      NormalisedShape cutoff state →
      etaDenominator * etaDenominator
        * normalisedShapeDiscriminantDefect R cutoff state
      ≤
      (etaDenominator - etaNumerator)
      * (etaDenominator - etaNumerator)
      * normalisedShapeDiscriminant R cutoff state

open NormalisedShapeCoreTailPromotion public

record ExactCounterexamplePromotion
    {c s : Level}
    (R : CandidateExactReserves {c} {s}) : Set (lsuc (c ⊔ s)) where
  field
    counterexampleCutoff : Cutoff R
    counterexampleState : State R

    CutoffMembership Reality DivergenceFree BoundaryAdmissible :
      Cutoff R → State R → Set
    NormalisedNonzero : Cutoff R → State R → Set

    counterexampleCutoffMembership :
      CutoffMembership counterexampleCutoff counterexampleState
    counterexampleReality :
      Reality counterexampleCutoff counterexampleState
    counterexampleDivergenceFree :
      DivergenceFree counterexampleCutoff counterexampleState
    counterexampleBoundaryAdmissible :
      BoundaryAdmissible counterexampleCutoff counterexampleState
    counterexampleNormalisedNonzero :
      NormalisedNonzero counterexampleCutoff counterexampleState

    counterexampleQuadraticReserveExact :
      quadraticReserve R counterexampleCutoff counterexampleState ≡
      literalQuadraticReserve R counterexampleCutoff counterexampleState
    counterexampleCubicContributionExact :
      cubicContribution R counterexampleCutoff counterexampleState ≡
      literalCubicContribution R counterexampleCutoff counterexampleState
    counterexampleQuarticReserveExact :
      quarticReserve R counterexampleCutoff counterexampleState ≡
      literalQuarticReserve R counterexampleCutoff counterexampleState

    counterexampleDiscriminantStrictlyNegative :
      normalisedShapeDiscriminant R counterexampleCutoff counterexampleState
      < normalisedShapeDiscriminantDefect R counterexampleCutoff counterexampleState

    LargerCutoff : Cutoff R → Set
    embedState : Cutoff R → State R → State R

    counterexampleEmbedsIntoLargerCutoffs :
      ∀ cutoff →
      LargerCutoff cutoff →
      CutoffMembership cutoff (embedState cutoff counterexampleState)

    counterexampleBoundaryPreservedByEmbedding :
      ∀ cutoff →
      LargerCutoff cutoff →
      BoundaryAdmissible cutoff (embedState cutoff counterexampleState)

    counterexampleRefutesEveryPositiveUniformEta :
      ∀ etaNumerator etaDenominator →
      0 < etaNumerator →
      etaNumerator < etaDenominator →
      Set

open ExactCounterexamplePromotion public

helicalDiscriminantProgrammeRepresented : Bool
helicalDiscriminantProgrammeRepresented = true

helicalDiscriminantProgrammeRepresentedIsTrue :
  helicalDiscriminantProgrammeRepresented ≡ true
helicalDiscriminantProgrammeRepresentedIsTrue = refl

fixedCutoffSOSCertificateConstructed : Bool
fixedCutoffSOSCertificateConstructed = false

fixedCutoffSOSCertificateConstructedIsFalse :
  fixedCutoffSOSCertificateConstructed ≡ false
fixedCutoffSOSCertificateConstructedIsFalse = refl

uniformHelicalDiscriminantMarginClosed : Bool
uniformHelicalDiscriminantMarginClosed = false

uniformHelicalDiscriminantMarginClosedIsFalse :
  uniformHelicalDiscriminantMarginClosed ≡ false
uniformHelicalDiscriminantMarginClosedIsFalse = refl
