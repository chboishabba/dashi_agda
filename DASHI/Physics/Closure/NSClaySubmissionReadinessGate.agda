module DASHI.Physics.Closure.NSClaySubmissionReadinessGate where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_)

------------------------------------------------------------------------
-- Fail-closed distinction between a formal architecture, inhabited analytic
-- leaves, a complete theorem, a public manuscript, and prize-level acceptance.
--
-- This module deliberately grants no route from repository size, CI success,
-- executable diagnostics, or theorem-surface completeness to a claimed proof of
-- the three-dimensional Navier--Stokes regularity problem.
------------------------------------------------------------------------

record ConcretePeriodicNSStatement (ℓ : Level) : Set (lsuc ℓ) where
  field
    SmoothDivergenceFreeInitialDatum : Set ℓ
    GlobalSmoothSolution : SmoothDivergenceFreeInitialDatum → Set ℓ
    Unique : ∀ {u₀} → GlobalSmoothSolution u₀ → Set ℓ
    FiniteEnergy : SmoothDivergenceFreeInitialDatum → Set ℓ

open ConcretePeriodicNSStatement public

record AnalyticCutsetInhabited
    {ℓ : Level}
    (S : ConcretePeriodicNSStatement ℓ) : Set (lsuc ℓ) where
  field
    cutoffUniformIntegerShellSchur : Set ℓ
    farLowCommutatorCancellation : Set ℓ
    uniformFarTailDecay : Set ℓ
    concreteAubinLionsLimit : Set ℓ
    invariantCompactGammaRegion : Set ℓ
    gammaCoerciveDifferentialInequality : Set ℓ
    offPacketDifferentialInequality : Set ℓ
    fiveHalvesBernsteinEnvelope : Set ℓ
    realFundamentalTheoremIntegration : Set ℓ
    nonCircularFiniteVorticityExpenditure : Set ℓ

open AnalyticCutsetInhabited public

record CompleteKernelTheorem
    {ℓ : Level}
    (S : ConcretePeriodicNSStatement ℓ)
    (A : AnalyticCutsetInhabited S) : Set (lsuc ℓ) where
  field
    globalExistence :
      (u₀ : SmoothDivergenceFreeInitialDatum S) →
      FiniteEnergy S u₀ →
      GlobalSmoothSolution S u₀

    uniqueness :
      ∀ {u₀} (solution : GlobalSmoothSolution S u₀) →
      Unique S solution

    noConditionalHypothesisEscapes : Set ℓ
    noPostulateOrUninhabitedRecordEscapes : Set ℓ
    theoremMatchesPublishedProblemStatement : Set ℓ

open CompleteKernelTheorem public

record ManuscriptReadiness
    {ℓ : Level}
    (S : ConcretePeriodicNSStatement ℓ)
    (A : AnalyticCutsetInhabited S)
    (T : CompleteKernelTheorem S A) : Set (lsuc ℓ) where
  field
    humanReadableProof : Set ℓ
    definitionsAndNormalizationsFixed : Set ℓ
    everyAgdaLemmaMappedToManuscript : Set ℓ
    dependencyAndAxiomAuditPublished : Set ℓ
    reproduciblePinnedBuild : Set ℓ
    comparisonWithClassicalLiterature : Set ℓ
    explicitNovelLemmaAndFailureModes : Set ℓ
    specialistPreSubmissionReview : Set ℓ

open ManuscriptReadiness public

record PublicAcceptanceReadiness
    {ℓ : Level}
    (S : ConcretePeriodicNSStatement ℓ)
    (A : AnalyticCutsetInhabited S)
    (T : CompleteKernelTheorem S A)
    (M : ManuscriptReadiness S A T) : Set (lsuc ℓ) where
  field
    publicationInQualifyingVenue : Set ℓ
    publicationAgeRequirementMet : Set ℓ
    generalMathematicalCommunityAcceptance : Set ℓ
    independentExpertVerification : Set ℓ

open PublicAcceptanceReadiness public

-- A submission-ready package necessarily contains the concrete theorem and the
-- human-readable/auditable manuscript package.  It is not produced from CI or
-- architecture alone.
SubmissionReady :
  ∀ {ℓ}
    {S : ConcretePeriodicNSStatement ℓ}
    {A : AnalyticCutsetInhabited S} →
  CompleteKernelTheorem S A → Set (lsuc ℓ)
SubmissionReady {S = S} {A = A} T = ManuscriptReadiness S A T

PrizeConsiderationReady :
  ∀ {ℓ}
    {S : ConcretePeriodicNSStatement ℓ}
    {A : AnalyticCutsetInhabited S}
    {T : CompleteKernelTheorem S A} →
  ManuscriptReadiness S A T → Set (lsuc ℓ)
PrizeConsiderationReady {S = S} {A = A} {T = T} M =
  PublicAcceptanceReadiness S A T M

record CurrentNSFrontier
    {ℓ : Level}
    (S : ConcretePeriodicNSStatement ℓ) : Set (lsuc ℓ) where
  field
    theoremArchitecture : Set ℓ
    namedAnalyticLeaves : Set ℓ
    computationalDiagnostics : Set ℓ

    -- These are intentionally separate and cannot be inferred from the three
    -- fields above.
    analyticCutset : AnalyticCutsetInhabited S → Set ℓ
    completeTheorem :
      (A : AnalyticCutsetInhabited S) → CompleteKernelTheorem S A → Set ℓ

open CurrentNSFrontier public
