module DASHI.Physics.Closure.NSTriadKNLuoPublishedContinuationAuthorityExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal/year: Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- SOURCE STATEMENT
-- Under the unit-viscosity normalization, regularity on (0,T] follows from
--
--   limsup_{p -> infinity}
--     integral_{T-c lambda_p^-2}^T ||nabla u_{<=p}||_infinity dt
--       <= delta_BKM.
--
-- A pointwise bound by the same universal threshold for every cutoff is a
-- stronger hypothesis and therefore supplies the source limsup bound.  This
-- module owns that assembly explicitly.  The repository must still identify
-- its solution, smooth projector and terminal-window integrals with the source
-- quantities.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record PublishedLuoTheorem11Authority
    {d s t : Level}
    (InitialDatum : Set d)
    (Solution : Set s)
    (Time : Set t) : Set (lsuc (d ⊔ s ⊔ t)) where
  field
    SmoothDivergenceFreeFiniteEnergy : InitialDatum → Set (d ⊔ s)
    SolvesPeriodicNavierStokesFrom :
      InitialDatum → Solution → Set (d ⊔ s)

    UnitViscosityNormalization : Set
    periodicDomainMatchesSource : UnitViscosityNormalization

    localizedGradientIntegral :
      Solution → Time → Nat → ℚ

    universalDeltaBKM : ℚ

    LuoLocalizedGradientLimsupBound :
      Solution → Time → Set (s ⊔ t)

    pointwiseThresholdImpliesLimsupBound :
      (solution : Solution) →
      (terminal : Time) →
      ((shell : Nat) →
        localizedGradientIntegral solution terminal shell
          ≤ universalDeltaBKM) →
      LuoLocalizedGradientLimsupBound solution terminal

    RegularOnOpenTerminalInterval :
      Solution → Time → Set (s ⊔ t)

    ContinuesBeyond : InitialDatum → Time → Set (d ⊔ t)

    theorem11Regularity :
      (initial : InitialDatum) →
      (solution : Solution) →
      (terminal : Time) →
      SmoothDivergenceFreeFiniteEnergy initial →
      SolvesPeriodicNavierStokesFrom initial solution →
      LuoLocalizedGradientLimsupBound solution terminal →
      RegularOnOpenTerminalInterval solution terminal

    regularityGivesContinuation :
      (initial : InitialDatum) →
      (solution : Solution) →
      (terminal : Time) →
      SolvesPeriodicNavierStokesFrom initial solution →
      RegularOnOpenTerminalInterval solution terminal →
      ContinuesBeyond initial terminal

open PublishedLuoTheorem11Authority public

luoTheorem11Continuation :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (A : PublishedLuoTheorem11Authority InitialDatum Solution Time) →
  (initial : InitialDatum) →
  (solution : Solution) →
  (terminal : Time) →
  SmoothDivergenceFreeFiniteEnergy A initial →
  SolvesPeriodicNavierStokesFrom A initial solution →
  LuoLocalizedGradientLimsupBound A solution terminal →
  ContinuesBeyond A initial terminal
luoTheorem11Continuation A initial solution terminal smooth solves localized =
  regularityGivesContinuation A initial solution terminal solves
    (theorem11Regularity A initial solution terminal smooth solves localized)

record LuoRepositoryHypothesisIdentification
    {d s t : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    (A : PublishedLuoTheorem11Authority InitialDatum Solution Time)
    (initial : InitialDatum)
    (solution : Solution)
    (terminal : Time) : Set (lsuc (d ⊔ s ⊔ t)) where
  field
    smoothInitialData : SmoothDivergenceFreeFiniteEnergy A initial
    solvesFromInitialData :
      SolvesPeriodicNavierStokesFrom A initial solution

    repositoryLocalizedIntegral : Nat → ℚ

    repositoryIntegralMatchesSource :
      (shell : Nat) →
      repositoryLocalizedIntegral shell
        ≡ localizedGradientIntegral A solution terminal shell

    repositoryThresholdBound :
      (shell : Nat) →
      repositoryLocalizedIntegral shell ≤ universalDeltaBKM A

open LuoRepositoryHypothesisIdentification public

repositoryPointwiseSourceBound :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {A : PublishedLuoTheorem11Authority InitialDatum Solution Time}
    {initial : InitialDatum}
    {solution : Solution}
    {terminal : Time} →
  (I : LuoRepositoryHypothesisIdentification
    A initial solution terminal) →
  (shell : Nat) →
  localizedGradientIntegral A solution terminal shell
    ≤ universalDeltaBKM A
repositoryPointwiseSourceBound I shell
  rewrite sym (repositoryIntegralMatchesSource I shell) =
  repositoryThresholdBound I shell

repositoryLuoLimsupBound :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {A : PublishedLuoTheorem11Authority InitialDatum Solution Time}
    {initial : InitialDatum}
    {solution : Solution}
    {terminal : Time} →
  (I : LuoRepositoryHypothesisIdentification
    A initial solution terminal) →
  LuoLocalizedGradientLimsupBound A solution terminal
repositoryLuoLimsupBound {A = A} {solution = solution}
  {terminal = terminal} I =
  pointwiseThresholdImpliesLimsupBound A solution terminal
    (repositoryPointwiseSourceBound I)

luoContinuationFromRepositoryCutoffBounds :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {A : PublishedLuoTheorem11Authority InitialDatum Solution Time}
    {initial : InitialDatum}
    {solution : Solution}
    {terminal : Time} →
  (I : LuoRepositoryHypothesisIdentification
    A initial solution terminal) →
  ContinuesBeyond A initial terminal
luoContinuationFromRepositoryCutoffBounds {A = A}
  {initial = initial} {solution = solution} {terminal = terminal} I =
  luoTheorem11Continuation A initial solution terminal
    (smoothInitialData I)
    (solvesFromInitialData I)
    (repositoryLuoLimsupBound I)

luoTheorem11AuthorityLevel : ProofLevel
luoTheorem11AuthorityLevel = standardImported

publishedLuoTheorem11AuthoritySurfaceConstructed : Bool
publishedLuoTheorem11AuthoritySurfaceConstructed = true

pointwiseCutoffToLimsupAssemblyConstructed : Bool
pointwiseCutoffToLimsupAssemblyConstructed = true

luoContinuationAdapterConstructed : Bool
luoContinuationAdapterConstructed = true

selectedPublishedLuoAuthorityInhabited : Bool
selectedPublishedLuoAuthorityInhabited = false

publishedLuoTheorem11AuthoritySurfaceConstructedIsTrue :
  publishedLuoTheorem11AuthoritySurfaceConstructed ≡ true
publishedLuoTheorem11AuthoritySurfaceConstructedIsTrue = refl

pointwiseCutoffToLimsupAssemblyConstructedIsTrue :
  pointwiseCutoffToLimsupAssemblyConstructed ≡ true
pointwiseCutoffToLimsupAssemblyConstructedIsTrue = refl

luoContinuationAdapterConstructedIsTrue :
  luoContinuationAdapterConstructed ≡ true
luoContinuationAdapterConstructedIsTrue = refl

selectedPublishedLuoAuthorityInhabitedIsFalse :
  selectedPublishedLuoAuthorityInhabited ≡ false
selectedPublishedLuoAuthorityInhabitedIsFalse = refl
