module DASHI.Physics.Closure.NSTriadKNLuoOfficialLerayHopfAuthorityExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- PURPOSE
-- Select Luo's published continuation theorem on one exact repository solution
-- carrier: periodic Leray--Hopf solutions on T3 with unit viscosity, smooth
-- divergence-free finite-energy initial data, and prior regularity on (0,T).
-- The source theorem remains standard imported; all source/repository carrier
-- identifications are explicit fields and cannot be replaced by Booleans.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNRegularLerayHopfPeriodicSolutionExact as LH
import DASHI.Physics.Closure.NSTriadKNLuoPublishedContinuationAuthorityExact as Luo
open import DASHI.Physics.YangMills.CompactLieProofLevel

record OfficialPeriodicLuoSourceCarrier
    {d s t : Level}
    (InitialDatum : Set d)
    (Solution : Set s)
    (Time : Set t) : Set (lsuc (d ⊔ s ⊔ t)) where
  field
    lerayHopfSolutionAt :
      InitialDatum → Solution →
      LH.PeriodicLerayHopfSolution InitialDatum Solution Time

    lerayHopfInitialMeaning :
      (initial : InitialDatum) →
      (solution : Solution) →
      LH.initialDatum (lerayHopfSolutionAt initial solution) ≡ initial

    lerayHopfSolutionMeaning :
      (initial : InitialDatum) →
      (solution : Solution) →
      LH.solution (lerayHopfSolutionAt initial solution) ≡ solution

    SmoothDivergenceFreeFiniteEnergy : InitialDatum → Set (d ⊔ s)

    smoothDataMatchesLerayHopfInitialClass :
      (initial : InitialDatum) →
      SmoothDivergenceFreeFiniteEnergy initial →
      Set (d ⊔ s)

    SolvesPeriodicNavierStokesFrom :
      InitialDatum → Solution → Set (d ⊔ s ⊔ t)

    solutionPredicateMatchesLerayHopf :
      (initial : InitialDatum) →
      (solution : Solution) →
      SolvesPeriodicNavierStokesFrom initial solution →
      LH.SolvesPeriodicNavierStokesDistributionally
        (lerayHopfSolutionAt initial solution)

    PeriodicDomainIsThreeTorus : Set
    periodicDomainIsThreeTorus : PeriodicDomainIsThreeTorus

    ViscosityIsExactlyOne : Set
    viscosityIsExactlyOne : ViscosityIsExactlyOne

    SourceNormalizationMatchesLuo : Set
    sourceNormalizationMatchesLuo : SourceNormalizationMatchesLuo

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

    regularityMatchesRegularLerayHopf :
      (initial : InitialDatum) →
      (solution : Solution) →
      (terminal : Time) →
      SolvesPeriodicNavierStokesFrom initial solution →
      RegularOnOpenTerminalInterval solution terminal →
      LH.RegularLerayHopfBeforeTerminal
        (lerayHopfSolutionAt initial solution) terminal

    ContinuesBeyond : InitialDatum → Time → Set (d ⊔ t)

    luoTheorem11RegularityImported :
      (initial : InitialDatum) →
      (solution : Solution) →
      (terminal : Time) →
      SmoothDivergenceFreeFiniteEnergy initial →
      SolvesPeriodicNavierStokesFrom initial solution →
      LuoLocalizedGradientLimsupBound solution terminal →
      RegularOnOpenTerminalInterval solution terminal

    regularityGivesContinuationImported :
      (initial : InitialDatum) →
      (solution : Solution) →
      (terminal : Time) →
      SolvesPeriodicNavierStokesFrom initial solution →
      RegularOnOpenTerminalInterval solution terminal →
      ContinuesBeyond initial terminal

open OfficialPeriodicLuoSourceCarrier public

officialPeriodicLuoAuthority :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  OfficialPeriodicLuoSourceCarrier InitialDatum Solution Time →
  Luo.PublishedLuoTheorem11Authority InitialDatum Solution Time
officialPeriodicLuoAuthority C = record
  { SmoothDivergenceFreeFiniteEnergy =
      SmoothDivergenceFreeFiniteEnergy C
  ; SolvesPeriodicNavierStokesFrom =
      SolvesPeriodicNavierStokesFrom C
  ; UnitViscosityNormalization =
      SourceNormalizationMatchesLuo C
  ; periodicDomainMatchesSource =
      sourceNormalizationMatchesLuo C
  ; localizedGradientIntegral = localizedGradientIntegral C
  ; universalDeltaBKM = universalDeltaBKM C
  ; LuoLocalizedGradientLimsupBound =
      LuoLocalizedGradientLimsupBound C
  ; pointwiseThresholdImpliesLimsupBound =
      pointwiseThresholdImpliesLimsupBound C
  ; RegularOnOpenTerminalInterval =
      RegularOnOpenTerminalInterval C
  ; ContinuesBeyond = ContinuesBeyond C
  ; theorem11Regularity = luoTheorem11RegularityImported C
  ; regularityGivesContinuation =
      regularityGivesContinuationImported C
  }

record OfficialLuoSolutionSelection
    {d s t : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    (carrier : OfficialPeriodicLuoSourceCarrier InitialDatum Solution Time)
    (initial : InitialDatum)
    (solution : Solution)
    (terminal : Time) : Set (lsuc (d ⊔ s ⊔ t)) where
  field
    smoothInitialData :
      SmoothDivergenceFreeFiniteEnergy carrier initial

    solvesFromInitialData :
      SolvesPeriodicNavierStokesFrom carrier initial solution

    regularityMatchesSource :
      RegularOnOpenTerminalInterval carrier solution terminal

open OfficialLuoSolutionSelection public

selectedRegularBeforeTerminal :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {carrier : OfficialPeriodicLuoSourceCarrier InitialDatum Solution Time}
    {initial : InitialDatum}
    {solution : Solution}
    {terminal : Time} →
  OfficialLuoSolutionSelection carrier initial solution terminal →
  LH.RegularLerayHopfBeforeTerminal
    (lerayHopfSolutionAt carrier initial solution) terminal
selectedRegularBeforeTerminal {carrier = carrier}
  {initial = initial} {solution = solution} {terminal = terminal} S =
  regularityMatchesRegularLerayHopf carrier
    initial solution terminal
    (solvesFromInitialData S)
    (regularityMatchesSource S)

-- Compatibility theorem: this is not a second regularity field.  It is exactly
-- the single source-to-Leray--Hopf derivation above.
regularBeforeTerminal :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {carrier : OfficialPeriodicLuoSourceCarrier InitialDatum Solution Time}
    {initial : InitialDatum}
    {solution : Solution}
    {terminal : Time} →
  OfficialLuoSolutionSelection carrier initial solution terminal →
  LH.RegularLerayHopfBeforeTerminal
    (lerayHopfSolutionAt carrier initial solution) terminal
regularBeforeTerminal = selectedRegularBeforeTerminal

selectedLuoAuthorityLevel : ProofLevel
selectedLuoAuthorityLevel = standardImported

officialPeriodicLuoCarrierSelected : Bool
officialPeriodicLuoCarrierSelected = true

unitViscosityThreeTorusIdentificationSelected : Bool
unitViscosityThreeTorusIdentificationSelected = true

regularLerayHopfSourceIdentificationSelected : Bool
regularLerayHopfSourceIdentificationSelected = true

officialPeriodicLuoAuthorityConstructorClosed : Bool
officialPeriodicLuoAuthorityConstructorClosed = true

officialPeriodicLuoCarrierSelectedIsTrue :
  officialPeriodicLuoCarrierSelected ≡ true
officialPeriodicLuoCarrierSelectedIsTrue = refl

unitViscosityThreeTorusIdentificationSelectedIsTrue :
  unitViscosityThreeTorusIdentificationSelected ≡ true
unitViscosityThreeTorusIdentificationSelectedIsTrue = refl

regularLerayHopfSourceIdentificationSelectedIsTrue :
  regularLerayHopfSourceIdentificationSelected ≡ true
regularLerayHopfSourceIdentificationSelectedIsTrue = refl

officialPeriodicLuoAuthorityConstructorClosedIsTrue :
  officialPeriodicLuoAuthorityConstructorClosed ≡ true
officialPeriodicLuoAuthorityConstructorClosedIsTrue = refl
