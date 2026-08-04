module DASHI.Physics.Closure.NSTriadKNPeriodicNavierStokesSubmissionTheoremExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Charles L. Fefferman.
-- Title: "Existence and Smoothness of the Navier--Stokes Equation".
-- Clay Mathematics Institute Millennium Prize Problem description, 2000.
-- DOI: not assigned to the official problem description.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- State the final periodic Navier--Stokes theorem as a typed witness package
-- and close the purely logical maximal-time dichotomy. The theorem package
-- requires velocity, pressure, equation, initial trace, uniqueness, energy,
-- divergence-free and mean-zero evidence separately.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)

record PeriodicNavierStokesSubmissionCarrier : Set₁ where
  field
    SmoothPeriodicDatum : Set
    GlobalVelocity : Set
    GlobalPressure : Set

    DivergenceFreeDatum : SmoothPeriodicDatum → Set
    MeanZeroDatum : SmoothPeriodicDatum → Set

    GlobalSmoothVelocity : GlobalVelocity → Set
    GlobalSmoothPressure : GlobalPressure → Set

    SolvesPeriodicNavierStokes :
      GlobalVelocity → GlobalPressure → SmoothPeriodicDatum → Set

    AttainsInitialDatum :
      GlobalVelocity → SmoothPeriodicDatum → Set

    VelocityPressurePairUnique :
      GlobalVelocity → GlobalPressure → SmoothPeriodicDatum → Set

    GlobalEnergyEquality :
      GlobalVelocity → SmoothPeriodicDatum → Set

    DivergenceFreePreserved : GlobalVelocity → Set
    MeanZeroPreserved : GlobalVelocity → Set
    FiniteEnergyAtEveryTime : GlobalVelocity → Set

open PeriodicNavierStokesSubmissionCarrier public

record PeriodicGlobalSolutionWitness
    (carrier : PeriodicNavierStokesSubmissionCarrier)
    (initial : SmoothPeriodicDatum carrier) : Set₁ where
  field
    velocity : GlobalVelocity carrier
    pressure : GlobalPressure carrier

    velocitySmooth : GlobalSmoothVelocity carrier velocity
    pressureSmooth : GlobalSmoothPressure carrier pressure

    solvesEquation :
      SolvesPeriodicNavierStokes carrier velocity pressure initial

    initialTrace : AttainsInitialDatum carrier velocity initial

    uniquePair :
      VelocityPressurePairUnique carrier velocity pressure initial

    energyEquality : GlobalEnergyEquality carrier velocity initial
    divergenceFree : DivergenceFreePreserved carrier velocity
    meanZero : MeanZeroPreserved carrier velocity
    finiteEnergy : FiniteEnergyAtEveryTime carrier velocity

open PeriodicGlobalSolutionWitness public

PeriodicNavierStokesGlobalRegularityStatement :
  PeriodicNavierStokesSubmissionCarrier → Set₁
PeriodicNavierStokesGlobalRegularityStatement carrier =
  (initial : SmoothPeriodicDatum carrier) →
  DivergenceFreeDatum carrier initial →
  MeanZeroDatum carrier initial →
  PeriodicGlobalSolutionWitness carrier initial

record PeriodicNavierStokesGlobalRegularityInputs
    (carrier : PeriodicNavierStokesSubmissionCarrier) : Set₁ where
  field
    globalSolutionForEveryAdmissibleDatum :
      PeriodicNavierStokesGlobalRegularityStatement carrier

open PeriodicNavierStokesGlobalRegularityInputs public

periodicNavierStokesGlobalRegularity :
  (carrier : PeriodicNavierStokesSubmissionCarrier) →
  PeriodicNavierStokesGlobalRegularityInputs carrier →
  PeriodicNavierStokesGlobalRegularityStatement carrier
periodicNavierStokesGlobalRegularity carrier inputs =
  globalSolutionForEveryAdmissibleDatum inputs

data MaximalTimeAlternative (Finite Infinite : Set) : Set where
  finiteAlternative : Finite → MaximalTimeAlternative Finite Infinite
  infiniteAlternative : Infinite → MaximalTimeAlternative Finite Infinite

record MaximalTimeDichotomyInputs : Set₁ where
  field
    FiniteMaximalTime : Set
    InfiniteMaximalTime : Set

    maximalTimeDichotomy :
      MaximalTimeAlternative FiniteMaximalTime InfiniteMaximalTime

    finiteMaximalTimeContradiction :
      FiniteMaximalTime → ⊥

open MaximalTimeDichotomyInputs public

maximalTimeMustBeInfinite :
  (inputs : MaximalTimeDichotomyInputs) →
  InfiniteMaximalTime inputs
maximalTimeMustBeInfinite inputs
  with maximalTimeDichotomy inputs
... | finiteAlternative finite =
  ⊥-elim (finiteMaximalTimeContradiction inputs finite)
... | infiniteAlternative infinite = infinite

record SelectedSolutionToSubmissionInputs
    (carrier : PeriodicNavierStokesSubmissionCarrier) : Set₁ where
  field
    InitialDatum : Set
    decodeInitialDatum : InitialDatum → SmoothPeriodicDatum carrier

    InitialDatumAdmissible : InitialDatum → Set
    initialDatumDivergenceFree :
      (initial : InitialDatum) →
      InitialDatumAdmissible initial →
      DivergenceFreeDatum carrier (decodeInitialDatum initial)
    initialDatumMeanZero :
      (initial : InitialDatum) →
      InitialDatumAdmissible initial →
      MeanZeroDatum carrier (decodeInitialDatum initial)

    selectedGlobalWitness :
      (initial : InitialDatum) →
      InitialDatumAdmissible initial →
      PeriodicGlobalSolutionWitness carrier (decodeInitialDatum initial)

open SelectedSolutionToSubmissionInputs public

selectedSolutionGivesSubmissionWitness :
  ∀ {carrier}
    (inputs : SelectedSolutionToSubmissionInputs carrier) →
  (initial : InitialDatum inputs) →
  InitialDatumAdmissible inputs initial →
  PeriodicGlobalSolutionWitness carrier
    (decodeInitialDatum inputs initial)
selectedSolutionGivesSubmissionWitness inputs initial admissible =
  selectedGlobalWitness inputs initial admissible

submissionTheoremStatementConstructed : Bool
submissionTheoremStatementConstructed = true

maximalTimeDichotomyReducerConstructed : Bool
maximalTimeDichotomyReducerConstructed = true

submissionTheoremStatementConstructedIsTrue :
  submissionTheoremStatementConstructed ≡ true
submissionTheoremStatementConstructedIsTrue = refl

maximalTimeDichotomyReducerConstructedIsTrue :
  maximalTimeDichotomyReducerConstructed ≡ true
maximalTimeDichotomyReducerConstructedIsTrue = refl
