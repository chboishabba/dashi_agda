module DASHI.Physics.Closure.NSCompactGammaAdmissiblePreservation where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- Compact-Gamma admissible class and invariant-region closure.
--
-- This module separates the logical invariant-region argument from the
-- analytic obligations which must be supplied by the Navier--Stokes lane:
-- continuity of packet observables, boundary differential estimates,
-- logarithmic expenditure bounds, shell-uniform Galerkin estimates, and
-- closedness under compactness limits.
------------------------------------------------------------------------

record OrderedScalar (s : Level) : Set (lsuc s) where
  field
    Scalar : Set s
    _≤_ : Scalar → Scalar → Set s
    _<_ : Scalar → Scalar → Set s

    ≤-refl : ∀ {a} → _≤_ a a
    ≤-trans : ∀ {a b c} → _≤_ a b → _≤_ b c → _≤_ a c
    <-irrefl-from-≤ : ∀ {a b} → _<_ a b → ¬ _≤_ b a

open OrderedScalar public

record CompactGammaSystem
    {s st sh : Level}
    (O : OrderedScalar s)
    (State : Set st)
    (Shell : Set sh) : Set (lsuc (s ⊔ st ⊔ sh)) where
  field
    gamma : Shell → State → Scalar O
    packetEnergy : Shell → State → Scalar O
    stateSize : State → Scalar O
    offPacketRatio : Shell → State → Scalar O

    Reality : State → Set st
    DivergenceFree : State → Set st

open CompactGammaSystem public

record CompactGammaThresholds
    {s : Level}
    (O : OrderedScalar s) : Set (lsuc s) where
  field
    gammaFloor : Scalar O
    energyFloor : Scalar O
    sizeCeiling : Scalar O
    offPacketCeiling : Scalar O

open CompactGammaThresholds public

record CompactGammaAdmissible
    {s st sh : Level}
    {O : OrderedScalar s}
    {State : Set st}
    {Shell : Set sh}
    (S : CompactGammaSystem O State Shell)
    (B : CompactGammaThresholds O)
    (K : Shell)
    (u : State) : Set (s ⊔ st) where
  field
    gammaAboveFloor : _≤_ O (gammaFloor B) (gamma S K u)
    packetEnergyAboveFloor :
      _≤_ O (energyFloor B) (packetEnergy S K u)
    sizeBelowCeiling : _≤_ O (stateSize S u) (sizeCeiling B)
    offPacketRatioBelowCeiling :
      _≤_ O (offPacketRatio S K u) (offPacketCeiling B)
    realityPreserved : Reality S u
    divergenceFreePreserved : DivergenceFree S u

open CompactGammaAdmissible public

------------------------------------------------------------------------
-- Continuity package for all defining packet functionals.
------------------------------------------------------------------------

record Path
    {t st : Level}
    (Time : Set t)
    (State : Set st) : Set (lsuc (t ⊔ st)) where
  field
    at : Time → State

open Path public

record ContinuityStructure
    {t s : Level}
    (Time : Set t)
    (O : OrderedScalar s) : Set (lsuc (t ⊔ s)) where
  field
    Continuous : (Time → Scalar O) → Set (t ⊔ s)

open ContinuityStructure public

record CompactGammaPathContinuity
    {t s st sh : Level}
    {Time : Set t}
    {State : Set st}
    {Shell : Set sh}
    {O : OrderedScalar s}
    (C : ContinuityStructure Time O)
    (S : CompactGammaSystem O State Shell)
    (p : Path Time State)
    (K : Shell) : Set (t ⊔ s ⊔ st ⊔ sh) where
  field
    gammaContinuous : Continuous C (λ τ → gamma S K (at p τ))
    packetEnergyContinuous :
      Continuous C (λ τ → packetEnergy S K (at p τ))
    sizeContinuous : Continuous C (λ τ → stateSize S (at p τ))
    offPacketRatioContinuous :
      Continuous C (λ τ → offPacketRatio S K (at p τ))

open CompactGammaPathContinuity public

------------------------------------------------------------------------
-- Boundary and logarithmic-expenditure estimates.
------------------------------------------------------------------------

record BoundaryDerivativeEstimate
    {s t : Level}
    {O : OrderedScalar s}
    (Time : Set t) : Set (lsuc (s ⊔ t)) where
  field
    gammaDerivative : Time → Scalar O
    boundaryLoss : Time → Scalar O
    inwardAtGammaBoundary :
      ∀ τ → _≤_ O (boundaryLoss τ) (gammaDerivative τ)

open BoundaryDerivativeEstimate public

record LogarithmicModulusIntegration
    {s t : Level}
    {O : OrderedScalar s}
    (Time : Set t) : Set (lsuc (s ⊔ t)) where
  field
    absoluteLogEnergyChange : Time → Scalar O
    integratedExpenditure : Time → Scalar O
    logChangeControlled :
      ∀ τ →
      _≤_ O
        (absoluteLogEnergyChange τ)
        (integratedExpenditure τ)

open LogarithmicModulusIntegration public

record PacketEnergyPositivity
    {s t st sh : Level}
    {O : OrderedScalar s}
    {Time : Set t}
    {State : Set st}
    {Shell : Set sh}
    (S : CompactGammaSystem O State Shell)
    (p : Path Time State)
    (K : Shell) : Set (lsuc (s ⊔ t ⊔ st ⊔ sh)) where
  field
    retainedLowerBound : Time → Scalar O
    retainedLowerBoundPositive : Time → Set s
    energyAboveRetainedLowerBound :
      ∀ τ →
      _≤_ O
        (retainedLowerBound τ)
        (packetEnergy S K (at p τ))

open PacketEnergyPositivity public

packetEnergyRemainsPositive :
  ∀ {s t st sh}
    {O : OrderedScalar s}
    {Time : Set t}
    {State : Set st}
    {Shell : Set sh}
    {S : CompactGammaSystem O State Shell}
    {p : Path Time State}
    {K : Shell} →
  (P : PacketEnergyPositivity S p K) →
  ∀ τ → Σ (Scalar O) (λ lower →
    retainedLowerBound P τ ≡ lower)
packetEnergyRemainsPositive P τ = retainedLowerBound P τ , refl

------------------------------------------------------------------------
-- No-first-exit theorem.
------------------------------------------------------------------------

record FirstExitData
    {s t st sh : Level}
    {O : OrderedScalar s}
    {Time : Set t}
    {State : Set st}
    {Shell : Set sh}
    {S : CompactGammaSystem O State Shell}
    {B : CompactGammaThresholds O}
    (p : Path Time State)
    (K : Shell) : Set (lsuc (s ⊔ t ⊔ st ⊔ sh)) where
  field
    exitTime : Time
    admissibleBeforeExit : Set (s ⊔ st)
    boundaryReached : Set (s ⊔ st)

open FirstExitData public

record NoFirstExitInputs
    {s t st sh : Level}
    {O : OrderedScalar s}
    {Time : Set t}
    {State : Set st}
    {Shell : Set sh}
    {S : CompactGammaSystem O State Shell}
    {B : CompactGammaThresholds O}
    (p : Path Time State)
    (K : Shell) : Set (lsuc (s ⊔ t ⊔ st ⊔ sh)) where
  field
    boundaryMargin : Scalar O
    totalExpenditure : Scalar O
    expenditureBelowMargin : _<_ O totalExpenditure boundaryMargin
    everyFirstExitCostsMargin :
      FirstExitData {S = S} {B = B} p K →
      _≤_ O boundaryMargin totalExpenditure

open NoFirstExitInputs public

noFirstExit :
  ∀ {s t st sh}
    {O : OrderedScalar s}
    {Time : Set t}
    {State : Set st}
    {Shell : Set sh}
    {S : CompactGammaSystem O State Shell}
    {B : CompactGammaThresholds O}
    {p : Path Time State}
    {K : Shell} →
  NoFirstExitInputs {S = S} {B = B} p K →
  ¬ FirstExitData {S = S} {B = B} p K
noFirstExit {O = O} I exit =
  OrderedScalar.<-irrefl-from-≤ O (expenditureBelowMargin I)
    (everyFirstExitCostsMargin I exit)

record FirstExitCompleteness
    {s t st sh : Level}
    {O : OrderedScalar s}
    {Time : Set t}
    {State : Set st}
    {Shell : Set sh}
    (S : CompactGammaSystem O State Shell)
    (B : CompactGammaThresholds O)
    (p : Path Time State)
    (K : Shell) : Set (lsuc (s ⊔ t ⊔ st ⊔ sh)) where
  field
    invariantFromNoFirstExit :
      ¬ FirstExitData {S = S} {B = B} p K →
      ∀ τ → CompactGammaAdmissible S B K (at p τ)

open FirstExitCompleteness public

compactGammaInvariantRegion :
  ∀ {s t st sh}
    {O : OrderedScalar s}
    {Time : Set t}
    {State : Set st}
    {Shell : Set sh}
    {S : CompactGammaSystem O State Shell}
    {B : CompactGammaThresholds O}
    {p : Path Time State}
    {K : Shell} →
  FirstExitCompleteness S B p K →
  NoFirstExitInputs {S = S} {B = B} p K →
  ∀ τ → CompactGammaAdmissible S B K (at p τ)
compactGammaInvariantRegion completeness inputs =
  invariantFromNoFirstExit completeness (noFirstExit inputs)

------------------------------------------------------------------------
-- Simultaneous compatibility across every shell used by the argument.
------------------------------------------------------------------------

record ShellSelection
    {sh : Level}
    (Shell : Set sh) : Set (lsuc sh) where
  field
    UsedShell : Shell → Set sh

open ShellSelection public

ShellFamilyAdmissible :
  ∀ {s st sh}
    {O : OrderedScalar s}
    {State : Set st}
    {Shell : Set sh} →
  (S : CompactGammaSystem O State Shell) →
  CompactGammaThresholds O →
  ShellSelection Shell →
  State → Set (s ⊔ st ⊔ sh)
ShellFamilyAdmissible S B selection u =
  ∀ K → UsedShell selection K → CompactGammaAdmissible S B K u

simultaneousShellPreservation :
  ∀ {s t st sh}
    {O : OrderedScalar s}
    {Time : Set t}
    {State : Set st}
    {Shell : Set sh}
    {S : CompactGammaSystem O State Shell}
    {B : CompactGammaThresholds O}
    {selection : ShellSelection Shell}
    {p : Path Time State} →
  (∀ K → UsedShell selection K →
    FirstExitCompleteness S B p K) →
  (∀ K → UsedShell selection K →
    NoFirstExitInputs {S = S} {B = B} p K) →
  ∀ τ → ShellFamilyAdmissible S B selection (at p τ)
simultaneousShellPreservation completeness inputs τ K used =
  compactGammaInvariantRegion
    (completeness K used)
    (inputs K used)
    τ

------------------------------------------------------------------------
-- Galerkin preservation and compactness-limit passage.
------------------------------------------------------------------------

record GalerkinFamily
    {n t st : Level}
    (Cutoff : Set n)
    (Time : Set t)
    (State : Set st) : Set (lsuc (n ⊔ t ⊔ st)) where
  field
    galerkinPath : Cutoff → Path Time State

open GalerkinFamily public

record UniformGalerkinPreservation
    {n t s st sh : Level}
    {Cutoff : Set n}
    {Time : Set t}
    {State : Set st}
    {Shell : Set sh}
    {O : OrderedScalar s}
    (S : CompactGammaSystem O State Shell)
    (B : CompactGammaThresholds O)
    (selection : ShellSelection Shell)
    (G : GalerkinFamily Cutoff Time State) :
    Set (lsuc (n ⊔ t ⊔ s ⊔ st ⊔ sh)) where
  field
    preservedUniformlyInCutoff :
      ∀ N τ →
      ShellFamilyAdmissible S B selection (at (galerkinPath G N) τ)

open UniformGalerkinPreservation public

record GalerkinCompactnessLimit
    {n t st : Level}
    {Cutoff : Set n}
    {Time : Set t}
    {State : Set st}
    (G : GalerkinFamily Cutoff Time State)
    (limitPath : Path Time State) : Set (lsuc (n ⊔ t ⊔ st)) where
  field
    ConvergesAt : Time → Set (n ⊔ st)
    convergence : ∀ τ → ConvergesAt τ

open GalerkinCompactnessLimit public

record ClosedAdmissibleInequalities
    {n t s st sh : Level}
    {Cutoff : Set n}
    {Time : Set t}
    {State : Set st}
    {Shell : Set sh}
    {O : OrderedScalar s}
    (S : CompactGammaSystem O State Shell)
    (B : CompactGammaThresholds O)
    (selection : ShellSelection Shell)
    (G : GalerkinFamily Cutoff Time State)
    (limitPath : Path Time State)
    (L : GalerkinCompactnessLimit G limitPath) :
    Set (lsuc (n ⊔ t ⊔ s ⊔ st ⊔ sh)) where
  field
    admissibleClosedUnderLimit :
      (∀ N τ →
        ShellFamilyAdmissible S B selection
          (at (galerkinPath G N) τ)) →
      ∀ τ →
        ShellFamilyAdmissible S B selection (at limitPath τ)

open ClosedAdmissibleInequalities public

galerkinPreservationPassesToLimit :
  ∀ {n t s st sh}
    {Cutoff : Set n}
    {Time : Set t}
    {State : Set st}
    {Shell : Set sh}
    {O : OrderedScalar s}
    {S : CompactGammaSystem O State Shell}
    {B : CompactGammaThresholds O}
    {selection : ShellSelection Shell}
    {G : GalerkinFamily Cutoff Time State}
    {limitPath : Path Time State}
    {L : GalerkinCompactnessLimit G limitPath} →
  UniformGalerkinPreservation S B selection G →
  ClosedAdmissibleInequalities S B selection G limitPath L →
  ∀ τ → ShellFamilyAdmissible S B selection (at limitPath τ)
galerkinPreservationPassesToLimit uniform closed =
  admissibleClosedUnderLimit closed
    (preservedUniformlyInCutoff uniform)
