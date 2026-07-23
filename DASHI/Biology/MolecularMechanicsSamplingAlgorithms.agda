module DASHI.Biology.MolecularMechanicsSamplingAlgorithms where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using
  ( Float
  ; primFloatExp
  ; primFloatLess
  )
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)

open import DASHI.Biology.ConcreteProteinMolecularMechanics
open import DASHI.Biology.BoltzmannConformationalEnsemble

------------------------------------------------------------------------
-- Local product carrier.

record Pair (A B : Set) : Set where
  constructor _,_
  field
    first : A
    second : B

open Pair public

_×_ : Set → Set → Set
A × B = Pair A B

------------------------------------------------------------------------
-- Deterministic random-stream carrier.
--
-- Sampling kernels consume supplied uniforms.  Random-number generation and its
-- statistical quality are separate evidence obligations rather than hidden IO.

record UniformDraw : Set where
  constructor uniformDraw
  field
    uniformValue : Float
    inUnitInterval : Bool

open UniformDraw public

record ProposalKernel : Set₁ where
  field
    propose : ProteinConfiguration → UniformDraw → ProteinConfiguration
    logForwardDensity : ProteinConfiguration → ProteinConfiguration → Float
    logReverseDensity : ProteinConfiguration → ProteinConfiguration → Float

open ProposalKernel public

record MetropolisState : Set where
  constructor metropolisState
  field
    currentConfiguration : ProteinConfiguration
    acceptedMoves : Nat
    rejectedMoves : Nat

open MetropolisState public

metropolisLogAcceptance :
  ThermodynamicParameters →
  ProposalKernel →
  ProteinConfiguration →
  ProteinConfiguration →
  Float
metropolisLogAcceptance thermo kernel old new =
  negf
    (inverseTemperature thermo *f
      (concreteTotalPotential new -f concreteTotalPotential old))
  +f logReverseDensity kernel new old
  -f logForwardDensity kernel old new

metropolisAcceptanceProbability :
  ThermodynamicParameters →
  ProposalKernel →
  ProteinConfiguration →
  ProteinConfiguration →
  Float
metropolisAcceptanceProbability thermo kernel old new =
  primFloatExp (metropolisLogAcceptance thermo kernel old new)

acceptMetropolis : Float → Float → Bool
acceptMetropolis probability draw with primFloatLess draw probability
... | true = true
... | false = false

metropolisStep :
  ThermodynamicParameters →
  ProposalKernel →
  UniformDraw →
  UniformDraw →
  MetropolisState →
  MetropolisState
metropolisStep thermo kernel proposalDraw acceptanceDraw state =
  decide candidate
  where
    candidate : ProteinConfiguration
    candidate = propose kernel (currentConfiguration state) proposalDraw

    decide : ProteinConfiguration → MetropolisState
    decide candidate with
      acceptMetropolis
        (metropolisAcceptanceProbability thermo kernel
          (currentConfiguration state) candidate)
        (uniformValue acceptanceDraw)
    ... | true =
      metropolisState candidate (suc (acceptedMoves state))
        (rejectedMoves state)
    ... | false =
      metropolisState (currentConfiguration state)
        (acceptedMoves state) (suc (rejectedMoves state))

runMetropolis :
  ThermodynamicParameters →
  ProposalKernel →
  List UniformDraw →
  MetropolisState →
  MetropolisState
runMetropolis thermo kernel [] state = state
runMetropolis thermo kernel (proposalDraw ∷ []) state = state
runMetropolis thermo kernel (proposalDraw ∷ acceptanceDraw ∷ rest) state =
  runMetropolis thermo kernel rest
    (metropolisStep thermo kernel proposalDraw acceptanceDraw state)

------------------------------------------------------------------------
-- Replica exchange.

record Replica : Set where
  constructor replica
  field
    replicaThermodynamics : ThermodynamicParameters
    replicaConfiguration : ProteinConfiguration

open Replica public

replicaExchangeExponent : Replica → Replica → Float
replicaExchangeExponent left right =
  (inverseTemperature (replicaThermodynamics left) -f
   inverseTemperature (replicaThermodynamics right))
  *f
  (concreteTotalPotential (replicaConfiguration left) -f
   concreteTotalPotential (replicaConfiguration right))

replicaExchangeProbability : Replica → Replica → Float
replicaExchangeProbability left right =
  primFloatExp (replicaExchangeExponent left right)

swapReplicaConfigurations : Replica → Replica → Replica × Replica
swapReplicaConfigurations left right =
  replica (replicaThermodynamics left) (replicaConfiguration right) ,
  replica (replicaThermodynamics right) (replicaConfiguration left)

replicaExchangeStep :
  UniformDraw →
  Replica →
  Replica →
  Replica × Replica
replicaExchangeStep draw left right with
  acceptMetropolis
    (replicaExchangeProbability left right)
    (uniformValue draw)
... | true = swapReplicaConfigurations left right
... | false = left , right

------------------------------------------------------------------------
-- Umbrella and general biased sampling.

record BiasPotential : Set₁ where
  field
    collectiveVariable : ProteinConfiguration → Float
    biasEnergy : Float → Float

open BiasPotential public

biasedPotential : BiasPotential → ProteinConfiguration → Float
biasedPotential bias c =
  concreteTotalPotential c +f
  biasEnergy bias (collectiveVariable bias c)

record HarmonicUmbrella : Set₁ where
  field
    umbrellaCoordinate : ProteinConfiguration → Float
    umbrellaCentre : Float
    umbrellaStiffness : Float

open HarmonicUmbrella public

harmonicUmbrellaBias : HarmonicUmbrella → BiasPotential
harmonicUmbrellaBias umbrella =
  record
    { collectiveVariable = umbrellaCoordinate umbrella
    ; biasEnergy = λ coordinate →
        umbrellaStiffness umbrella *f
        square (coordinate -f umbrellaCentre umbrella)
    }

------------------------------------------------------------------------
-- Sampling diagnostics and fail-closed scientific boundary.

record SamplingDiagnostics : Set where
  field
    totalSamples : Nat
    acceptedSamples : Nat
    effectiveSampleSize : Float
    integratedAutocorrelationTime : Float
    independentChains : Nat
    chainAgreementTolerance : Float
    allKnownMetastableBasinsVisited : Bool
    detailedBalanceChecked : Bool
    proposalSupportAdequate : Bool
    randomStreamQualityChecked : Bool

open SamplingDiagnostics public

record EnhancedSamplingBoundary : Set where
  field
    replicaTemperatureLadderAdequate : Bool
    adjacentReplicaOverlapAdequate : Bool
    exchangeAcceptanceAdequate : Bool
    umbrellaWindowsCoverCoordinate : Bool
    biasReweightingImplemented : Bool
    freeEnergyEstimatorErrorBound : Float
    convergenceAcrossIndependentRuns : Bool

open EnhancedSamplingBoundary public

record SamplingAlgorithmStatus : Set where
  field
    metropolisKernelExecutable : Bool
    asymmetricHastingsCorrectionPresent : Bool
    replicaExchangeKernelExecutable : Bool
    harmonicUmbrellaExecutable : Bool
    equilibriumSamplingProved : Bool
    universalMixingTimeBoundProved : Bool

open SamplingAlgorithmStatus public

canonicalSamplingAlgorithmStatus : SamplingAlgorithmStatus
canonicalSamplingAlgorithmStatus =
  record
    { metropolisKernelExecutable = true
    ; asymmetricHastingsCorrectionPresent = true
    ; replicaExchangeKernelExecutable = true
    ; harmonicUmbrellaExecutable = true
    ; equilibriumSamplingProved = false
    ; universalMixingTimeBoundProved = false
    }

canonicalEquilibriumSamplingNotProved :
  equilibriumSamplingProved canonicalSamplingAlgorithmStatus ≡ false
canonicalEquilibriumSamplingNotProved = refl
