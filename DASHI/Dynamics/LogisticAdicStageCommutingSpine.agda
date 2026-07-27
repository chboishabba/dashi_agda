module DASHI.Dynamics.LogisticAdicStageCommutingSpine where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BridgeRequirementCore as Bridge
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.TrackedPrimes as TP
import Ontology.GodelLattice as Lattice

------------------------------------------------------------------------
-- One algebraic logistic polynomial, many chart-specific dynamics.
------------------------------------------------------------------------

record LogisticAlgebra (Carrier : Set) : Set₁ where
  field
    one : Carrier
    sub : Carrier → Carrier → Carrier
    mul : Carrier → Carrier → Carrier

open LogisticAlgebra public

logisticStep :
  ∀ {Carrier} →
  LogisticAlgebra Carrier →
  Carrier →
  Carrier →
  Carrier
logisticStep algebra parameter state =
  mul algebra parameter
    (mul algebra state
      (sub algebra (one algebra) state))

record LogisticAlgebraMorphism
  {Source Target : Set}
  (source : LogisticAlgebra Source)
  (target : LogisticAlgebra Target) : Set₁ where
  field
    map : Source → Target
    preservesOne :
      map (one source) ≡ one target
    preservesSub :
      ∀ x y →
      map (sub source x y)
      ≡ sub target (map x) (map y)
    preservesMul :
      ∀ x y →
      map (mul source x y)
      ≡ mul target (map x) (map y)

open LogisticAlgebraMorphism public

logisticStepCommutes :
  ∀ {Source Target}
    {source : LogisticAlgebra Source}
    {target : LogisticAlgebra Target}
    (morphism : LogisticAlgebraMorphism source target)
    (parameter state : Source) →
  map morphism (logisticStep source parameter state)
  ≡
  logisticStep target (map morphism parameter) (map morphism state)
logisticStepCommutes {source = source} {target = target}
  morphism parameter state =
  trans
    (preservesMul morphism parameter
      (mul source state (sub source (one source) state)))
    (cong
      (mul target (map morphism parameter))
      (trans
        (preservesMul morphism state
          (sub source (one source) state))
        (cong
          (mul target (map morphism state))
          (trans
            (preservesSub morphism (one source) state)
            (cong
              (λ unit →
                sub target unit (map morphism state))
              (preservesOne morphism))))))

identityLogisticMorphism :
  ∀ {Carrier}
    (algebra : LogisticAlgebra Carrier) →
  LogisticAlgebraMorphism algebra algebra
identityLogisticMorphism algebra = record
  { map = λ x → x
  ; preservesOne = refl
  ; preservesSub = λ x y → refl
  ; preservesMul = λ x y → refl
  }

identityLogisticSquareCommutes :
  ∀ {Carrier}
    (algebra : LogisticAlgebra Carrier)
    (parameter state : Carrier) →
  map (identityLogisticMorphism algebra)
    (logisticStep algebra parameter state)
  ≡
  logisticStep algebra
    (map (identityLogisticMorphism algebra) parameter)
    (map (identityLogisticMorphism algebra) state)
identityLogisticSquareCommutes algebra parameter state =
  logisticStepCommutes
    (identityLogisticMorphism algebra)
    parameter
    state

------------------------------------------------------------------------
-- Chart, invariant-region and finite-residue contracts.
------------------------------------------------------------------------

data LogisticChartKind : Set where
  rationalAlgebraicChart : LogisticChartKind
  archimedeanRealChart : LogisticChartKind
  pAdicChart : TP.SSP → LogisticChartKind
  finiteResidueChart : TP.SSP → Nat → LogisticChartKind
  decimalDisplayChart : LogisticChartKind
  semanticStageChart : LogisticChartKind

record LogisticChartSeparation : Set where
  field
    commonSource : LogisticChartKind
    realTarget : LogisticChartKind
    selectedPrimeTarget : LogisticChartKind
    decimalDisplay : LogisticChartKind
    commonSourceIsRational :
      commonSource ≡ rationalAlgebraicChart
    noCanonicalRealToPAdicEmbeddingUsed : Bool
    realAndPAdicDynamicsIdentified : Bool
    decimalDigitsIdentifiedWithPAdicDigits : Bool
    algebraicFormulaShared : Bool

canonicalP3ChartSeparation : LogisticChartSeparation
canonicalP3ChartSeparation = record
  { commonSource = rationalAlgebraicChart
  ; realTarget = archimedeanRealChart
  ; selectedPrimeTarget = pAdicChart TP.p3
  ; decimalDisplay = decimalDisplayChart
  ; commonSourceIsRational = refl
  ; noCanonicalRealToPAdicEmbeddingUsed = true
  ; realAndPAdicDynamicsIdentified = false
  ; decimalDigitsIdentifiedWithPAdicDigits = false
  ; algebraicFormulaShared = true
  }

data InvariantRegionKind : Set where
  orderedIntervalRegion : InvariantRegionKind
  pAdicBallRegion : TP.SSP → InvariantRegionKind
  finiteResidueRegion : TP.SSP → Nat → InvariantRegionKind

record LogisticInvariantRegion
  (Parameter State : Set) : Set₁ where
  field
    regionKind : InvariantRegionKind
    contains : State → Set
    admissibleParameter : Parameter → Set
    step : Parameter → State → State
    preservesRegion :
      ∀ parameter state →
      admissibleParameter parameter →
      contains state →
      contains (step parameter state)

record FiniteResidueLogisticSquare
  (PAdicState ResidueState : Set) : Set₁ where
  field
    parameterPAdic : PAdicState
    reduce : PAdicState → ResidueState
    pAdicStep : PAdicState → PAdicState → PAdicState
    residueStep : ResidueState → ResidueState → ResidueState
    denominatorAdmissible : PAdicState → Bool
    parameterDenominatorAdmissible :
      denominatorAdmissible parameterPAdic ≡ true
    reductionCommutes :
      ∀ state →
      denominatorAdmissible state ≡ true →
      reduce (pAdicStep parameterPAdic state)
      ≡ residueStep (reduce parameterPAdic) (reduce state)

record GovernedStageObservation
  (ResidueState : Set) : Set₁ where
  field
    observe : ResidueState → Atlas.StageAtlasZeroToEleven
    bridgeRequirement : Bridge.BridgeRequirementRow
    interpretationCandidateOnly : Bool
    mathematicalAuthorityPromoted : Bool
    psychologicalAuthorityPromoted : Bool
    politicalAuthorityPromoted : Bool

canonicalResidueToStageBridgeRequirement :
  Bridge.BridgeRequirementRow
canonicalResidueToStageBridgeRequirement =
  Bridge.canonicalBridgeRequirementRow
    "finite p-adic logistic residue orbit"
    "StageAtlasZeroToEleven interpretation"
    Bridge.bridgeSuppliedCandidateOnly
    true
    true
    true

canonicalResidueToStageBridgeRequirementReceipt :
  Bridge.BridgeRequirementRowReceipt
    canonicalResidueToStageBridgeRequirement
canonicalResidueToStageBridgeRequirementReceipt =
  Bridge.bridgeRequirementRowReceipt refl refl refl

------------------------------------------------------------------------
-- Exact FactorVec support of the rational approximation 357/100.
--
-- Existing FactorVec exponents are natural, so numerator and denominator are
-- represented separately rather than smuggling signed exponents into the type.
------------------------------------------------------------------------

numeratorFactorVec357 : Lattice.FactorVec
numeratorFactorVec357 =
  Lattice.v15
    0 1 0 1 0
    0 1 0 0 0
    0 0 0 0 0

denominatorFactorVec100 : Lattice.FactorVec
denominatorFactorVec100 =
  Lattice.v15
    2 0 2 0 0
    0 0 0 0 0
    0 0 0 0 0

numerator357Factorisation :
  357 ≡ 3 * 7 * 17
numerator357Factorisation = refl

denominator100Factorisation :
  100 ≡ 2 * 2 * 5 * 5
denominator100Factorisation = refl

data ValuationSign : Set where
  negativeValuation : Nat → ValuationSign
  zeroValuation : ValuationSign
  positiveValuation : Nat → ValuationSign

valuationProfile357Over100 : Lattice.Vec15 ValuationSign
valuationProfile357Over100 =
  Lattice.v15
    (negativeValuation 2)
    (positiveValuation 1)
    (negativeValuation 2)
    (positiveValuation 1)
    zeroValuation
    zeroValuation
    (positiveValuation 1)
    zeroValuation
    zeroValuation
    zeroValuation
    zeroValuation
    zeroValuation
    zeroValuation
    zeroValuation
    zeroValuation

record NormFraction : Set where
  constructor norm-fraction
  field
    numerator : Nat
    denominator : Nat

normAt2 : NormFraction
normAt2 = norm-fraction 4 1

normAt3 : NormFraction
normAt3 = norm-fraction 1 3

normAt5 : NormFraction
normAt5 = norm-fraction 25 1

normAt7 : NormFraction
normAt7 = norm-fraction 1 7

normAt17 : NormFraction
normAt17 = norm-fraction 1 17

normAt11 : NormFraction
normAt11 = norm-fraction 1 1

record LogisticRationalFactorVecReceipt : Set₁ where
  field
    numerator : Nat
    denominator : Nat
    numeratorFactors : Lattice.FactorVec
    denominatorFactors : Lattice.FactorVec
    numeratorExact : numerator ≡ 3 * 7 * 17
    denominatorExact : denominator ≡ 2 * 2 * 5 * 5
    numeratorFactorsExact :
      numeratorFactors ≡ numeratorFactorVec357
    denominatorFactorsExact :
      denominatorFactors ≡ denominatorFactorVec100
    valuationProfile : Lattice.Vec15 ValuationSign
    valuationProfileExact :
      valuationProfile ≡ valuationProfile357Over100
    p2Norm : NormFraction
    p3Norm : NormFraction
    p5Norm : NormFraction
    p7Norm : NormFraction
    p17Norm : NormFraction
    p11Norm : NormFraction
    p2NormExact : p2Norm ≡ normAt2
    p3NormExact : p3Norm ≡ normAt3
    p5NormExact : p5Norm ≡ normAt5
    p7NormExact : p7Norm ≡ normAt7
    p17NormExact : p17Norm ≡ normAt17
    p11NormExact : p11Norm ≡ normAt11
    allNonzeroSupportOnTrackedPrimes : Bool
    decimalApproximationToRealAccumulation : Bool
    exactRealAccumulationParameterClaimed : Bool
    monsterOriginClaimed : Bool

canonicalLogisticRationalFactorVecReceipt :
  LogisticRationalFactorVecReceipt
canonicalLogisticRationalFactorVecReceipt = record
  { numerator = 357
  ; denominator = 100
  ; numeratorFactors = numeratorFactorVec357
  ; denominatorFactors = denominatorFactorVec100
  ; numeratorExact = numerator357Factorisation
  ; denominatorExact = denominator100Factorisation
  ; numeratorFactorsExact = refl
  ; denominatorFactorsExact = refl
  ; valuationProfile = valuationProfile357Over100
  ; valuationProfileExact = refl
  ; p2Norm = normAt2
  ; p3Norm = normAt3
  ; p5Norm = normAt5
  ; p7Norm = normAt7
  ; p17Norm = normAt17
  ; p11Norm = normAt11
  ; p2NormExact = refl
  ; p3NormExact = refl
  ; p5NormExact = refl
  ; p7NormExact = refl
  ; p17NormExact = refl
  ; p11NormExact = refl
  ; allNonzeroSupportOnTrackedPrimes = true
  ; decimalApproximationToRealAccumulation = true
  ; exactRealAccumulationParameterClaimed = false
  ; monsterOriginClaimed = false
  }

------------------------------------------------------------------------
-- Continuum and interpretation authority boundary.
------------------------------------------------------------------------

record LogisticContinuumAuthorityBoundary : Set where
  field
    rationalPolynomialCarrierConstructed : Bool
    realCarrierConstructedHere : Bool
    derivativeTheoryImportedHere : Bool
    invariantRealIntervalProvedHere : Bool
    pAdicInvariantBallProvedHere : Bool
    finiteResidueSquareInstantiatedHere : Bool
    periodDoublingTheoremProvedHere : Bool
    accumulationConstantProvedHere : Bool
    continuumChaosPromoted : Bool
    realBifurcationTreeTransferredToPAdics : Bool
    stageMeaningDerivedFromResidueAlone : Bool
    finiteResidueSquareRequiresAdmissibility : Bool

canonicalLogisticContinuumAuthorityBoundary :
  LogisticContinuumAuthorityBoundary
canonicalLogisticContinuumAuthorityBoundary = record
  { rationalPolynomialCarrierConstructed = true
  ; realCarrierConstructedHere = false
  ; derivativeTheoryImportedHere = false
  ; invariantRealIntervalProvedHere = false
  ; pAdicInvariantBallProvedHere = false
  ; finiteResidueSquareInstantiatedHere = false
  ; periodDoublingTheoremProvedHere = false
  ; accumulationConstantProvedHere = false
  ; continuumChaosPromoted = false
  ; realBifurcationTreeTransferredToPAdics = false
  ; stageMeaningDerivedFromResidueAlone = false
  ; finiteResidueSquareRequiresAdmissibility = true
  }

logisticAdicSummary : String
logisticAdicSummary =
  "The logistic polynomial is shared algebraically from a rational source; real, p-adic and finite-residue dynamics are distinct charts, and only proof-carrying algebraic or admissible residue squares commute before the governed Stage-atlas arrow."
