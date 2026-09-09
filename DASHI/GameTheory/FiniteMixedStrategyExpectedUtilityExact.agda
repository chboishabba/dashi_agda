module DASHI.GameTheory.FiniteMixedStrategyExpectedUtilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.GameTheory.StrategicInteractionCoreExact as Game
import DASHI.Cognition.PNF.GenericExpectedFibreRateExact as Expected

------------------------------------------------------------------------
-- FINITE MIXED STRATEGIES / EXPECTED UTILITY
--
-- Pure-strategy Nash needs only preference ordering.  Mixed-strategy expected
-- utility is stronger: it needs a finite probability law and cardinal expected-
-- utility semantics.  This module therefore reuses the existing exact rational
-- probability atoms and requires a separate expected-utility admissibility
-- receipt rather than treating every ordinal payoff representation as cardinal.
------------------------------------------------------------------------

record WeightedStrategy
    (G : Game.StrategicGame)
    (player : Game.Player G) : Set where
  constructor weighted-strategy
  field
    probability : Expected.ProbabilityAtom
    strategy : Game.Strategy G player

open WeightedStrategy public

strategyMass :
  ∀ {G player} → WeightedStrategy G player → ℚ
strategyMass atom = Expected.probabilityMass (probability atom)

mixedStrategyMass :
  ∀ {G player} → List (WeightedStrategy G player) → ℚ
mixedStrategyMass [] = 0ℚ
mixedStrategyMass (atom ∷ atoms) =
  strategyMass atom + mixedStrategyMass atoms

record FiniteMixedStrategy
    (G : Game.StrategicGame)
    (player : Game.Player G) : Set₁ where
  constructor finite-mixed-strategy
  field
    atoms : List (WeightedStrategy G player)
    normalized : mixedStrategyMass atoms ≡ 1ℚ
    lawReference : String

open FiniteMixedStrategy public

record WeightedProfile (G : Game.StrategicGame) : Set where
  constructor weighted-profile
  field
    probability : Expected.ProbabilityAtom
    profile : Game.Profile G

open WeightedProfile public

profileMass : ∀ {G} → WeightedProfile G → ℚ
profileMass atom = Expected.probabilityMass (probability atom)

mixedProfileMass : ∀ {G} → List (WeightedProfile G) → ℚ
mixedProfileMass [] = 0ℚ
mixedProfileMass (atom ∷ atoms) = profileMass atom + mixedProfileMass atoms

record FiniteMixedProfileLaw (G : Game.StrategicGame) : Set₁ where
  constructor finite-mixed-profile-law
  field
    atoms : List (WeightedProfile G)
    normalized : mixedProfileMass atoms ≡ 1ℚ
    lawReference : String

open FiniteMixedProfileLaw public

------------------------------------------------------------------------
-- Product-law mass for unilateral mixed deviations.
------------------------------------------------------------------------

jointDeviationMass :
  ∀ {G player} →
  List (WeightedProfile G) →
  List (WeightedStrategy G player) → ℚ
jointDeviationMass [] alternatives = 0ℚ
jointDeviationMass (profileAtom ∷ profiles) alternatives =
  profileMass profileAtom * mixedStrategyMass alternatives
  + jointDeviationMass profiles alternatives

jointDeviationMassFactors :
  ∀ {G player}
    (profiles : List (WeightedProfile G))
    (alternatives : List (WeightedStrategy G player)) →
  jointDeviationMass profiles alternatives
  ≡ mixedProfileMass profiles * mixedStrategyMass alternatives
jointDeviationMassFactors [] alternatives = solve-∀
jointDeviationMassFactors (profileAtom ∷ profiles) alternatives
  rewrite jointDeviationMassFactors profiles alternatives = solve-∀

normalizedJointDeviationMass :
  ∀ {G player}
    (profileLaw : FiniteMixedProfileLaw G)
    (alternative : FiniteMixedStrategy G player) →
  jointDeviationMass
    (FiniteMixedProfileLaw.atoms profileLaw)
    (FiniteMixedStrategy.atoms alternative)
  ≡ 1ℚ
normalizedJointDeviationMass profileLaw alternative
  rewrite jointDeviationMassFactors
    (FiniteMixedProfileLaw.atoms profileLaw)
    (FiniteMixedStrategy.atoms alternative)
    | FiniteMixedProfileLaw.normalized profileLaw
    | FiniteMixedStrategy.normalized alternative = solve-∀

------------------------------------------------------------------------
-- Cardinal expected-utility gate.
------------------------------------------------------------------------

record FiniteExpectedUtilitySurface (G : Game.StrategicGame) : Set₁ where
  constructor finite-expected-utility-surface
  field
    numericalPayoff : Game.NumericalPayoffRealisation G
    payoffToRational : Game.Payoff numericalPayoff → ℚ

    ExpectedUtilitySemanticsAdmissible : Set
    expectedUtilitySemanticsReceipt : ExpectedUtilitySemanticsAdmissible

    cardinalReference : String
    probabilityReference : String

open FiniteExpectedUtilitySurface public

profileExpectedUtility :
  ∀ {G} →
  (U : FiniteExpectedUtilitySurface G) →
  (player : Game.Player G) →
  List (WeightedProfile G) → ℚ
profileExpectedUtility U player [] = 0ℚ
profileExpectedUtility {G} U player (atom ∷ atoms) =
  profileMass atom
    * payoffToRational U
        (Game.payoff (numericalPayoff U) player
          (Game.outcome G (profile atom)))
  + profileExpectedUtility U player atoms

------------------------------------------------------------------------
-- Expected utility under a unilateral mixed deviation.  The profile law is
-- held fixed as the context law; each profile atom is crossed with each atom of
-- the deviating player's finite mixed strategy.
------------------------------------------------------------------------

deviationExpectedUtilityAgainstProfile :
  ∀ {G} →
  (U : FiniteExpectedUtilitySurface G) →
  (player : Game.Player G) →
  Game.Profile G →
  List (WeightedStrategy G player) → ℚ
deviationExpectedUtilityAgainstProfile U player profile [] = 0ℚ
deviationExpectedUtilityAgainstProfile {G} U player profile (atom ∷ atoms) =
  strategyMass atom
    * payoffToRational U
        (Game.payoff (numericalPayoff U) player
          (Game.outcome G
            (Game.deviate G profile player (strategy atom))))
  + deviationExpectedUtilityAgainstProfile U player profile atoms

mixedDeviationExpectedUtility :
  ∀ {G} →
  (U : FiniteExpectedUtilitySurface G) →
  (player : Game.Player G) →
  List (WeightedProfile G) →
  List (WeightedStrategy G player) → ℚ
mixedDeviationExpectedUtility U player [] alternatives = 0ℚ
mixedDeviationExpectedUtility U player (profileAtom ∷ profiles) alternatives =
  profileMass profileAtom
    * deviationExpectedUtilityAgainstProfile
        U player (profile profileAtom) alternatives
  + mixedDeviationExpectedUtility U player profiles alternatives

FiniteMixedBestResponse :
  ∀ {G} →
  (U : FiniteExpectedUtilitySurface G) →
  (law : FiniteMixedProfileLaw G) →
  (player : Game.Player G) →
  Set₁
FiniteMixedBestResponse {G} U law player =
  (alternative : FiniteMixedStrategy G player) →
  mixedDeviationExpectedUtility
    U player (FiniteMixedProfileLaw.atoms law)
      (FiniteMixedStrategy.atoms alternative)
  ≤
  profileExpectedUtility U player (FiniteMixedProfileLaw.atoms law)

record FiniteMixedNashEquilibrium
    (G : Game.StrategicGame)
    (U : FiniteExpectedUtilitySurface G) : Set₁ where
  constructor finite-mixed-nash-equilibrium
  field
    profileLaw : FiniteMixedProfileLaw G
    everyPlayerMixedBestResponds :
      (player : Game.Player G) →
      FiniteMixedBestResponse U profileLaw player

    equilibriumReference : String

open FiniteMixedNashEquilibrium public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data OrdinalUtilityMeansExpectedUtilityPermission : Set where

data FiniteMixedLawMeansGeneralProbabilityMeasurePermission : Set where

data PureNashMeansMixedNashPermission : Set where

data MixedNashMeansUniqueEquilibriumPermission : Set where

data MixedNashMeansEvolutionaryStabilityPermission : Set where

data MixedExpectedUtilityMeansEmpiricalFrequencyPermission : Set where

data MixedExpectedUtilityMeansMoralValuePermission : Set where

data MarginalNormalizationMeansIndependencePermission : Set where

ordinalUtilityDoesNotAutomaticallySupportExpectation :
  OrdinalUtilityMeansExpectedUtilityPermission → ⊥
ordinalUtilityDoesNotAutomaticallySupportExpectation ()

finiteMixedLawDoesNotCreateGeneralMeasureSpace :
  FiniteMixedLawMeansGeneralProbabilityMeasurePermission → ⊥
finiteMixedLawDoesNotCreateGeneralProbabilityMeasurePermission = λ ()

pureNashDoesNotAutomaticallyGiveMixedNash : PureNashMeansMixedNashPermission → ⊥
pureNashDoesNotAutomaticallyGiveMixedNash ()

mixedNashNeedNotBeUnique : MixedNashMeansUniqueEquilibriumPermission → ⊥
mixedNashNeedNotBeUnique ()

mixedNashDoesNotAutomaticallyGiveESS :
  MixedNashMeansEvolutionaryStabilityPermission → ⊥
mixedNashDoesNotAutomaticallyGiveESS ()

mixedExpectedUtilityDoesNotBecomeObservedFrequency :
  MixedExpectedUtilityMeansEmpiricalFrequencyPermission → ⊥
mixedExpectedUtilityDoesNotBecomeObservedFrequency ()

mixedExpectedUtilityDoesNotBecomeMoralValue :
  MixedExpectedUtilityMeansMoralValuePermission → ⊥
mixedExpectedUtilityDoesNotBecomeMoralValue ()

marginalNormalizationDoesNotAssertStatisticalIndependence :
  MarginalNormalizationMeansIndependencePermission → ⊥
marginalNormalizationDoesNotAssertStatisticalIndependence ()

record FiniteMixedStrategyBoundary : Set where
  constructor finite-mixed-strategy-boundary
  field
    finiteProbabilityAtomsReused : Bool
    mixedStrategyNormalizationExplicit : Bool
    mixedProfileNormalizationExplicit : Bool
    deviationProductMassNormalized : Bool
    cardinalExpectedUtilityRequiresReceipt : Bool
    mixedBestResponseExpectedUtilityBased : Bool
    generalMeasureTheoryInventedHere : Bool
    pureNashAutomaticallyPromotesToMixedNash : Bool

canonicalFiniteMixedStrategyBoundary : FiniteMixedStrategyBoundary
canonicalFiniteMixedStrategyBoundary =
  finite-mixed-strategy-boundary true true true true true true false false
