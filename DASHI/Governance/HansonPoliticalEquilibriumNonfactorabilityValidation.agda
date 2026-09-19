module DASHI.Governance.HansonPoliticalEquilibriumNonfactorabilityValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.RelationalHistoryFabricExact as History
import DASHI.Governance.HansonPoliticalEquilibriumNonfactorabilityExact as E

interfaceAloneDoesNotDetermineReach :
  NF.FactorsThrough E.interfaceObserver E.politicalReachConsumer → ⊥
interfaceAloneDoesNotDetermineReach =
  E.hansonInterfaceAloneCannotDeterminePoliticalReach

environmentAloneDoesNotDetermineReach :
  NF.FactorsThrough E.broadEnvironmentObserver E.actorReachConsumer → ⊥
environmentAloneDoesNotDetermineReach =
  E.environmentAloneCannotDeterminePoliticalReach

samePresentDoesNotDetermineFutureCone :
  NF.FactorsThrough
    (History.observe E.politicalEquilibriumFabric)
    (History.futureConeOf E.politicalEquilibriumFabric) →
  ⊥
samePresentDoesNotDetermineFutureCone =
  E.presentRegisterCannotDetermineFutureCone

interfaceInsufficiencyPinned :
  E.interfaceAloneInsufficient E.canonicalHansonEquilibriumExplanation ≡ true
interfaceInsufficiencyPinned =
  E.interfaceAloneInsufficientIsTrue E.canonicalHansonEquilibriumExplanation

environmentInsufficiencyPinned :
  E.environmentAloneInsufficient E.canonicalHansonEquilibriumExplanation ≡ true
environmentInsufficiencyPinned =
  E.environmentAloneInsufficientIsTrue E.canonicalHansonEquilibriumExplanation

noDiagnosisRequired :
  E.psychologicalDiagnosisRequired E.canonicalHansonEquilibriumExplanation ≡ false
noDiagnosisRequired =
  E.psychologicalDiagnosisRequiredIsFalse E.canonicalHansonEquilibriumExplanation

noSingleAxisCausalSufficiency :
  E.oneAxisCausallySufficient E.canonicalHansonEquilibriumExplanation ≡ false
noSingleAxisCausalSufficiency =
  E.oneAxisCausallySufficientIsFalse E.canonicalHansonEquilibriumExplanation

reachIsNotElectionForecast :
  E.politicalReachIsElectionForecast E.canonicalHansonEquilibriumExplanation ≡ false
reachIsNotElectionForecast =
  E.politicalReachIsElectionForecastIsFalse E.canonicalHansonEquilibriumExplanation

interfaceCostRemainsOpen :
  E.hansonInterfaceCostStatus ≡ E.candidateInterpretation
interfaceCostRemainsOpen = E.refl

personalityDoesNotEqualPhenomenon :
  E.HansonPersonalityIsHansonPhenomenon → ⊥
personalityDoesNotEqualPhenomenon =
  E.personalityDoesNotEqualPhenomenon

mediaDoesNotEqualPhenomenon :
  E.HansonPhenomenonIsMediaEffect → ⊥
mediaDoesNotEqualPhenomenon =
  E.mediaDoesNotEqualPhenomenon

economicsDoesNotEqualPhenomenon :
  E.HansonPhenomenonIsEconomicGrievance → ⊥
economicsDoesNotEqualPhenomenon =
  E.economicsDoesNotEqualPhenomenon

regionDoesNotEqualPhenomenon :
  E.HansonPhenomenonIsRegionalConservatism → ⊥
regionDoesNotEqualPhenomenon =
  E.regionDoesNotEqualPhenomenon
