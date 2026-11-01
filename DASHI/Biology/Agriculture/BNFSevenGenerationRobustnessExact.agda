module DASHI.Biology.Agriculture.BNFSevenGenerationRobustnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.HorizonRobustInterventionExact as Robust
import DASHI.Core.IntergenerationalPlanningHorizonExact as Intergen
import DASHI.Biology.Agriculture.BNFSevenGenerationPlanningExact as Seven
import DASHI.Biology.Agriculture.BNFQualifiedInterventionModelExact as Qualified

data BNFLongHorizonHypothesis : Set where
  optimisticPersistence : BNFLongHorizonHypothesis
  stressSensitivePersistence : BNFLongHorizonHypothesis
  recoveryLimitedPersistence : BNFLongHorizonHypothesis


data BNFLongHorizonAction : Set where
  baselineManagement : BNFLongHorizonAction
  inoculationCentredManagement : BNFLongHorizonAction
  diversifiedNitrogenStrategy : BNFLongHorizonAction


data BNFLongHorizonOutcome : Set where
  acceptableOutcome : BNFLongHorizonOutcome
  impairedOutcome : BNFLongHorizonOutcome


longHorizonSystem :
  Robust.HorizonInterventionSystem
    BNFLongHorizonHypothesis
    Intergen.Generation
    BNFLongHorizonAction
    BNFLongHorizonOutcome
longHorizonSystem =
  Robust.horizon-intervention-system
    baselineManagement
    predict
    NoWorse
    StrictlyBetter
  where
  predict : BNFLongHorizonHypothesis → Intergen.Generation → BNFLongHorizonAction → BNFLongHorizonOutcome
  predict optimisticPersistence _ inoculationCentredManagement = acceptableOutcome
  predict optimisticPersistence _ diversifiedNitrogenStrategy = acceptableOutcome
  predict optimisticPersistence _ baselineManagement = acceptableOutcome
  predict stressSensitivePersistence Intergen.generation7 inoculationCentredManagement = impairedOutcome
  predict stressSensitivePersistence _ inoculationCentredManagement = acceptableOutcome
  predict stressSensitivePersistence _ diversifiedNitrogenStrategy = acceptableOutcome
  predict stressSensitivePersistence _ baselineManagement = acceptableOutcome
  predict recoveryLimitedPersistence Intergen.generation6 inoculationCentredManagement = impairedOutcome
  predict recoveryLimitedPersistence Intergen.generation7 inoculationCentredManagement = impairedOutcome
  predict recoveryLimitedPersistence _ inoculationCentredManagement = acceptableOutcome
  predict recoveryLimitedPersistence _ diversifiedNitrogenStrategy = acceptableOutcome
  predict recoveryLimitedPersistence _ baselineManagement = acceptableOutcome

  NoWorse : BNFLongHorizonOutcome → BNFLongHorizonOutcome → Set
  NoWorse acceptableOutcome acceptableOutcome = ⊤
  NoWorse impairedOutcome impairedOutcome = ⊤
  NoWorse acceptableOutcome impairedOutcome = ⊤
  NoWorse impairedOutcome acceptableOutcome = ⊥

  StrictlyBetter : BNFLongHorizonOutcome → BNFLongHorizonOutcome → Set
  StrictlyBetter acceptableOutcome impairedOutcome = ⊤
  StrictlyBetter _ _ = ⊥

DeclaredHypothesis : BNFLongHorizonHypothesis → Set
DeclaredHypothesis _ = ⊤

DeclaredSevenGeneration : Intergen.Generation → Set
DeclaredSevenGeneration _ = ⊤

diversifiedStrategyRobust :
  Robust.RobustAcrossHypothesesAndHorizon
    longHorizonSystem
    DeclaredHypothesis
    DeclaredSevenGeneration
    diversifiedNitrogenStrategy
diversifiedStrategyRobust =
  Robust.robust-across-hypotheses-and-horizon
    λ { optimisticPersistence _ _ _ → tt
      ; stressSensitivePersistence _ _ _ → tt
      ; recoveryLimitedPersistence _ _ _ → tt
      }

robustBoundary : Robust.HorizonRobustInterventionBoundary
robustBoundary = Robust.canonicalHorizonRobustInterventionBoundary

intergenerationalBoundary : Intergen.IntergenerationalPlanningBoundary
intergenerationalBoundary = Intergen.canonicalIntergenerationalPlanningBoundary

sevenGenerationBoundary : Seven.SevenGenerationBNFBoundary
sevenGenerationBoundary = Seven.canonicalSevenGenerationBNFBoundary

countryDecisionStillRequiresAuthority :
  Qualified.requiredFor Qualified.decideCountryAffectingIntervention Qualified.authorityAdequacy ≡ true
countryDecisionStillRequiresAuthority = refl

data RobustLongHorizonImpliesCountryAuthorityPermission : Set where
data RobustLongHorizonImpliesUniqueFuturePermission : Set where

robustLongHorizonDoesNotCreateCountryAuthority : RobustLongHorizonImpliesCountryAuthorityPermission → ⊥
robustLongHorizonDoesNotCreateCountryAuthority ()
robustLongHorizonDoesNotCreateUniqueFuture : RobustLongHorizonImpliesUniqueFuturePermission → ⊥
robustLongHorizonDoesNotCreateUniqueFuture ()
