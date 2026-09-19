module DASHI.Governance.HansonBurqaIslamophobiaFeministRelationalValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.HansonBurqaIslamophobiaFeministRelationalExact as B

veilSymbolDoesNotRecoverAgency :
  INF.FactorsThrough B.veilObserver B.originatingAgency → ⊥
veilSymbolDoesNotRecoverAgency =
  B.veilSymbolCannotRecoverOriginatingAgency

shariaDoesNotCollapseToFiqh :
  B.ShariaEqualsFiqh → ⊥
shariaDoesNotCollapseToFiqh =
  B.shariaDoesNotDefinitionallyEqualFiqh

fiqhDoesNotCollapseToStateLaw :
  B.FiqhEqualsStateLaw → ⊥
fiqhDoesNotCollapseToStateLaw =
  B.fiqhDoesNotDefinitionallyEqualStateLaw

oneInterpretationDoesNotExhaustIslam :
  B.OneInterpretationExhaustsIslam → ⊥
oneInterpretationDoesNotExhaustIslam =
  B.oneInterpretationDoesNotExhaustIslam

coercionDoesNotEraseAllAgency :
  B.SomeWomenCoercedThereforeEveryVeiledWomanLacksAgency → ⊥
coercionDoesNotEraseAllAgency =
  B.coercionDoesNotEraseAllAgency

agencyDoesNotEraseCoercion :
  B.SomeWomenChooseVeilingThereforeCoercionNeverExists → ⊥
agencyDoesNotEraseCoercion =
  B.agencyDoesNotEraseCoercion

feminismDoesNotRequireOneDressPosition :
  B.FeminismRequiresOneDressPosition → ⊥
feminismDoesNotRequireOneDressPosition =
  B.feminismDoesNotRequireSingleDressPosition

humanGroupNeverBecomesAmalek :
  B.Amalek.ethnicOrReligiousEssentialismPromotion B.amalekBoundary ≡ false
humanGroupNeverBecomesAmalek =
  B.humanGroupCannotInhabitAmalekPredicate

antiFeministVerdictNotAutoPromoted :
  B.antiFeministVerdictAutomaticallyProved
    B.canonicalHansonBurqaFeministRelationalBoundary
    ≡ false
antiFeministVerdictNotAutoPromoted =
  B.antiFeministVerdictAutomaticallyProvedIsFalse
    B.canonicalHansonBurqaFeministRelationalBoundary

islamophobiaVerdictNotAutoPromoted :
  B.islamophobiaVerdictAutomaticallyProved
    B.canonicalHansonBurqaFeministRelationalBoundary
    ≡ false
islamophobiaVerdictNotAutoPromoted =
  B.islamophobiaVerdictAutomaticallyProvedIsFalse
    B.canonicalHansonBurqaFeministRelationalBoundary

oneFeministVoiceNotSovereign :
  B.oneFeministVoiceMadeSovereign
    B.canonicalHansonBurqaFeministRelationalBoundary
    ≡ false
oneFeministVoiceNotSovereign =
  B.oneFeministVoiceMadeSovereignIsFalse
    B.canonicalHansonBurqaFeministRelationalBoundary

positiveRepairRetainsSituatedResidual :
  B.positiveRepairAddsSituatedResidual
    B.canonicalHansonBurqaFeministRelationalBoundary
    ≡ true
positiveRepairRetainsSituatedResidual = refl
