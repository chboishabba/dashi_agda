module DASHI.Law.NaziBureaucraticParticipationResponsibilitySourceBoundaryRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.NaziBureaucraticParticipationResponsibilitySourceBoundaryExact as Nazi

fragmentationParentRegression :
  Nazi.parentFragmentationReused Nazi.canonicalNaziBureaucraticParticipationBoundary
  ≡ true
fragmentationParentRegression = refl

responsibilityParentRegression :
  Nazi.parentResponsibilitySeparationReused Nazi.canonicalNaziBureaucraticParticipationBoundary
  ≡ true
responsibilityParentRegression = refl

bureaucraticParticipationSourcePaidRegression :
  Nazi.ushmmBureaucraticParticipationSourcePaid Nazi.canonicalNaziBureaucraticParticipationBoundary
  ≡ true
bureaucraticParticipationSourcePaidRegression = refl

nurembergPrinciplePaidRegression :
  Nazi.nurembergSuperiorOrdersPrinciplePaid Nazi.canonicalNaziBureaucraticParticipationBoundary
  ≡ true
nurembergPrinciplePaidRegression = refl

routineTaskHarmlessRegression :
  Nazi.routineAdministrativeTaskAutomaticallyHarmless Nazi.canonicalNaziBureaucraticParticipationBoundary
  ≡ false
routineTaskHarmlessRegression = refl

roleMembershipCulpabilityRegression :
  Nazi.roleMembershipAutomaticallyIndividualCriminalCulpability Nazi.canonicalNaziBureaucraticParticipationBoundary
  ≡ false
roleMembershipCulpabilityRegression = refl

superiorOrderNoResponsibilityRegression :
  Nazi.superiorOrderAutomaticallyEliminatesResponsibility Nazi.canonicalNaziBureaucraticParticipationBoundary
  ≡ false
superiorOrderNoResponsibilityRegression = refl

historicalEquivalenceRegression :
  Nazi.sharedFragmentationStructureAutomaticallyHistoricalEquivalence
    Nazi.canonicalNaziBureaucraticParticipationBoundary
  ≡ false
historicalEquivalenceRegression = refl
