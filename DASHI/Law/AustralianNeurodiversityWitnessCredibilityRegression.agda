module DASHI.Law.AustralianNeurodiversityWitnessCredibilityRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.AustralianNeurodiversityWitnessCredibilityExact as Neuro

parentSituatedObserverReusedRegression :
  Neuro.parentSituatedObserverReused Neuro.canonicalAustralianNeurodiversityWitnessBoundary
  ≡ true
parentSituatedObserverReusedRegression = refl

qldJudicialStudyPaidRegression :
  Neuro.queenslandJudicialNeurodiversityStudyPaid Neuro.canonicalAustralianNeurodiversityWitnessBoundary
  ≡ true
qldJudicialStudyPaidRegression = refl

autisticMockWitnessStudyPaidRegression :
  Neuro.autisticAdultMockWitnessStudyPaid Neuro.canonicalAustralianNeurodiversityWitnessBoundary
  ≡ true
autisticMockWitnessStudyPaidRegression = refl

visibleNeuroatypicalPresentationRiskPaidRegression :
  Neuro.visibleNeuroatypicalCharacteristicsMayBeNegativelyPerceivedPaid
    Neuro.canonicalAustralianNeurodiversityWitnessBoundary
  ≡ true
visibleNeuroatypicalPresentationRiskPaidRegression = refl

neurodivergenceUnreliableRegression :
  Neuro.neurodivergenceAutomaticallyUnreliable
    Neuro.canonicalAustralianNeurodiversityWitnessBoundary
  ≡ false
neurodivergenceUnreliableRegression = refl

labelTruthRegression :
  Neuro.diagnosticLabelAutomaticallyTruthOrCredibilityAuthority
    Neuro.canonicalAustralianNeurodiversityWitnessBoundary
  ≡ false
labelTruthRegression = refl

mockJurorRealCourtRegression :
  Neuro.mockJurorEffectAutomaticallyRealCourtEffect
    Neuro.canonicalAustralianNeurodiversityWitnessBoundary
  ≡ false
mockJurorRealCourtRegression = refl

studyDiagnosesPersonRegression :
  Neuro.sourceScholarshipAutomaticallyDiagnosesObservedPerson
    Neuro.canonicalAustralianNeurodiversityWitnessBoundary
  ≡ false
studyDiagnosesPersonRegression = refl
