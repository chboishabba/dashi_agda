module DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound4Regression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDIntersectionalSourceAcquisitionParetoRound4Exact as Round4

candidateStillNotIncluded :
  Round4.Round4CandidateCreatesIncludedStudy → ⊥
candidateStillNotIncluded = Round4.round4CandidateDoesNotCreateIncludedStudy

studentPerspectiveNotDecisionAuthority :
  Round4.StudentPerspectiveCreatesDecisionAuthority → ⊥
studentPerspectiveNotDecisionAuthority = Round4.studentPerspectiveDoesNotCreateDecisionAuthority

coDesignNotEqualAuthority :
  Round4.CoDesignCreatesEqualDecisionAuthority → ⊥
coDesignNotEqualAuthority = Round4.coDesignDoesNotCreateEqualDecisionAuthority
