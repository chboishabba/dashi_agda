module DASHI.Mathematics.Algebra.RationalAlbertMoufangTrialityAutomorphismValidation where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertMoufangTrialityAutomorphismExact as T

leftInverseValidation : (x : A.RationalAlbert) →
  T.trialityInverseA (T.trialityA x) ≡ x
leftInverseValidation = T.trialityInverseLeft

rightInverseValidation : (x : A.RationalAlbert) →
  T.trialityA (T.trialityInverseA x) ≡ x
rightInverseValidation = T.trialityInverseRight
