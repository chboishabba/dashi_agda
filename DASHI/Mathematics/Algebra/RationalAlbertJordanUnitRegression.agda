module DASHI.Mathematics.Algebra.RationalAlbertJordanUnitRegression where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Mathematics.Algebra.RationalAlbertJordanExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanUnitExact as U

leftUnitRegression : (x : A.RationalAlbert) →
  A.jordanProduct A.albertUnit x ≡ x
leftUnitRegression = U.leftUnit

rightUnitRegression : (x : A.RationalAlbert) →
  A.jordanProduct x A.albertUnit ≡ x
rightUnitRegression = U.rightUnit
