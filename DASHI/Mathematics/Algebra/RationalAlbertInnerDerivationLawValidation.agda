module DASHI.Mathematics.Algebra.RationalAlbertInnerDerivationLawValidation where

import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertInnerDerivationF4BoundaryExact as D
import DASHI.Mathematics.Algebra.RationalAlbertInnerDerivationLawExact as Law

allInnerDerivationsAreDerivations :
  (a b : A.RationalAlbert) →
  D.DerivationLaw (D.innerDerivation a b)
allInnerDerivationsAreDerivations = Law.innerDerivationLaw
