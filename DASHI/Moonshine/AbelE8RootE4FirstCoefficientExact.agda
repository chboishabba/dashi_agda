module DASHI.Moonshine.AbelE8RootE4FirstCoefficientExact where

------------------------------------------------------------------------
-- LITERAL ORIGINAL E8 ROOT LIST ↔ FIRST BISHOP E4 COEFFICIENT.
--
-- q^1 coefficient of theta_E8 is the cardinality of norm-2 roots,
-- provided the generated list enumerates those roots exactly.
-- Here we prove the source COUNT of the generated E8 list and the
-- independent literal E4 coefficient at n=0 agree.
--
-- This is an actual arithmetic bridge, not the all-q theta identity.
-- The lattice, norm-two completeness and higher-shell comparison
-- remain required separately.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; trans; sym)
open import Agda.Builtin.Nat using (Nat)

import Real as Bishop
import RealProperties as BishopP
import DASHI.Algebra.Trit.E8RootEnumeration as Roots
import DASHI.Moonshine.JInvariantEisensteinIncrementCoefficientBoundExact as Coeff
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as E
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal

originalE8GeneratedRootCount :
  Roots.indexedRootListLength Roots.combinedIndexedRoots
  ≡ Roots.expectedTotalRootCount
originalE8GeneratedRootCount =
  Roots.combinedIndexedRootsLengthIs240

originalBishopE4FirstCoefficientIs240 :
  Coeff.e4IncrementCoefficient 0 ≡ 240
originalBishopE4FirstCoefficientIs240 = refl

originalE8RootListEqualsE4FirstCoefficient :
  Roots.indexedRootListLength Roots.combinedIndexedRoots
  ≡ Coeff.e4IncrementCoefficient 0
originalE8RootListEqualsE4FirstCoefficient =
  trans
    originalE8GeneratedRootCount
    (sym originalBishopE4FirstCoefficientIs240)

originalBishopE4FirstCoefficientMatchesE8RootCount :
  Bishop._≃_
    (E.e4CoefficientReal 0)
    (NatReal.natReal (Roots.indexedRootListLength Roots.combinedIndexedRoots))
originalBishopE4FirstCoefficientMatchesE8RootCount
  rewrite originalE8RootListEqualsE4FirstCoefficient = BishopP.≃-refl
