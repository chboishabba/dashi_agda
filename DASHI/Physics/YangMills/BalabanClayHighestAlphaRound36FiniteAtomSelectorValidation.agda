module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound36FiniteAtomSelectorValidation where

------------------------------------------------------------------------
-- Cumulative Round Thirty Six validation root.
--
-- Round 36 closes the finite pair and deep channels from the literal physical
-- selected-factor radius, gives every subset atom exactly one budget owner,
-- and connects the remaining singleton curvature obligation to a local
-- gauge/constraint-admissible variation selector.  The actual selected
-- Euler--Lagrange selector and its spillover estimate remain open.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound35PlaquetteCurlValidation
import DASHI.Physics.YangMills.BalabanP33WilsonAtomOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanP33PhysicalSelectedFactorEnvelopeExact as Envelope
import DASHI.Physics.YangMills.BalabanP33WilsonPairEnvelopeExact as Pair
import DASHI.Physics.YangMills.BalabanP33PhysicalPairDeepLowerExact as Finite
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanP33WilsonPairDeepBudgetExact as Coeff
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (length)
open import Data.Rational.Base using (_*_; _/_; _+_)

subsetOwnershipExhaustsAllAtoms :
  length Ownership.correlatedAtoms + length Ownership.deepAtoms
  ≡ length Ownership.allSubsetAtoms
subsetOwnershipExhaustsAllAtoms = Ownership.correlatedAndDeepCountExact

pairDeepOwnershipExhaustsFifteen : 10 + 5 ≡ 15
pairDeepOwnershipExhaustsFifteen = refl

pairCoefficientPerCrossRegression :
  Coeff.pairCoefficientPerCrossCharge
  ≡ Coeff.rho * (+ 1 / 256)
pairCoefficientPerCrossRegression = Coeff.pairPerCrossExact

deepCoefficientSlackRegression :
  Coeff.allPlacementDeepCoefficient + Coeff.deepSlack
  ≡ Coeff.diagonalTargetCoefficient
deepCoefficientSlackRegression =
  Coeff.deepCoefficientPlusSlackIsDiagonalTarget

selectorBudgetRegression :
  Selector.remainingSingletonCoefficient + Coeff.rho * (+ 1 / 256)
  ≡ Wilson.rhoOverThirtySix
selectorBudgetRegression = Selector.remainingPlusPairIsCorrelated
