module DASHI.Physics.YangMills.BalabanP33SingletonBudgetFeasibilityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Make the tiny singleton/localization/KKT budget an exact rational
-- feasibility object rather than an informal allocation.  The pair channel
-- consumes 9/18874368 of the correlated coefficient and leaves exactly
--
--   55/18874368.
--
-- A symbolic split alpha+beta may be used only after the charge is proved
-- nonnegative and the two owner estimates are available.  The module supplies
-- an explicit balanced witness 27/18874368 + 28/18874368 and a fail-closed
-- no-fit predicate for estimate families whose total coefficient is too large.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Negation using (¬_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33WilsonPairDeepBudgetExact as PairDeep
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

singletonBudget : ℚ
singletonBudget = Selector.remainingSingletonCoefficient

pairBudgetPerCross : ℚ
pairBudgetPerCross = PairDeep.pairCoefficientPerCrossCharge

correlatedBudgetPerCross : ℚ
correlatedBudgetPerCross = Wilson.rhoOverThirtySix

singletonBudgetExact : singletonBudget ≡ + 55 / 18874368
singletonBudgetExact = refl

pairBudgetExact : pairBudgetPerCross ≡ + 9 / 18874368
pairBudgetExact =
  trans PairDeep.pairPerCrossExact (ℚRing.solve [])

singletonPlusPairClosesCorrelated :
  singletonBudget + pairBudgetPerCross ≡ correlatedBudgetPerCross
singletonPlusPairClosesCorrelated =
  trans
    (cong (singletonBudget +_)
      PairDeep.pairPerCrossExact)
    Selector.remainingPlusPairIsCorrelated

record SymbolicSingletonSplit (alpha beta : ℚ) : Set where
  field
    alphaNonnegative : 0ℚ ≤ alpha
    betaNonnegative : 0ℚ ≤ beta
    splitFits : alpha + beta ≤ singletonBudget

open SymbolicSingletonSplit public

balancedAlpha balancedBeta : ℚ
balancedAlpha = + 27 / 18874368
balancedBeta = + 28 / 18874368

balancedAlphaPositive : 0ℚ < balancedAlpha
balancedAlphaPositive = ℚP.positive⁻¹ balancedAlpha

balancedBetaPositive : 0ℚ < balancedBeta
balancedBetaPositive = ℚP.positive⁻¹ balancedBeta

balancedSplitExact :
  balancedAlpha + balancedBeta ≡ singletonBudget
balancedSplitExact = ℚRing.solve []

balancedSingletonSplit :
  SymbolicSingletonSplit balancedAlpha balancedBeta
balancedSingletonSplit = record
  { alphaNonnegative = ℚP.<⇒≤ balancedAlphaPositive
  ; betaNonnegative = ℚP.<⇒≤ balancedBetaPositive
  ; splitFits =
      subst
        (λ upper → balancedAlpha + balancedBeta ≤ upper)
        balancedSplitExact
        ℚP.≤-refl
  }

record OwnerEstimatePair
    (alpha beta charge localization repair : ℚ) : Set where
  field
    chargeNonnegative : 0ℚ ≤ charge
    localizationUpper : localization ≤ alpha * charge
    repairUpper : repair ≤ beta * charge

open OwnerEstimatePair public

symbolicSplitClosesSingletonBudget :
  ∀ {alpha beta charge localization repair} →
  SymbolicSingletonSplit alpha beta →
  OwnerEstimatePair alpha beta charge localization repair →
  localization + repair ≤ singletonBudget * charge
symbolicSplitClosesSingletonBudget
    {alpha} {beta} {charge} {localization} {repair}
    split estimates =
  let
    owners = ℚP.+-mono-≤
      (localizationUpper estimates)
      (repairUpper estimates)

    combinedExact :
      alpha * charge + beta * charge
      ≡ (alpha + beta) * charge
    combinedExact = ℚRing.solve-∀ alpha beta charge

    coefficientScaled :
      (alpha + beta) * charge ≤ singletonBudget * charge
    coefficientScaled =
      Norm.scaleNonnegative charge
        (chargeNonnegative estimates)
        (splitFits split)
  in
  subst
    (λ upper → localization + repair ≤ upper)
    combinedExact
    (ℚP.≤-trans owners coefficientScaled)

record CoefficientNoFit (alpha beta : ℚ) : Set where
  field
    totalStrictlyExceedsBudget : singletonBudget < alpha + beta

open CoefficientNoFit public

coefficientNoFitContradictsSymbolicSplit :
  ∀ {alpha beta} →
  CoefficientNoFit alpha beta →
  SymbolicSingletonSplit alpha beta →
  ¬ (alpha + beta ≤ singletonBudget)
coefficientNoFitContradictsSymbolicSplit noFit split =
  ℚP.<⇒≱ (totalStrictlyExceedsBudget noFit)

record CancelBeforeNormWitness
    (rawLocalization projectorRepair combinedResidual : ℚ) : Set where
  field
    combinedBeforeMajorisation :
      combinedResidual ≡ rawLocalization + projectorRepair

open CancelBeforeNormWitness public

cancelledOwnersCloseBudget :
  ∀ {alpha beta charge raw repair combined} →
  CancelBeforeNormWitness raw repair combined →
  SymbolicSingletonSplit alpha beta →
  OwnerEstimatePair alpha beta charge raw repair →
  combined ≤ singletonBudget * charge
cancelledOwnersCloseBudget cancellation split estimates =
  subst
    (λ lower → lower ≤ singletonBudget * _)
    (sym (combinedBeforeMajorisation cancellation))
    (symbolicSplitClosesSingletonBudget split estimates)

singletonBudgetArithmeticLevel : ProofLevel
singletonBudgetArithmeticLevel = machineChecked

symbolicSingletonFeasibilityLevel : ProofLevel
symbolicSingletonFeasibilityLevel = machineChecked

cancellationBeforeMajorisationBudgetLevel : ProofLevel
cancellationBeforeMajorisationBudgetLevel = machineChecked
