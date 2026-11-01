module DASHI.Physics.YangMills.BalabanP33PhysicalSingletonBudgetOptimizationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Replace the Round-39 feasibility witness 27+28=55 by the output type of an
-- actual finite parameter optimization.  A certificate identifies one
-- admissible physical parameter assignment, proves its two exact owner costs,
-- proves global minimality inside the declared candidate family, and proves
-- that the resulting total lies below the literal 55/18874368 budget.
--
-- A dual no-fit certificate is also supplied: if every admissible candidate is
-- bounded below by a number strictly larger than the budget, then no generated
-- successful certificate can exist.  Thus a crude estimate family fails
-- closed rather than being rescued by an arbitrary symbolic split.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using
  (cong₂; subst; trans)
open import Relation.Nullary.Negation using (¬_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanP33SingletonBudgetFeasibilityExact as Feasible

singletonBudget : ℚ
singletonBudget = Selector.remainingSingletonCoefficient

record PhysicalSingletonCosts : Set where
  constructor physicalCosts
  field
    rawLocalizationCost : ℚ
    multiplierDefectCost : ℚ
open PhysicalSingletonCosts public

singletonTotalCost : PhysicalSingletonCosts → ℚ
singletonTotalCost costs =
  rawLocalizationCost costs + multiplierDefectCost costs

record PhysicalSingletonCostModel (Parameter : Set) : Set₁ where
  field
    Admissible : Parameter → Set
    evaluate : Parameter → PhysicalSingletonCosts
open PhysicalSingletonCostModel public

record GeneratedPhysicalSingletonCertificate
    {Parameter : Set}
    (model : PhysicalSingletonCostModel Parameter) : Set₁ where
  field
    physicalParameterAssignment : Parameter
    physicalParameterAdmissible :
      Admissible model physicalParameterAssignment

    reportedRawLocalizationCost : ℚ
    reportedMultiplierDefectCost : ℚ
    reportedSingletonTotalCost : ℚ

    rawLocalizationCostExact :
      reportedRawLocalizationCost
      ≡ rawLocalizationCost
          (evaluate model physicalParameterAssignment)

    multiplierDefectCostExact :
      reportedMultiplierDefectCost
      ≡ multiplierDefectCost
          (evaluate model physicalParameterAssignment)

    singletonTotalCostExact :
      reportedSingletonTotalCost
      ≡ reportedRawLocalizationCost
        + reportedMultiplierDefectCost

    rawLocalizationCostNonnegative :
      0ℚ ≤ reportedRawLocalizationCost
    multiplierDefectCostNonnegative :
      0ℚ ≤ reportedMultiplierDefectCost

    physicalAssignmentGloballyMinimal : ∀ candidate →
      Admissible model candidate →
      reportedSingletonTotalCost
      ≤ singletonTotalCost (evaluate model candidate)

    singletonTotalBelowBudget :
      reportedSingletonTotalCost ≤ singletonBudget

open GeneratedPhysicalSingletonCertificate public

generatedCertificateGivesSymbolicSplit :
  ∀ {Parameter}
    {model : PhysicalSingletonCostModel Parameter} →
  (certificate : GeneratedPhysicalSingletonCertificate model) →
  Feasible.SymbolicSingletonSplit
    (reportedRawLocalizationCost certificate)
    (reportedMultiplierDefectCost certificate)
generatedCertificateGivesSymbolicSplit certificate = record
  { Feasible.SymbolicSingletonSplit.alphaNonnegative =
      rawLocalizationCostNonnegative certificate
  ; Feasible.SymbolicSingletonSplit.betaNonnegative =
      multiplierDefectCostNonnegative certificate
  ; Feasible.SymbolicSingletonSplit.splitFits =
      subst
        (λ total → total ≤ singletonBudget)
        (singletonTotalCostExact certificate)
        (singletonTotalBelowBudget certificate) }

generatedPhysicalOwnerBoundsCloseBudget :
  ∀ {Parameter}
    {model : PhysicalSingletonCostModel Parameter}
    (certificate : GeneratedPhysicalSingletonCertificate model)
    {charge rawLocalization multiplierDefect} →
  Feasible.OwnerEstimatePair
    (reportedRawLocalizationCost certificate)
    (reportedMultiplierDefectCost certificate)
    charge rawLocalization multiplierDefect →
  rawLocalization + multiplierDefect ≤ singletonBudget * charge
generatedPhysicalOwnerBoundsCloseBudget certificate estimates =
  Feasible.symbolicSplitClosesSingletonBudget
    (generatedCertificateGivesSymbolicSplit certificate)
    estimates

record SingletonNoFitDual
    {Parameter : Set}
    (model : PhysicalSingletonCostModel Parameter) : Set₁ where
  field
    certifiedLowerBound : ℚ
    allAdmissibleCostsAboveLowerBound : ∀ candidate →
      Admissible model candidate →
      certifiedLowerBound
      ≤ singletonTotalCost (evaluate model candidate)
    lowerBoundStrictlyExceedsBudget :
      singletonBudget < certifiedLowerBound
open SingletonNoFitDual public

noFitDualRejectsEveryAdmissibleBudgetFit :
  ∀ {Parameter}
    {model : PhysicalSingletonCostModel Parameter} →
  SingletonNoFitDual model →
  ∀ candidate →
  Admissible model candidate →
  ¬ (singletonTotalCost (evaluate model candidate) ≤ singletonBudget)
noFitDualRejectsEveryAdmissibleBudgetFit dual candidate admissible fit =
  ℚP.<-irrefl singletonBudget
    (ℚP.<-≤-trans
      (ℚP.<-≤-trans
        (lowerBoundStrictlyExceedsBudget dual)
        (allAdmissibleCostsAboveLowerBound dual candidate admissible))
      fit)

noFitDualContradictsGeneratedCertificate :
  ∀ {Parameter}
    {model : PhysicalSingletonCostModel Parameter} →
  SingletonNoFitDual model →
  ¬ GeneratedPhysicalSingletonCertificate model
noFitDualContradictsGeneratedCertificate dual certificate =
  noFitDualRejectsEveryAdmissibleBudgetFit
    dual
    (physicalParameterAssignment certificate)
    (physicalParameterAdmissible certificate)
    (subst
      (λ total → total ≤ singletonBudget)
      (trans
        (singletonTotalCostExact certificate)
        (cong₂ _+_
          (rawLocalizationCostExact certificate)
          (multiplierDefectCostExact certificate)))
      (singletonTotalBelowBudget certificate))

record CandidateDominance
    {Parameter : Set}
    (model : PhysicalSingletonCostModel Parameter)
    (left right : Parameter) : Set where
  field
    leftAdmissible : Admissible model left
    rightAdmissible : Admissible model right
    leftNoMoreExpensive :
      singletonTotalCost (evaluate model left)
      ≤ singletonTotalCost (evaluate model right)
open CandidateDominance public

candidateDominanceTransitive :
  ∀ {Parameter}
    {model : PhysicalSingletonCostModel Parameter}
    {first second third} →
  CandidateDominance model first second →
  CandidateDominance model second third →
  CandidateDominance model first third
candidateDominanceTransitive firstSecond secondThird = record
  { leftAdmissible = leftAdmissible firstSecond
  ; rightAdmissible = rightAdmissible secondThird
  ; leftNoMoreExpensive = ℚP.≤-trans
      (leftNoMoreExpensive firstSecond)
      (leftNoMoreExpensive secondThird) }

physicalSingletonOptimizationCertificateLevel : ProofLevel
physicalSingletonOptimizationCertificateLevel = machineChecked

physicalSingletonNoFitDualLevel : ProofLevel
physicalSingletonNoFitDualLevel = machineChecked

generatedPhysicalSingletonCertificateProducerLevel : ProofLevel
generatedPhysicalSingletonCertificateProducerLevel = conditional
