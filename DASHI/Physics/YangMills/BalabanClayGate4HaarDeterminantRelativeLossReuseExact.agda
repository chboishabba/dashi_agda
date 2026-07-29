module DASHI.Physics.YangMills.BalabanClayGate4HaarDeterminantRelativeLossReuseExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT2LiteralActivityLossConstantsExact as Loss

------------------------------------------------------------------------
-- Primary provenance.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
-- Relationship: SU(2) exponential coordinates and compact-group Haar density.
--
-- Barry Simon,
-- "Trace Ideals and Their Applications", second edition,
-- American Mathematical Society (2005). DOI: 10.1090/surv/120.
-- Relationship: trace-log series and trace-class determinant bounds.
--
-- Gerald V. Dunne,
-- "Functional Determinants in Quantum Field Theory",
-- Journal of Physics A: Mathematical and Theoretical 41 (2008), 304006.
-- DOI: 10.1088/1751-8113/41/30/304006; arXiv:0711.1178.
-- Relationship: determinant methodology only.  DASHI's present operator is a
-- finite lattice Hessian, so no zeta regularization is imported here.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
------------------------------------------------------------------------

record HaarDeterminantRelativeLossReuse
    (Scale Traversal Link Polymer Index Operator : Set) : Set₁ where
  field
    haarData : Loss.SU2HaarLossData Link Polymer ℚ
    determinantData :
      Loss.RelativeDeterminantLossData Index Polymer Operator ℚ

    polymerOf : Scale → Traversal → Polymer
    determinantIndexOf : Scale → Traversal → Index

    exponential : ℚ → ℚ
    exponentialMonotone : ∀ {left right} →
      left ≤ right → exponential left ≤ exponential right

    haarMultiplier determinantMultiplier : Scale → Traversal → ℚ

    haarMultiplierMeaning : ∀ scale traversal →
      haarMultiplier scale traversal
      ≡ exponential
          (Loss.haarLogLoss haarData (polymerOf scale traversal))

    determinantMultiplierMeaning : ∀ scale traversal →
      determinantMultiplier scale traversal
      ≡ exponential
          (Loss.determinantLogLoss determinantData
            (determinantIndexOf scale traversal)
            (polymerOf scale traversal))

    determinantIndexSmallField : ∀ scale traversal →
      Loss.SmallFieldIndex determinantData
        (determinantIndexOf scale traversal)

    physicalHaar referenceHaar physicalDeterminant referenceDeterminant :
      Scale → Traversal → ℚ

    physicalHaarRelativeMeaning : ∀ scale traversal →
      physicalHaar scale traversal
      ≤ haarMultiplier scale traversal * referenceHaar scale traversal

    physicalDeterminantRelativeMeaning : ∀ scale traversal →
      physicalDeterminant scale traversal
      ≤ determinantMultiplier scale traversal
        * referenceDeterminant scale traversal

open HaarDeterminantRelativeLossReuse public

haarLogLossBoundFromExistingOwner :
  ∀ {Scale Traversal Link Polymer Index Operator}
    (dataSet : HaarDeterminantRelativeLossReuse
      Scale Traversal Link Polymer Index Operator)
    scale traversal →
  Loss.LessEqual (haarData dataSet)
    (Loss.haarLogLoss (haarData dataSet)
      (polymerOf dataSet scale traversal))
    (Loss.natScale (haarData dataSet)
      (Loss.polymerLossPerBlock (haarData dataSet))
      (Loss.polymerSize (haarData dataSet)
        (polymerOf dataSet scale traversal)))
haarLogLossBoundFromExistingOwner dataSet scale traversal =
  Loss.haarJacobianPolymerLossBound (haarData dataSet)
    (polymerOf dataSet scale traversal)

determinantLogLossBoundFromExistingOwner :
  ∀ {Scale Traversal Link Polymer Index Operator}
    (dataSet : HaarDeterminantRelativeLossReuse
      Scale Traversal Link Polymer Index Operator)
    scale traversal →
  Loss.LessEqual (determinantData dataSet)
    (Loss.determinantLogLoss (determinantData dataSet)
      (determinantIndexOf dataSet scale traversal)
      (polymerOf dataSet scale traversal))
    (Loss.natScale (determinantData dataSet)
      (Loss.determinantLossPerBlock (determinantData dataSet)
        (determinantIndexOf dataSet scale traversal))
      (Loss.polymerSize (determinantData dataSet)
        (polymerOf dataSet scale traversal)))
determinantLogLossBoundFromExistingOwner dataSet scale traversal =
  Loss.fluctuationDeterminantPolymerLossBound (determinantData dataSet)
    (determinantIndexOf dataSet scale traversal)
    (polymerOf dataSet scale traversal)
    (determinantIndexSmallField dataSet scale traversal)

haarMultiplierBound :
  ∀ {Scale Traversal Link Polymer Index Operator}
    (dataSet : HaarDeterminantRelativeLossReuse
      Scale Traversal Link Polymer Index Operator)
    scale traversal →
  haarMultiplier dataSet scale traversal
  ≤ exponential dataSet
      (Loss.natScale (haarData dataSet)
        (Loss.polymerLossPerBlock (haarData dataSet))
        (Loss.polymerSize (haarData dataSet)
          (polymerOf dataSet scale traversal)))
haarMultiplierBound dataSet scale traversal =
  subst
    (λ lower → lower ≤ exponential dataSet
      (Loss.natScale (haarData dataSet)
        (Loss.polymerLossPerBlock (haarData dataSet))
        (Loss.polymerSize (haarData dataSet)
          (polymerOf dataSet scale traversal))))
    (sym (haarMultiplierMeaning dataSet scale traversal))
    (exponentialMonotone dataSet
      (haarLogLossBoundFromExistingOwner dataSet scale traversal))

determinantMultiplierBound :
  ∀ {Scale Traversal Link Polymer Index Operator}
    (dataSet : HaarDeterminantRelativeLossReuse
      Scale Traversal Link Polymer Index Operator)
    scale traversal →
  determinantMultiplier dataSet scale traversal
  ≤ exponential dataSet
      (Loss.natScale (determinantData dataSet)
        (Loss.determinantLossPerBlock (determinantData dataSet)
          (determinantIndexOf dataSet scale traversal))
        (Loss.polymerSize (determinantData dataSet)
          (polymerOf dataSet scale traversal)))
determinantMultiplierBound dataSet scale traversal =
  subst
    (λ lower → lower ≤ exponential dataSet
      (Loss.natScale (determinantData dataSet)
        (Loss.determinantLossPerBlock (determinantData dataSet)
          (determinantIndexOf dataSet scale traversal))
        (Loss.polymerSize (determinantData dataSet)
          (polymerOf dataSet scale traversal))))
    (sym (determinantMultiplierMeaning dataSet scale traversal))
    (exponentialMonotone dataSet
      (determinantLogLossBoundFromExistingOwner dataSet scale traversal))

haarRelativeFactorReuseLevel : ProofLevel
haarRelativeFactorReuseLevel = machineChecked

determinantRelativeFactorReuseLevel : ProofLevel
determinantRelativeFactorReuseLevel = machineChecked

haarMultiplierBudgetReuseLevel : ProofLevel
haarMultiplierBudgetReuseLevel = machineChecked

determinantMultiplierBudgetReuseLevel : ProofLevel
determinantMultiplierBudgetReuseLevel = machineChecked

physicalHaarRatioMeaningInputsLevel : ProofLevel
physicalHaarRatioMeaningInputsLevel = conditional

physicalDeterminantRatioMeaningInputsLevel : ProofLevel
physicalDeterminantRatioMeaningInputsLevel = conditional

physicalRelativeHessianSmallFieldInputsLevel : ProofLevel
physicalRelativeHessianSmallFieldInputsLevel = conditional
