module DASHI.Analysis.NonArchimedeanSemilocalSigmaNonDescentExact where

------------------------------------------------------------------------
-- SEMILOCAL SIGMA NON-DESCENT
--
-- `ProlateScaling.semiloalProlateOp` has the source shape
--
--   P_S(s) = P_inf(s) tensor L_{2,n},
--
-- where `s` is an independent input and `L_{2,n}` is the fixed 2-adic factor.
-- Therefore the 2-adic factor by itself cannot determine the Archimedean real
-- part sigma.  This module instantiates the repository-wide generic
-- non-factorability theorem on the minimal two-state witness.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF


data SemilocalState : Set where
  sameTwoAdicAtCriticalSigma : SemilocalState
  sameTwoAdicOffCriticalSigma : SemilocalState


data TwoAdicFactor : Set where
  fixedCollatzMarkovFactor : TwoAdicFactor

projectTwoAdic : SemilocalState → TwoAdicFactor
projectTwoAdic sameTwoAdicAtCriticalSigma = fixedCollatzMarkovFactor
projectTwoAdic sameTwoAdicOffCriticalSigma = fixedCollatzMarkovFactor

isCriticalSigmaHalf : SemilocalState → Bool
isCriticalSigmaHalf sameTwoAdicAtCriticalSigma = true
isCriticalSigmaHalf sameTwoAdicOffCriticalSigma = false

criticalStatusDiffers :
  isCriticalSigmaHalf sameTwoAdicAtCriticalSigma
  ≡ isCriticalSigmaHalf sameTwoAdicOffCriticalSigma → ⊥
criticalStatusDiffers ()

semilocalSigmaNonFactorability :
  NF.NonFactorabilityWitness projectTwoAdic isCriticalSigmaHalf
semilocalSigmaNonFactorability =
  NF.nonFactorabilityWitness
    sameTwoAdicAtCriticalSigma
    sameTwoAdicOffCriticalSigma
    refl
    criticalStatusDiffers

criticalSigmaCannotFactorThroughTwoAdicAlone :
  NF.FactorsThrough projectTwoAdic isCriticalSigmaHalf → ⊥
criticalSigmaCannotFactorThroughTwoAdicAlone =
  NF.witnessRulesOutEveryFlatFactorisation semilocalSigmaNonFactorability

record SemilocalSourceBoundary : Set where
  constructor semilocalSourceBoundary
  field
    semilocalOperatorIsTensorProduct : Bool
    spectralParameterIsIndependentArgument : Bool
    twoAdicFactorFixedAtGivenLevel : Bool
    twoAdicFactorAloneDeterminesSigma : Bool
    extraCouplingLawNeededForAnchor : Bool

canonicalSemilocalSourceBoundary : SemilocalSourceBoundary
canonicalSemilocalSourceBoundary =
  semilocalSourceBoundary true true true false true

anchorNeedsMoreThanCommonTensorCarrier :
  SemilocalSourceBoundary.twoAdicFactorAloneDeterminesSigma
    canonicalSemilocalSourceBoundary
  ≡ false
anchorNeedsMoreThanCommonTensorCarrier = refl
