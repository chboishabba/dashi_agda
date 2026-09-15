{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedHessianWalkResummationCutRound353Exact where

------------------------------------------------------------------------
-- ROUND353 / H_stab SOURCE THEOREM DESCENDS TO THE EXISTING MARKED-WALK ABI
--
-- R352 still packages the source theorem as one inequality
--
--   Hdiff^src <= L^src * d_sub^src.
--
-- Repository archaeology shows that most of the route below that inequality
-- is already compiler-owned.  BalabanMarkedPolarisationResummation proves the
-- finite common-walk cancellation, surviving-walk triangle inequality and
-- marked-walk summation.  The older
-- BalabanDifferentiatedMarkedFactorProductExact theorem separately proves the
-- finite factor telescope once literal factorwise ordinary/marked bounds are
-- supplied; it is a donor/compiler and is deliberately not imported into this
-- safe owner.
--
-- Therefore the least-privilege source-facing cut is NOT a fresh generic
-- Hessian-Lipschitz theorem.  It is:
--
--   H_factor : instantiate the physical CMP99/CMP109 factorwise marked bounds
--              / surviving-walk marked estimate on the literal source carrier;
--   H_sum    : instantiate the retained CMP116 marked/tree summability;
--   H_scale  : compare the resulting source Hessian marked majorant with
--              L^src * d_sub^src.
--
-- Once the source walk carrier and H_scale are present, R352's source theorem
-- is compiler output.  This owner deliberately does not identify those source
-- coordinates with the selected R318/R350 carrier; R352's attachment remains
-- a separate same-object payment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (ℕ)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; absℝ; _-ℝ_; _*ℝ_; _≤ℝ_; ≤ℝ-trans)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum
import DASHI.Physics.YangMills.BalabanSelectedHessianStabilitySourceRound352Exact as R352

------------------------------------------------------------------------
-- Literal selected source instance of the existing marked-walk compiler.
------------------------------------------------------------------------

record CMP116MarkedWalkHessianStabilityData
    (Domain Background History : Set) : Set₁ where
  field
    walkData : Resum.MarkedWalkHessianData Domain Background History

    scale : ℕ
    leftDomain rightDomain : Domain
    background : Background
    history : History

    localisation : Resum.Localisation walkData
    leftCube rightCube : Resum.Cube walkData

    sourceLipschitz : ℝ
    sourceSubstitutionDistance : ℝ

    -- H_scale: after common-walk cancellation and CMP116 summation, the
    -- retained marked Hessian majorant is controlled at exactly the scale
    -- consumed by R352/R350.
    markedMajorantBelowLipschitzDistance :
      Resum.hessianMarkedMajorant walkData
        scale leftDomain rightDomain background history
        localisation leftCube rightCube
      ≤ℝ sourceLipschitz *ℝ sourceSubstitutionDistance

open CMP116MarkedWalkHessianStabilityData public

sourceHessianDifferenceFromWalks :
  ∀ {Domain Background History} →
  CMP116MarkedWalkHessianStabilityData Domain Background History →
  ℝ
sourceHessianDifferenceFromWalks dataSet =
  absℝ
    (Resum.localisedHessian (walkData dataSet)
      (scale dataSet) (leftDomain dataSet) (background dataSet)
      (history dataSet) (localisation dataSet)
      (leftCube dataSet) (rightCube dataSet)
    -ℝ
    Resum.localisedHessian (walkData dataSet)
      (scale dataSet) (rightDomain dataSet) (background dataSet)
      (history dataSet) (localisation dataSet)
      (leftCube dataSet) (rightCube dataSet))

markedWalkCompilerPaysSourceHessianStability :
  ∀ {Domain Background History}
    (dataSet : CMP116MarkedWalkHessianStabilityData Domain Background History) →
  sourceHessianDifferenceFromWalks dataSet
    ≤ℝ sourceLipschitz dataSet *ℝ sourceSubstitutionDistance dataSet
markedWalkCompilerPaysSourceHessianStability dataSet =
  ≤ℝ-trans
    (Resum.markedLocalisedHessianEstimate
      (walkData dataSet)
      (scale dataSet)
      (leftDomain dataSet)
      (rightDomain dataSet)
      (background dataSet)
      (history dataSet)
      (localisation dataSet)
      (leftCube dataSet)
      (rightCube dataSet))
    (markedMajorantBelowLipschitzDistance dataSet)

------------------------------------------------------------------------
-- Compile directly into the R352 source theorem ABI.  The chosen boundary
-- carrier is ℝ only because R352's record is point-indexed; this source object
-- is constant in that bookkeeping point.  R352's selected attachment still
-- performs the actual same-object identification.
------------------------------------------------------------------------

round353ToR352Source :
  ∀ {Domain Background History}
    (dataSet : CMP116MarkedWalkHessianStabilityData Domain Background History) →
  R352.CMP116LocalHessianStabilitySource ℝ
round353ToR352Source dataSet = record
  { sourceHessianDifference = λ _ → sourceHessianDifferenceFromWalks dataSet
  ; sourceLipschitz = sourceLipschitz dataSet
  ; sourceSubstitutionDistance = λ _ → sourceSubstitutionDistance dataSet
  ; sourceHessianStable = λ _ → markedWalkCompilerPaysSourceHessianStability dataSet
  }

------------------------------------------------------------------------
-- Pareto / proof-debt accounting.
------------------------------------------------------------------------

-- `walkData` is intentionally proof-bearing.  Its physical inhabitants must
-- pay the actual common-walk expansion/cancellation, surviving-walk CMP99
-- marked bound, and CMP116 marked/tree summability on the same source object.
literalCMP99CMP109FactorwiseMarkedInputLevel : ProofLevel
literalCMP99CMP109FactorwiseMarkedInputLevel = conditional

literalCMP116MarkedTreeSummabilityLevel : ProofLevel
literalCMP116MarkedTreeSummabilityLevel = conditional

-- H_scale is the only additional quantitative inequality after the existing
-- marked-walk compiler has produced the local Hessian majorant.
sourceMarkedMajorantScaleComparisonLevel : ProofLevel
sourceMarkedMajorantScaleComparisonLevel = conditional

-- Existing donor theorem:
-- BalabanDifferentiatedMarkedFactorProductExact.
-- It proves the finite factor telescope; R353 does not import it because its
-- historical generic-real helper surface is outside this safe cone.
finiteFactorTelescopeAlreadyOwned : Bool
finiteFactorTelescopeAlreadyOwned = true

finiteFactorTelescopeAlreadyOwnedIsTrue :
  finiteFactorTelescopeAlreadyOwned ≡ true
finiteFactorTelescopeAlreadyOwnedIsTrue = refl

markedWalkResummationCompilerLevel : ProofLevel
markedWalkResummationCompilerLevel = machineChecked

round353ToR352CompilerLevel : ProofLevel
round353ToR352CompilerLevel = machineChecked

freshGenericCauchyHessianTheoremRequired : Bool
freshGenericCauchyHessianTheoremRequired = false

freshGenericCauchyHessianTheoremRequiredIsFalse :
  freshGenericCauchyHessianTheoremRequired ≡ false
freshGenericCauchyHessianTheoremRequiredIsFalse = refl

factorwiseAndResummationAreSamePayment : Bool
factorwiseAndResummationAreSamePayment = false

factorwiseAndResummationAreSamePaymentIsFalse :
  factorwiseAndResummationAreSamePayment ≡ false
factorwiseAndResummationAreSamePaymentIsFalse = refl

r352SourceStabilityBecomesCompilerAfterRound353Inputs : Bool
r352SourceStabilityBecomesCompilerAfterRound353Inputs = true

r352SourceStabilityBecomesCompilerAfterRound353InputsIsTrue :
  r352SourceStabilityBecomesCompilerAfterRound353Inputs ≡ true
r352SourceStabilityBecomesCompilerAfterRound353InputsIsTrue = refl

record Round353Boundary : Set where
  constructor round353-boundary
  field
    physicalFactorwiseMarkedInputStillOpen : Bool
    physicalFactorwiseMarkedInputStillOpenIsTrue :
      physicalFactorwiseMarkedInputStillOpen ≡ true

    physicalMarkedTreeSummabilityStillOpen : Bool
    physicalMarkedTreeSummabilityStillOpenIsTrue :
      physicalMarkedTreeSummabilityStillOpen ≡ true

    sourceScaleComparisonStillOpen : Bool
    sourceScaleComparisonStillOpenIsTrue :
      sourceScaleComparisonStillOpen ≡ true

    finiteAssemblyAlreadyOwned : Bool
    finiteAssemblyAlreadyOwnedIsTrue :
      finiteAssemblyAlreadyOwned ≡ true

canonicalRound353Boundary : Round353Boundary
canonicalRound353Boundary =
  round353-boundary
    true refl
    true refl
    true refl
    true refl

round353FrontierRefinementLevel : ProofLevel
round353FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
