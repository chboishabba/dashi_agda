module DASHI.Physics.YangMills.BalabanCMP122ConditionalRGClosure where

-- Literal wrapper for Theorem 1 of Balaban, CMP 122 II (article pp. 355--356,
-- conclusion on p. 391).  The theorem is conditional: it assumes that every
-- effective coupling lies in a sufficiently small interval ]0, γ].
--
-- This is deliberately a paper-import boundary.  It does not claim to prove
-- the small-coupling trajectory, nor does it replace the separate continuum
-- or observable analysis which CMP 122 explicitly leaves for later work.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; _≤ℝ_ ; _<ℝ_ ; 0ℝ )
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; VerificationStatus
  ; balaban-cmp-122
  ; paperImport
  )
open import DASHI.Physics.YangMills.BalabanSection2InductivePackage using
  ( BalabanSection2InductivePackage
  ; UniformBalabanRGClosure
  )
open import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory using
  ( BalabanInverseSquareCouplingStep
  ; CouplingTrajectoryBoundedBy
  )
open import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget using
  ( InverseSquareBudgetArithmetic
  ; InverseSquareBudgetOrderBridge
  ; InverseSquareThresholdControlsCoupling
  ; BalabanBetaPrefixBound
  ; BalabanBareCouplingSchedule
  ; couplingTrajectoryBoundedByGamma
  ; scheduleTrajectoryBoundedByGamma
  )

-- CMP 122 II Theorem 1 as an imported implication, in the exact direction
-- used by the paper: a verified small-coupling trajectory yields the Sect. 2
-- [III] package at every scale.  This is the canonical source boundary.
record BalabanCMP122ConditionalTheorem : Set₁ where
  field
    γ : ℝ
    γ-positive : 0ℝ <ℝ γ
    section2Package : BalabanSection2InductivePackage
    conclusion :
      (step : BalabanInverseSquareCouplingStep) →
      CouplingTrajectoryBoundedBy γ step →
      UniformBalabanRGClosure
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

open BalabanCMP122ConditionalTheorem public

balabanConditionalUniformRG :
  (theorem : BalabanCMP122ConditionalTheorem) →
  (step : BalabanInverseSquareCouplingStep) →
  CouplingTrajectoryBoundedBy (γ theorem) step →
  UniformBalabanRGClosure
balabanConditionalUniformRG theorem step trajectory =
  conclusion theorem step trajectory

-- Finite-cutoff composition.  This is the entire mechanical bridge from a
-- cumulative β-budget to the published CMP 122 implication.  The hard input
-- remains `BalabanBetaPrefixBound`; no β estimate is imported or asserted
-- here.  The Section-2 package's terminal scale is source-owned, while `K`
-- is the cutoff through which the coupling premise was certified.
finiteCutoffUniformBalabanRG :
  (theorem : BalabanCMP122ConditionalTheorem) →
  (arith : InverseSquareBudgetArithmetic) →
  (order : InverseSquareBudgetOrderBridge) →
  {K : ℕ} →
  {step : BalabanInverseSquareCouplingStep} →
  (threshold : InverseSquareThresholdControlsCoupling K (γ theorem) step) →
  (budget : BalabanBetaPrefixBound K step threshold) →
  UniformBalabanRGClosure
finiteCutoffUniformBalabanRG theorem arith order {step = step} threshold budget =
  balabanConditionalUniformRG theorem step
    (couplingTrajectoryBoundedByGamma arith order threshold budget)

relabelCouplingTrajectoryBound :
  {γ₁ γ₂ : ℝ} →
  {step : BalabanInverseSquareCouplingStep} →
  γ₁ ≡ γ₂ →
  CouplingTrajectoryBoundedBy γ₁ step →
  CouplingTrajectoryBoundedBy γ₂ step
relabelCouplingTrajectoryBound refl bounded = bounded

-- The schedule version is the finite-cutoff theorem intended for the later
-- continuum construction.  The equality pins the schedule to the particular
-- small interval used by the published CMP 122 theorem.
finiteCutoffScheduledBalabanRG :
  (theorem : BalabanCMP122ConditionalTheorem) →
  (arith : InverseSquareBudgetArithmetic) →
  (order : InverseSquareBudgetOrderBridge) →
  (schedule : BalabanBareCouplingSchedule) →
  γ schedule ≡ γ theorem →
  ∀ K → UniformBalabanRGClosure
finiteCutoffScheduledBalabanRG theorem arith order schedule γ≡ K =
  balabanConditionalUniformRG theorem (BalabanBareCouplingSchedule.trajectory schedule K)
    (relabelCouplingTrajectoryBound γ≡
      (scheduleTrajectoryBoundedByGamma arith order schedule K))

record BalabanCMP122ConditionalRGClosure : Set₁ where
  field
    γ : ℝ
    γ-positive : 0ℝ <ℝ γ

    terminalScale : ℕ
    effectiveCoupling : ℕ → ℝ
    couplingRemainsSmall :
      ∀ k → k ≤ terminalScale →
      (0ℝ <ℝ effectiveCoupling k) × (effectiveCoupling k ≤ℝ γ)

    section2Package : BalabanSection2InductivePackage
    effectiveDensityRepresentation :
      ∀ k → k ≤ BalabanSection2InductivePackage.terminalScale section2Package →
      BalabanSection2InductivePackage.EffectiveDensity section2Package k
    smallFieldBounds :
      ∀ k →
      (k≤sourceTerminal :
        k ≤ BalabanSection2InductivePackage.terminalScale section2Package) →
      BalabanSection2InductivePackage.smallFieldEstimate
        section2Package k k≤sourceTerminal
    largeFieldRBounds :
      ∀ k →
      (k≤sourceTerminal :
        k ≤ BalabanSection2InductivePackage.terminalScale section2Package) →
      BalabanSection2InductivePackage.largeFieldREstimate
        section2Package k k≤sourceTerminal
    localisationSummability :
      ∀ k →
      (k≤sourceTerminal :
        k ≤ BalabanSection2InductivePackage.terminalScale section2Package) →
      BalabanSection2InductivePackage.localisationSummability
        section2Package k k≤sourceTerminal
    polymerExpansionConverges :
      ∀ k →
      (k≤sourceTerminal :
        k ≤ BalabanSection2InductivePackage.terminalScale section2Package) →
      BalabanSection2InductivePackage.rOperationConvergence
        section2Package k k≤sourceTerminal
    nextScaleClosure :
      ∀ k →
      (k≤sourceTerminal :
        k ≤ BalabanSection2InductivePackage.terminalScale section2Package) →
      BalabanSection2InductivePackage.nextScaleClosure
        section2Package k k≤sourceTerminal
    scaleVolumeUniformity :
      BalabanSection2InductivePackage.uniformInVolume section2Package

    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    noClayPromotion : clayYangMillsPromoted ≡ false

open BalabanCMP122ConditionalRGClosure public

-- The source-native result of unpacking a specialised CMP 122 theorem
-- witness.  This is the
-- canonical RG consumer: it carries the literal Sect. 2 package and does not
-- mention the legacy P06/P10/P11/P33 assembly interfaces.
specialisedCMP122ClosureToUniformRG :
  BalabanCMP122ConditionalRGClosure →
  UniformBalabanRGClosure
specialisedCMP122ClosureToUniformRG cmp122 = record
  { section2 = section2Package cmp122
  ; terminalScale = BalabanSection2InductivePackage.terminalScale (section2Package cmp122)
  ; terminalScaleAgrees = refl
  ; allScalesEffectiveDensityForm = effectiveDensityRepresentation cmp122
  ; allScalesSmallFieldEstimate = smallFieldBounds cmp122
  ; allScalesLargeFieldREstimate = largeFieldRBounds cmp122
  ; allScalesLocalisationSummability =
      localisationSummability cmp122
  ; allScalesROperationConvergence = polymerExpansionConverges cmp122
  ; allScalesNextStepClosure =
      nextScaleClosure cmp122
  ; uniformInVolume =
      scaleVolumeUniformity cmp122
  ; sourceAuthorityId = balaban-cmp-122
  ; theoremLocator = "CMP 122 II Theorem 1 (pp. 355--356), concluding p. 391; CMP 119 Sect. 2 (pp. 254--263)"
  ; status = paperImport
  ; noClayPromotion = refl
  }

-- The premise and conclusion have been transcribed, but no source witness is
-- installed here: it must be reviewed against Sect. 2 [III] before it can be
-- used as a paper import in a promoted route.
currentBalabanCMP122ConditionalRGClosureAvailable : Set
currentBalabanCMP122ConditionalRGClosureAvailable = ⊥

currentBalabanCMP122ConditionalTheoremAvailable : Set
currentBalabanCMP122ConditionalTheoremAvailable = ⊥

-- This metadata records the exact intended source citation without asserting
-- that the unextracted Sect. 2 package has already been instantiated.
currentBalabanCMP122Source : SourceAuthorityId
currentBalabanCMP122Source = balaban-cmp-122

currentBalabanCMP122Status : VerificationStatus
currentBalabanCMP122Status = paperImport
