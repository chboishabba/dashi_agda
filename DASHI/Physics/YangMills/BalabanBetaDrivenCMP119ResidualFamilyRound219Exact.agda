{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact where

------------------------------------------------------------------------
-- ROUND219 / REMOVE THE LAST DENSITY/COUPLING IDENTITY RECEIPTS
--
-- A CMP119 complete-density object has enough structure to be built directly
-- on the beta-driven density/coupling coordinates.  We therefore ask the source
-- realization only for the residual CMP119 coordinates and the two source
-- assembly equations.  The fields
--
--   rho_k = Beta.densityAt inputs k
--   g_k   = History.couplingAt (Beta.betaHistory inputs) k
--
-- are then definitionally fixed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.Balaban1989BetaSplitInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Published
import DASHI.Physics.YangMills.BalabanCMP119Section2CompleteDensityDictionaryExact as CMP119
import DASHI.Physics.YangMills.BalabanSourceNativeStrongStateEntryExact as Native
import DASHI.Physics.YangMills.BalabanBetaDrivenSourceNativePublishedFlowRound218Exact as R218

record BetaDrivenCMP119ResidualFamily
    {trajectory split}
    (inputs : Beta.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}) : Set₂ where
  field
    Operation Action Field : Set
    RegularTerm RTerm BoundaryTerm VacuumTerm : Set
    SmallFieldScale BlockRadius AnalyticRadius Decay : Set

    operationAt : Nat → Operation
    effectiveActionAt : Nat → Action
    backgroundAt : Nat → Field
    regularEAt : Nat → RegularTerm
    rOperationAt : Nat → RTerm
    boundaryAt : Nat → BoundaryTerm
    vacuumAt : Nat → VacuumTerm

    epsilonAt : Nat → SmallFieldScale
    blockRadiusAt : Nat → BlockRadius
    alpha0At alpha1At : Nat → AnalyticRadius
    decayAt : Nat → Decay

    assembleDensity : Operation → Action → Beta.Density inputs
    assembleAction :
      ℚ → Field → RegularTerm → RTerm → BoundaryTerm → VacuumTerm → Action

    densityEquation : ∀ scale →
      Beta.densityAt inputs scale
      ≡ assembleDensity (operationAt scale) (effectiveActionAt scale)

    actionEquation : ∀ scale →
      effectiveActionAt scale
      ≡ assembleAction
          (History.couplingAt (Beta.betaHistory inputs) scale)
          (backgroundAt scale)
          (regularEAt scale)
          (rOperationAt scale)
          (boundaryAt scale)
          (vacuumAt scale)

open BetaDrivenCMP119ResidualFamily public

completeDensityAt :
  ∀ {trajectory split inputs} →
  BetaDrivenCMP119ResidualFamily
    {trajectory = trajectory} {split = split} inputs →
  Nat →
  CMP119.CMP119Section2CompleteDensity
    ℚ (Beta.Density inputs)
    (Operation _) (Action _) (Field _)
    (RegularTerm _) (RTerm _) (BoundaryTerm _) (VacuumTerm _)
    (SmallFieldScale _) (BlockRadius _) (AnalyticRadius _) (Decay _)
completeDensityAt {inputs = inputs} family scale = record
  { CMP119.CMP119Section2CompleteDensity.scale = scale
  ; CMP119.CMP119Section2CompleteDensity.g =
      History.couplingAt (Beta.betaHistory inputs) scale
  ; CMP119.CMP119Section2CompleteDensity.rho = Beta.densityAt inputs scale
  ; CMP119.CMP119Section2CompleteDensity.T = operationAt family scale
  ; CMP119.CMP119Section2CompleteDensity.effectiveAction = effectiveActionAt family scale
  ; CMP119.CMP119Section2CompleteDensity.background = backgroundAt family scale
  ; CMP119.CMP119Section2CompleteDensity.regularE = regularEAt family scale
  ; CMP119.CMP119Section2CompleteDensity.rOperationR = rOperationAt family scale
  ; CMP119.CMP119Section2CompleteDensity.boundaryB = boundaryAt family scale
  ; CMP119.CMP119Section2CompleteDensity.vacuumE = vacuumAt family scale
  ; CMP119.CMP119Section2CompleteDensity.epsilon = epsilonAt family scale
  ; CMP119.CMP119Section2CompleteDensity.blockRadius = blockRadiusAt family scale
  ; CMP119.CMP119Section2CompleteDensity.alpha0 = alpha0At family scale
  ; CMP119.CMP119Section2CompleteDensity.alpha1 = alpha1At family scale
  ; CMP119.CMP119Section2CompleteDensity.decayKappa = decayAt family scale
  ; CMP119.CMP119Section2CompleteDensity.assembleDensity = assembleDensity family
  ; CMP119.CMP119Section2CompleteDensity.assembleAction = assembleAction family
  ; CMP119.CMP119Section2CompleteDensity.densityEquation = densityEquation family scale
  ; CMP119.CMP119Section2CompleteDensity.actionEquation = actionEquation family scale
  }

record BetaDrivenSourceNativeResidualInputs
    {trajectory split}
    (inputs : Beta.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}) : Set₂ where
  field
    residual : BetaDrivenCMP119ResidualFamily inputs

    theorem1 :
      Published.Balaban1989Theorem1Witness
        (Beta.betaDrivenCompleteDensityFlow inputs)

    differentiatedAt : Nat →
      Native.CMP109DifferentiatedCoordinate (RegularTerm residual)

open BetaDrivenSourceNativeResidualInputs public

asRound218 :
  ∀ {trajectory split inputs} →
  BetaDrivenSourceNativeResidualInputs
    {trajectory = trajectory} {split = split} inputs →
  R218.BetaDrivenSourceNativePublishedFlowInputs inputs
asRound218 {inputs = inputs} dataSet = record
  { R218.BetaDrivenSourceNativePublishedFlowInputs.Operation = Operation (residual dataSet)
  ; R218.BetaDrivenSourceNativePublishedFlowInputs.Action = Action (residual dataSet)
  ; R218.BetaDrivenSourceNativePublishedFlowInputs.Field = Field (residual dataSet)
  ; R218.BetaDrivenSourceNativePublishedFlowInputs.RegularTerm = RegularTerm (residual dataSet)
  ; R218.BetaDrivenSourceNativePublishedFlowInputs.RTerm = RTerm (residual dataSet)
  ; R218.BetaDrivenSourceNativePublishedFlowInputs.BoundaryTerm = BoundaryTerm (residual dataSet)
  ; R218.BetaDrivenSourceNativePublishedFlowInputs.VacuumTerm = VacuumTerm (residual dataSet)
  ; R218.BetaDrivenSourceNativePublishedFlowInputs.SmallFieldScale = SmallFieldScale (residual dataSet)
  ; R218.BetaDrivenSourceNativePublishedFlowInputs.BlockRadius = BlockRadius (residual dataSet)
  ; R218.BetaDrivenSourceNativePublishedFlowInputs.AnalyticRadius = AnalyticRadius (residual dataSet)
  ; R218.BetaDrivenSourceNativePublishedFlowInputs.Decay = Decay (residual dataSet)
  ; R218.BetaDrivenSourceNativePublishedFlowInputs.theorem1 = theorem1 dataSet
  ; R218.BetaDrivenSourceNativePublishedFlowInputs.completeDensityAt =
      completeDensityAt (residual dataSet)
  ; R218.BetaDrivenSourceNativePublishedFlowInputs.densityIsBetaDensity = λ scale → refl
  ; R218.BetaDrivenSourceNativePublishedFlowInputs.couplingIsBetaHistory = λ scale → refl
  ; R218.BetaDrivenSourceNativePublishedFlowInputs.differentiatedAt = differentiatedAt dataSet
  }

betaDensitySameObjectByConstruction :
  ∀ {trajectory split inputs}
    (dataSet : BetaDrivenSourceNativeResidualInputs
      {trajectory = trajectory} {split = split} inputs) →
  ∀ scale →
  CMP119.rho (R218.completeDensityAt (asRound218 dataSet) scale)
  ≡ Beta.densityAt inputs scale
betaDensitySameObjectByConstruction dataSet scale = refl

betaCouplingSameObjectByConstruction :
  ∀ {trajectory split inputs}
    (dataSet : BetaDrivenSourceNativeResidualInputs
      {trajectory = trajectory} {split = split} inputs) →
  ∀ scale →
  CMP119.g (R218.completeDensityAt (asRound218 dataSet) scale)
  ≡ History.couplingAt (Beta.betaHistory inputs) scale
betaCouplingSameObjectByConstruction dataSet scale = refl

betaDrivenCMP119ResidualFamilyCompilerLevel : ProofLevel
betaDrivenCMP119ResidualFamilyCompilerLevel = machineChecked

betaDensityAndCouplingSameObjectCompilerLevel : ProofLevel
betaDensityAndCouplingSameObjectCompilerLevel = machineChecked

-- The remaining source content is now exactly the CMP119 residual family
-- (T/A/background/E/R/B/vacuum/analytic scales plus equations (2.18)/(2.23)),
-- the imported CMP122 Theorem-1 witness on that beta-driven flow, and the CMP109
-- differentiated coordinate on the SAME regular-E carrier.
literalBetaDrivenCMP119ResidualFamilyLevel : ProofLevel
literalBetaDrivenCMP119ResidualFamilyLevel = conditional

literalBetaDrivenCMP119DifferentiatedCoordinateLevel : ProofLevel
literalBetaDrivenCMP119DifferentiatedCoordinateLevel = conditional
