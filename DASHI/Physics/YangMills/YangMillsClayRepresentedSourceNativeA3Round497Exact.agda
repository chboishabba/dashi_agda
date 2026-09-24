{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayRepresentedSourceNativeA3Round497Exact where

------------------------------------------------------------------------
-- GOAL-1 A3 / ROUND497:
-- SOURCE-NATIVE CONTINUUM RECOVERY ON THE REPRESENTATION-FIRST CONSTRUCTION
--
-- R480 stored represented continuum semantics as a remaining conditional field.
-- R457, however, is parametric in the literal YM construction Y.  Instantiate
-- R457 directly at R483.asLiteralConstruction representedYM.
--
-- Then:
--   * the finite family is the represented construction's finite family;
--   * the continuum carrier is definitionally projected from the represented
--     countably-additive measure;
--   * the Schwinger family is definitionally built from that same carrier;
--   * R457 supplies the literal continuum + Schwinger semantics.
--
-- Therefore there is no separate "represented A3 semantic weld" theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayRepresentedContinuumRound476Exact as R476
import DASHI.Physics.YangMills.YangMillsClayRepresentedA3Round480Exact as R480
import DASHI.Physics.YangMills.YangMillsClayRepresentedLiteralConstructionRound483Exact as R483
import DASHI.Physics.YangMills.YangMillsClayGoal1SourceNativeContinuumRound457Exact as R457
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123

representedA3FromSourceNativeRecovery :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Hamiltonian Vacuum}
    {S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Nat Configuration ℝ
          (Configuration → ℝ)
          Position CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          Hilbert Hamiltonian Vacuum)}
    (representedYM :
      R483.RepresentedLiteralYMConstruction
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Hamiltonian Vacuum S)
    (group : G)
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    {stressLane :
      R123.DensityAnchoredCanonicalMetricStressLane
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {C =
          Physical.physicalLiteralCarriers
            G X Nat Configuration ℝ
            (Configuration → ℝ)
            Position CurvaturePolynomial LocalOperator OPECoefficient StressTensor
            Hilbert Hamiltonian Vacuum}
        {S = S}
        {Y = R483.asLiteralConstruction representedYM}
        {group = group}
        domain representation}
    (sourceNative :
      R457.SourceNativeContinuumAndOS stressLane) →
  R480.RepresentedA3At
    G X Configuration Position CurvaturePolynomial LocalOperator
    OPECoefficient StressTensor Hilbert Hamiltonian Vacuum
    S group
    (R483.finiteMeasure representedYM group)
    (R483.cylinderEncoding representedYM)
representedA3FromSourceNativeRecovery representedYM group sourceNative =
  let
    semantics = R457.literalContinuumAndSchwinger sourceNative
  in
  record
    { R480.RepresentedA3At.represented =
        R483.representedContinuum representedYM group
    ; R480.RepresentedA3At.literalContinuumLimit =
        Data.Product.proj₁ semantics
    ; R480.RepresentedA3At.literalSchwingerBelongs =
        Data.Product.proj₂ semantics
    }

representedA3IndependentSemanticWeldRequired : Bool
representedA3IndependentSemanticWeldRequired = false

sourceNativeRecoveryCanTargetRepresentedConstructionDirectly : Bool
sourceNativeRecoveryCanTargetRepresentedConstructionDirectly = true

round497RepresentedSourceNativeA3CompilerLevel : ProofLevel
round497RepresentedSourceNativeA3CompilerLevel = machineChecked

-- The physical payment is exactly the existing R457 source-native recovery,
-- now specialized to the representation-first Y.
literalRound497RepresentedA3SourceLevel : ProofLevel
literalRound497RepresentedA3SourceLevel =
  R457.literalRound457SourceNativeContinuumOSLevel
