{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyMarkedStressOSWightmanReconstructionExact where

------------------------------------------------------------------------
-- MARKED LOCAL-C STRESS OS/WIGHTMAN RECONSTRUCTION.
--
-- Source calibration:
--   Osterwalder--Schrader, CMP 31 (1973), Theorem E->R:
--   Euclidean Green functions satisfying E0--E4 determine a unique Wightman
--   family satisfying R0--R5.
--
--   Osterwalder--Schrader, CMP 42 (1975):
--   reconstructs the Wightman distributions by analytic continuation under
--   the weakened/technical regularity hypotheses and recovers the remaining
--   Wightman axioms.
--
-- The theorem is standard external authority.  What is NOT standard/imported
-- for free is that DASHI's completed Local-C stress insertion belongs to an
-- extended marked Schwinger hierarchy satisfying those hypotheses.
--
-- Round109 already gives the completed marked stress field.
-- Round128/129 already pin it to the SAME continuum Schwinger family/measure.
-- This file therefore isolates the correct remaining physical producer:
--
--   "the Local-C stress-marked Schwinger hierarchy satisfies the marked OS
--    regularity/covariance/positivity/symmetry/clustering hypotheses."
--
-- Once such evidence and the standard marked-field reconstruction authority
-- are supplied, the selected Wightman stress operator is definitionally the
-- continuation image of the pinned Local-C stress.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.CMP119CosmologyLocalCWightmanStressHingeExact as Hinge
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanSameFamilyOSStressRecoveryRound128Exact as R128
import DASHI.Physics.YangMills.BalabanDensityAnchoredStressLaneRound123Exact as R123
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaDensity
import DASHI.Physics.YangMills.BalabanCMP116SubstitutedActivityHessianRound103Exact as Chain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricSourceDomainRound106Exact as Domain
import DASHI.Physics.YangMills.BalabanCMP116CanonicalMetricStressRepresentationRound106Exact as StressRep

record LocalCStressMarkedOSHypotheses
    {trajectory split}
    {inputs : BetaDensity.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {Scale Volume : Set}
    {activity : Chain.SubstitutedActivitySecondVariation}
    {domain : Domain.CanonicalMetricSourceDomain Scale Volume activity}
    {representation : StressRep.CanonicalMetricStressRepresentation domain}
    (stressLane : R123.DensityAnchoredCanonicalMetricStressLane
      {trajectory = trajectory} {split = split} {inputs = inputs}
      {C = C} {S = S} {Y = Y} {group = group}
      domain representation)
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = osS}
        osInputs reconstruction group)
    : Set₂ where
  field
    sameFamilyOSRecovery :
      R128.SameFamilyOSStressRecovery stressLane

    markedStressCompletion :
      R109.LiteralSchwingerStressMarkedCompletion Y group

    markedStressIsPinnedLocalCStress :
      Top.stressTensor Y group
      ≡ LocalC.stressTensor localC

    -- Marked extension of the SAME Schwinger hierarchy.  These predicates are
    -- intentionally abstract because the repo does not yet own the distribution
    -- spaces/test-function action needed to spell OS E0--E4 internally.
    MarkedE0Regularity : Set
    MarkedE1EuclideanTensorCovariance : Set
    MarkedE2ReflectionPositivityCompatibility : Set
    MarkedE3SymmetryLocality : Set
    MarkedE4ClusterCompatibility : Set

    markedE0 :
      MarkedE0Regularity
    markedE1 :
      MarkedE1EuclideanTensorCovariance
    markedE2 :
      MarkedE2ReflectionPositivityCompatibility
    markedE3 :
      MarkedE3SymmetryLocality
    markedE4 :
      MarkedE4ClusterCompatibility

open LocalCStressMarkedOSHypotheses public

record StandardMarkedStressOSWightmanAuthority
    {trajectory split inputs C S Y group Scale Volume activity domain
     representation stressLane
     G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction
     localC}
    (hypotheses :
      LocalCStressMarkedOSHypotheses
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {C = C} {S = S} Y group
        {Scale = Scale} {Volume = Volume} {activity = activity}
        {domain = domain} {representation = representation}
        stressLane
        {G = G} {X = X} {Configuration = Configuration}
        {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {Hilbert = Hilbert} {Vector = Vector}
        {Hamiltonian = Hamiltonian} {Algebra = Algebra}
        {Root = Root} {ContinuumFamily = ContinuumFamily} {Core = Core}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division}
        {osS = osS} {osInputs = osInputs}
        {reconstruction = reconstruction}
        localC)
    : Set₂ where
  field
    reconstructMarkedStress :
      MarkedE0Regularity hypotheses →
      MarkedE1EuclideanTensorCovariance hypotheses →
      MarkedE2ReflectionPositivityCompatibility hypotheses →
      MarkedE3SymmetryLocality hypotheses →
      MarkedE4ClusterCompatibility hypotheses →
      Hinge.LocalCWightmanStressHinge
        Y group localC

open StandardMarkedStressOSWightmanAuthority public

reconstructLocalCWightmanStress :
  ∀ {trajectory split inputs C S Y group Scale Volume activity domain
      representation stressLane
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC}
    (hypotheses :
      LocalCStressMarkedOSHypotheses
        {trajectory = trajectory} {split = split} {inputs = inputs}
        {C = C} {S = S} Y group
        {Scale = Scale} {Volume = Volume} {activity = activity}
        {domain = domain} {representation = representation}
        stressLane
        {G = G} {X = X} {Configuration = Configuration}
        {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {Hilbert = Hilbert} {Vector = Vector}
        {Hamiltonian = Hamiltonian} {Algebra = Algebra}
        {Root = Root} {ContinuumFamily = ContinuumFamily} {Core = Core}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division}
        {osS = osS} {osInputs = osInputs}
        {reconstruction = reconstruction}
        localC)
    (authority :
      StandardMarkedStressOSWightmanAuthority hypotheses) →
  Hinge.LocalCWightmanStressHinge Y group localC
reconstructLocalCWightmanStress hypotheses authority =
  reconstructMarkedStress authority
    (markedE0 hypotheses)
    (markedE1 hypotheses)
    (markedE2 hypotheses)
    (markedE3 hypotheses)
    (markedE4 hypotheses)

standardMarkedStressOSWightmanAuthorityLevel : ProofLevel
standardMarkedStressOSWightmanAuthorityLevel = standardImported

sameFamilyStressMarkedOSHypothesesLevel : ProofLevel
sameFamilyStressMarkedOSHypothesesLevel = conditional

baseOSRecoveryAlreadySameFamily : Bool
baseOSRecoveryAlreadySameFamily = true

markedStressCompletionAlreadyExists : Bool
markedStressCompletionAlreadyExists = true

markedStressOSHypothesesAreTheNovelPhysicalProducer : Bool
markedStressOSHypothesesAreTheNovelPhysicalProducer = true

standardOSAuthorityDoesNotByItselfProveMarkedHypotheses : Bool
standardOSAuthorityDoesNotByItselfProveMarkedHypotheses = true
