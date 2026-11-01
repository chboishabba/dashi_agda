{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119Round109ToCommonCoreExact where

------------------------------------------------------------------------
-- C / ROUND109 COMPLETED STRESS -> PINNED COMMON-CORE STRESS
--
-- Keep the carrier boundary honest:
--
--   Round109 completed marked stress
--       = literal Clay stress tensor
--       = stress selected by the pinned common-core Ward datum.
--
-- Once this equality is supplied, the existing common-core compiler already
-- proves that the charge of that SAME selected stress equals the reconstructed
-- CMP119 OS Hamiltonian.  No second continuum stress or generator is chosen.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact as StressMarked
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119StressCommonCoreExact as Common
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as OSR
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

record Round109PinnedCommonCoreWeld
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {Configuration Position CurvaturePolynomial LocalOperator OPECoefficient
     Hilbert Vector Hamiltonian Algebra Core : Set}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {limitLaws : RealLimit.CanonicalRealLimitLaws sequenceLimit}
    {quotient :
      Quotient.RealQuotientConvergenceAuthority
        (RealLimit.Converges sequenceLimit)}
    {division :
      Division.RealDivisionAlgebra
        (RealLimit.canonicalCylinderAlgebra limitLaws)
        quotient}
    {osS}
    {osInputs :
      OSSystem.PinnedCMP119OSAxiomInputs
        (Top.CompactSimpleGroup C) (Top.Spacetime C)
        Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Hamiltonian Vector
        {sequenceLimit = sequenceLimit}
        limitLaws quotient division osS}
    (reconstruction :
      OSR.PinnedCMP119OSReconstruction
        (Top.CompactSimpleGroup C) (Top.Spacetime C)
        Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = osS} osInputs)
    : Set₂ where
  field
    completion : R109.LiteralSchwingerStressMarkedCompletion Y group

    commonCore :
      Common.PinnedStressCommonCoreData
        (Top.CompactSimpleGroup C) (Top.Spacetime C)
        Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {S = osS} {osInputs = osInputs} reconstruction group

    literalStressIsPinnedCommonCoreStress :
      Top.stressTensor Y group ≡ Common.stressTensor commonCore

open Round109PinnedCommonCoreWeld public

completedMarkedStressEqualsPinnedCommonCoreStress :
  ∀ {C S Y group Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (weld :
      Round109PinnedCommonCoreWeld
        {C = C} {S = S} Y group
        {Configuration = Configuration} {Position = Position}
        {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {Hilbert = Hilbert} {Vector = Vector}
        {Hamiltonian = Hamiltonian} {Algebra = Algebra} {Core = Core}
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {osS = osS} {osInputs = osInputs} reconstruction) →
  Marked.continuumComposite
    (StressMarked.stressField
      (StressMarked.sameCompletedMarkedSourcesGiveCompositeAndStressFields
        (R109.completedSources (completion weld))))
  ≡ Common.stressTensor (commonCore weld)
completedMarkedStressEqualsPinnedCommonCoreStress weld =
  trans
    (R109.literalStressIsCompletedMarkedStress (completion weld))
    (literalStressIsPinnedCommonCoreStress weld)

pinnedCommonCoreStressChargeEqualsOSHamiltonian :
  ∀ {C S Y group Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (weld :
      Round109PinnedCommonCoreWeld
        {C = C} {S = S} Y group
        {Configuration = Configuration} {Position = Position}
        {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {Hilbert = Hilbert} {Vector = Vector}
        {Hamiltonian = Hamiltonian} {Algebra = Algebra} {Core = Core}
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws} {quotient = quotient} {division = division}
        {osS = osS} {osInputs = osInputs} reconstruction) →
  Common.stressCharge (commonCore weld)
    (Common.stressTensor (commonCore weld))
  ≡ OSR.reconstructedHamiltonian reconstruction group
pinnedCommonCoreStressChargeEqualsOSHamiltonian weld =
  Common.stressChargeEqualsPinnedOSHamiltonian (commonCore weld)

round109ToPinnedCommonCoreSameStressCompilerLevel : ProofLevel
round109ToPinnedCommonCoreSameStressCompilerLevel = machineChecked

round109PinnedCommonCoreGeneratorCompilerLevel : ProofLevel
round109PinnedCommonCoreGeneratorCompilerLevel = machineChecked

-- Remaining physical seam: instantiate the Round109 completion and the pinned
-- Ward/common-core datum on the same literal stress tensor.  R144 -> Round109
-- insertion identity remains a separate source-coordinate theorem.
literalRound109PinnedCommonCoreStressIdentificationLevel : ProofLevel
literalRound109PinnedCommonCoreStressIdentificationLevel = conditional
