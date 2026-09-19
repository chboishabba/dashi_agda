module DASHI.Physics.YangMills.BalabanClayGate4ConditionalMixtureReopeningExact where

------------------------------------------------------------------------
-- GATE4 COARSE SLOW-FIELD LAW + CONSTRAINED REFERENCE KERNEL
--   -> CANONICAL FINITE RG REOPENING
--
-- The Gate4 reference normalization is interpreted in its natural direction:
-- as a conditional fast-field law at fixed slow field.
--
-- A finite slow-field probability law supplies the coarse marginal.  The fine
-- law is then defined by the exact mixture
--
--   mu_fine(x) = sum_slow mu_coarse(slow) kappa(slow,x).
--
-- Finite rational Fubini proves normalization, while disintegration is
-- definitional.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact as Kernel
import DASHI.Physics.YangMills.BalabanFiniteConditionalMixtureReopeningExact as Mixture
import DASHI.Physics.YangMills.BalabanFiniteRGObservableReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanFiniteRGProbabilityExpectationSemanticsExact as Probability

record Gate4SlowFieldProbabilityLaw
    {Scale Fine SlowField Component Functional : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction})
    (typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs) : Set₁ where
  field
    scale : Scale
    component : Component

    slowStates : List SlowField
    slowWeight : SlowField → ℚ

    slowWeightNonnegative : ∀ slow →
      0ℚ ≤ slowWeight slow

    slowWeightNormalized :
      DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact.sumRational
        slowStates slowWeight
      ≡ 1ℚ

open Gate4SlowFieldProbabilityLaw public

asFiniteConditionalMixture :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs} →
  Gate4SlowFieldProbabilityLaw referenceInputs typed →
  Mixture.FiniteConditionalMixtureData Fine SlowField
asFiniteConditionalMixture
  {construction = construction}
  {referenceInputs = referenceInputs}
  {typed = typed}
  coarse = record
  { fineStates =
      T.fastFibre
        (PhysicalT.canonicalPhysicalTData construction)
        (scale coarse) (component coarse)
  ; coarseStates = slowStates coarse
  ; project =
      Integral.blockMap
        (T.sumData (PhysicalT.canonicalPhysicalTData construction))
  ; coarseWeight = slowWeight coarse
  ; coarseWeightNonnegative = slowWeightNonnegative coarse
  ; coarseWeightNormalized = slowWeightNormalized coarse
  ; kernel =
      Kernel.constrainedReferenceKernel
        referenceInputs (scale coarse) (component coarse)
  ; kernelNonnegative =
      Kernel.constrainedReferenceKernelNonnegative
        typed (scale coarse) (component coarse)
  ; kernelNormalized =
      Kernel.constrainedReferenceKernelNormalized
        typed (scale coarse) (component coarse)
  ; FibreSupport = λ slow fine →
      Integral.blockMap
        (T.sumData (PhysicalT.canonicalPhysicalTData construction))
        fine
      ≡ slow
  ; fibreSupportProjects = λ support → support
  ; kernelOffFibreZero =
      Kernel.constrainedReferenceKernelOffFibreZero
        referenceInputs (scale coarse) (component coarse)
  }

gate4ConditionalMixtureReopeningStep :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs} →
  Gate4SlowFieldProbabilityLaw referenceInputs typed →
  Reopen.FiniteRGReopeningStep Fine SlowField
gate4ConditionalMixtureReopeningStep coarse =
  Mixture.compileConditionalMixtureReopeningStep
    (asFiniteConditionalMixture coarse)

gate4ConditionalMixtureFineProbabilityLaw :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    {typed :
      Kernel.TypedReferenceCoarseConstraint referenceInputs}
    (coarse :
      Gate4SlowFieldProbabilityLaw referenceInputs typed) →
  Probability.FiniteRGProbabilityLaw
    (gate4ConditionalMixtureReopeningStep coarse)
gate4ConditionalMixtureFineProbabilityLaw coarse =
  Mixture.compileConditionalMixtureFineProbabilityLaw
    (asFiniteConditionalMixture coarse)

gate4ConditionalMixtureReopeningCompilerLevel : ProofLevel
gate4ConditionalMixtureReopeningCompilerLevel = machineChecked

gate4ConditionalMixtureFineProbabilityCompilerLevel : ProofLevel
gate4ConditionalMixtureFineProbabilityCompilerLevel = machineChecked

-- Remaining source-facing finite probability payment:
-- identify the actual selected complete-density slow-field law and prove that it
-- is nonnegative/normalized on the finite slow-field carrier.
physicalSlowFieldProbabilityLawLevel : ProofLevel
physicalSlowFieldProbabilityLawLevel = conditional
