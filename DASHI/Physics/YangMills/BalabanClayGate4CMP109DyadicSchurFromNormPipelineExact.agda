module DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicSchurFromNormPipelineExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (PositiveBond)

import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Primary
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicProjectionNormalizationExact as Dyadic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicSupportBudgetsExact as Support
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicEnvelopeSchurExact as Schur
import DASHI.Physics.YangMills.BalabanClayGate4OperatorNormPipelineExact as Pipeline

------------------------------------------------------------------------
-- From component norm bounds to the exact 128-by-8 Schur envelope.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Issai Schur,
-- "Bemerkungen zur Theorie der beschränkten Bilinearformen mit unendlich
-- vielen Veränderlichen", Journal für die reine und angewandte Mathematik
-- 140 (1911), 1--28. No DOI recorded.
--
-- Every physical kernel entry and adjoint entry may have its own four-stage
-- derivative pipeline, but all pipelines are compared with one scalar bound M.
-- This module transports those norm estimates into the scalar order used by the
-- exact dyadic support envelope.  The existing finite theorem then yields
--
--   row <= 128 M,    column <= 8 M.
--
-- Hence the Schur frontier consists only of the four component estimates and
-- their norm-convention equalities, not a separate global kernel estimate.
------------------------------------------------------------------------

FineBond : Nat → Set
FineBond coarseN = PositiveBond (suc (Dyadic.dyadicFineN coarseN))

CoarseBond : Nat → Set
CoarseBond coarseN = PositiveBond (suc coarseN)

record DyadicPipelineSchurInputs
    (coarseN : Nat)
    (Operator Bound : Set) : Set₁ where
  field
    scalarAlgebra : Primary.OrderedAdditiveScale Bound

    kernelPipeline :
      CoarseBond coarseN → FineBond coarseN →
      Pipeline.CMP109DerivativeEntryPipeline Operator Bound

    adjointPipeline :
      FineBond coarseN → CoarseBond coarseN →
      Pipeline.CMP109DerivativeEntryPipeline Operator Bound

    kernelAbsolute : CoarseBond coarseN → FineBond coarseN → Bound
    adjointKernelAbsolute :
      FineBond coarseN → CoarseBond coarseN → Bound

    globalEntryBound : Bound

    kernelAbsoluteMeaning : ∀ coarse fine →
      kernelAbsolute coarse fine
      ≡ Pipeline.operatorNorm
          (Pipeline.algebra (kernelPipeline coarse fine))
          (Pipeline.assembledDerivativeEntryOperator
            (kernelPipeline coarse fine))

    adjointKernelAbsoluteMeaning : ∀ fine coarse →
      adjointKernelAbsolute fine coarse
      ≡ Pipeline.operatorNorm
          (Pipeline.algebra (adjointPipeline fine coarse))
          (Pipeline.assembledDerivativeEntryOperator
            (adjointPipeline fine coarse))

    kernelEntryBoundMeaning : ∀ coarse fine →
      Pipeline.entryBound (kernelPipeline coarse fine)
      ≡ globalEntryBound

    adjointEntryBoundMeaning : ∀ fine coarse →
      Pipeline.entryBound (adjointPipeline fine coarse)
      ≡ globalEntryBound

    kernelOrderMeaning : ∀ coarse fine →
      Pipeline.LessEqual
        (Pipeline.algebra (kernelPipeline coarse fine))
      ≡ Primary.LessEqual scalarAlgebra

    adjointOrderMeaning : ∀ fine coarse →
      Pipeline.LessEqual
        (Pipeline.algebra (adjointPipeline fine coarse))
      ≡ Primary.LessEqual scalarAlgebra

    stepInverseCertificate : Support.PeriodicStepInverseCertificate coarseN

open DyadicPipelineSchurInputs public

kernelEntryBelowGlobalBound :
  ∀ {coarseN Operator Bound}
    (inputs : DyadicPipelineSchurInputs coarseN Operator Bound)
    coarse fine →
  Primary.LessEqual (scalarAlgebra inputs)
    (kernelAbsolute inputs coarse fine)
    (globalEntryBound inputs)
kernelEntryBelowGlobalBound inputs coarse fine =
  subst
    (λ relation → relation
      (kernelAbsolute inputs coarse fine)
      (globalEntryBound inputs))
    (kernelOrderMeaning inputs coarse fine)
    (subst
      (λ lower →
        Pipeline.LessEqual
          (Pipeline.algebra (kernelPipeline inputs coarse fine))
          lower (globalEntryBound inputs))
      (sym (kernelAbsoluteMeaning inputs coarse fine))
      (subst
        (λ upper →
          Pipeline.LessEqual
            (Pipeline.algebra (kernelPipeline inputs coarse fine))
            (Pipeline.operatorNorm
              (Pipeline.algebra (kernelPipeline inputs coarse fine))
              (Pipeline.assembledDerivativeEntryOperator
                (kernelPipeline inputs coarse fine)))
            upper)
        (kernelEntryBoundMeaning inputs coarse fine)
        (Pipeline.assembledDerivativeEntryNormBound
          (kernelPipeline inputs coarse fine))))

adjointEntryBelowGlobalBound :
  ∀ {coarseN Operator Bound}
    (inputs : DyadicPipelineSchurInputs coarseN Operator Bound)
    fine coarse →
  Primary.LessEqual (scalarAlgebra inputs)
    (adjointKernelAbsolute inputs fine coarse)
    (globalEntryBound inputs)
adjointEntryBelowGlobalBound inputs fine coarse =
  subst
    (λ relation → relation
      (adjointKernelAbsolute inputs fine coarse)
      (globalEntryBound inputs))
    (adjointOrderMeaning inputs fine coarse)
    (subst
      (λ lower →
        Pipeline.LessEqual
          (Pipeline.algebra (adjointPipeline inputs fine coarse))
          lower (globalEntryBound inputs))
      (sym (adjointKernelAbsoluteMeaning inputs fine coarse))
      (subst
        (λ upper →
          Pipeline.LessEqual
            (Pipeline.algebra (adjointPipeline inputs fine coarse))
            (Pipeline.operatorNorm
              (Pipeline.algebra (adjointPipeline inputs fine coarse))
              (Pipeline.assembledDerivativeEntryOperator
                (adjointPipeline inputs fine coarse)))
            upper)
        (adjointEntryBoundMeaning inputs fine coarse)
        (Pipeline.assembledDerivativeEntryNormBound
          (adjointPipeline inputs fine coarse))))

asDyadicEnvelopeKernelData :
  ∀ {coarseN Operator Bound} →
  DyadicPipelineSchurInputs coarseN Operator Bound →
  Schur.DyadicEnvelopeKernelData coarseN Bound
asDyadicEnvelopeKernelData inputs = record
  { algebra = scalarAlgebra inputs
  ; kernelAbsolute = kernelAbsolute inputs
  ; adjointKernelAbsolute =
      adjointKernelAbsolute inputs
  ; entryBound = globalEntryBound inputs
  ; kernelEntryBelow =
      kernelEntryBelowGlobalBound inputs
  ; adjointEntryBelow =
      adjointEntryBelowGlobalBound inputs
  ; stepInverseCertificate =
      stepInverseCertificate inputs
  }

pipelineRowEnvelopeBelow128Entries :
  ∀ {coarseN Operator Bound}
    (inputs : DyadicPipelineSchurInputs coarseN Operator Bound)
    coarse →
  Primary.LessEqual (scalarAlgebra inputs)
    (Schur.rowEnvelopeSum (asDyadicEnvelopeKernelData inputs) coarse)
    (Primary.natScale (scalarAlgebra inputs)
      Dyadic.oneTwentyEight (globalEntryBound inputs))
pipelineRowEnvelopeBelow128Entries inputs =
  Schur.rowEnvelopeBelow128Entries (asDyadicEnvelopeKernelData inputs)

pipelineColumnEnvelopeBelow8Entries :
  ∀ {coarseN Operator Bound}
    (inputs : DyadicPipelineSchurInputs coarseN Operator Bound)
    fine →
  Primary.LessEqual (scalarAlgebra inputs)
    (Schur.columnEnvelopeSum (asDyadicEnvelopeKernelData inputs) fine)
    (Primary.natScale (scalarAlgebra inputs)
      Dyadic.eight (globalEntryBound inputs))
pipelineColumnEnvelopeBelow8Entries inputs =
  Schur.columnEnvelopeBelow8Entries (asDyadicEnvelopeKernelData inputs)

cmp109PipelineToEntryBoundLevel : ProofLevel
cmp109PipelineToEntryBoundLevel = machineChecked

cmp109PipelineToDyadicEnvelopeLevel : ProofLevel
cmp109PipelineToDyadicEnvelopeLevel = machineChecked

cmp109PipelineRow128BudgetLevel : ProofLevel
cmp109PipelineRow128BudgetLevel = machineChecked

cmp109PipelineColumn8BudgetLevel : ProofLevel
cmp109PipelineColumn8BudgetLevel = machineChecked

physicalCMP109KernelNormConventionInputsLevel : ProofLevel
physicalCMP109KernelNormConventionInputsLevel = conditional

physicalCMP109AdjointPipelineInputsLevel : ProofLevel
physicalCMP109AdjointPipelineInputsLevel = conditional
