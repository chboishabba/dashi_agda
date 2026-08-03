module DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicEnvelopeSchurExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (PositiveBond; first)

import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Primary
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicProjectionNormalizationExact as Dyadic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicSupportBudgetsExact as Support

------------------------------------------------------------------------
-- Explicit dyadic row/column Schur envelopes.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Issai Schur,
-- "Bemerkungen zur Theorie der beschränkten Bilinearformen mit unendlich
-- vielen Veränderlichen", Journal für die reine und angewandte Mathematik
-- 140 (1911), 1--28. No DOI recorded.
--
-- The sibling geometry proves a 128-entry row envelope and an 8-entry column
-- envelope for one four-dimensional dyadic step.  Given one uniform absolute
-- kernel-entry bound M, this module derives the literal scalar budgets
--
--   row <= 128 M,     column <= 8 M.
--
-- A physical instantiation only has to show that its actual support-restricted
-- sums are below these envelope sums and identify the selected scalar norm.
------------------------------------------------------------------------

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList function [] = []
mapList function (value ∷ values) =
  function value ∷ mapList function values

allMappedBelow :
  ∀ {A Scalar}
    (algebra : Primary.OrderedAdditiveScale Scalar)
    (function : A → Scalar) bound values →
  (∀ value → Primary.LessEqual algebra (function value) bound) →
  Primary.AllBelow algebra bound (mapList function values)
allMappedBelow algebra function bound [] pointwise = Primary.allBelowNil
allMappedBelow algebra function bound (value ∷ values) pointwise =
  Primary.allBelowCons
    (pointwise value)
    (allMappedBelow algebra function bound values pointwise)

record DyadicEnvelopeKernelData
    (coarseN : Nat) (Scalar : Set) : Set₁ where
  field
    algebra : Primary.OrderedAdditiveScale Scalar

    kernelAbsolute :
      PositiveBond (suc coarseN) →
      PositiveBond (suc (Dyadic.dyadicFineN coarseN)) → Scalar

    adjointKernelAbsolute :
      PositiveBond (suc (Dyadic.dyadicFineN coarseN)) →
      PositiveBond (suc coarseN) → Scalar

    entryBound : Scalar

    kernelEntryBelow : ∀ coarse fine →
      Primary.LessEqual algebra (kernelAbsolute coarse fine) entryBound

    adjointEntryBelow : ∀ fine coarse →
      Primary.LessEqual algebra
        (adjointKernelAbsolute fine coarse) entryBound

    stepInverseCertificate : Support.PeriodicStepInverseCertificate coarseN

open DyadicEnvelopeKernelData public

rowEnvelopeValues :
  ∀ {coarseN Scalar} →
  DyadicEnvelopeKernelData coarseN Scalar →
  PositiveBond (suc coarseN) → List Scalar
rowEnvelopeValues dataSet coarse =
  mapList (kernelAbsolute dataSet coarse)
    (Support.dyadicRowEnvelope coarse)

columnEnvelopeValues :
  ∀ {coarseN Scalar} →
  DyadicEnvelopeKernelData coarseN Scalar →
  PositiveBond (suc (Dyadic.dyadicFineN coarseN)) → List Scalar
columnEnvelopeValues dataSet fine =
  mapList
    (adjointKernelAbsolute dataSet fine)
    (Support.incidentPositiveBonds
      (Dyadic.projectDyadicSite (first fine)))

rowEnvelopeSum :
  ∀ {coarseN Scalar} →
  DyadicEnvelopeKernelData coarseN Scalar →
  PositiveBond (suc coarseN) → Scalar
rowEnvelopeSum dataSet coarse =
  Primary.finiteSum (algebra dataSet) (rowEnvelopeValues dataSet coarse)

columnEnvelopeSum :
  ∀ {coarseN Scalar} →
  DyadicEnvelopeKernelData coarseN Scalar →
  PositiveBond (suc (Dyadic.dyadicFineN coarseN)) → Scalar
columnEnvelopeSum dataSet fine =
  Primary.finiteSum (algebra dataSet) (columnEnvelopeValues dataSet fine)

rowEnvelopeBelow128Entries :
  ∀ {coarseN Scalar}
    (dataSet : DyadicEnvelopeKernelData coarseN Scalar)
    coarse →
  Primary.LessEqual (algebra dataSet)
    (rowEnvelopeSum dataSet coarse)
    (Primary.natScale (algebra dataSet)
      Dyadic.oneTwentyEight (entryBound dataSet))
rowEnvelopeBelow128Entries dataSet coarse =
  subst
    (λ count →
      Primary.LessEqual (algebra dataSet)
        (rowEnvelopeSum dataSet coarse)
        (Primary.natScale (algebra dataSet) count (entryBound dataSet)))
    (Support.dyadicRowEnvelopeLength coarse)
    (Primary.finiteSumBelowCardinalityScale
      (algebra dataSet) (entryBound dataSet)
      (allMappedBelow
        (algebra dataSet)
        (kernelAbsolute dataSet coarse)
        (entryBound dataSet)
        (Support.dyadicRowEnvelope coarse)
        (kernelEntryBelow dataSet coarse)))

columnEnvelopeBelow8Entries :
  ∀ {coarseN Scalar}
    (dataSet : DyadicEnvelopeKernelData coarseN Scalar)
    fine →
  Primary.LessEqual (algebra dataSet)
    (columnEnvelopeSum dataSet fine)
    (Primary.natScale (algebra dataSet)
      Dyadic.eight (entryBound dataSet))
columnEnvelopeBelow8Entries dataSet fine =
  subst
    (λ count →
      Primary.LessEqual (algebra dataSet)
        (columnEnvelopeSum dataSet fine)
        (Primary.natScale (algebra dataSet) count (entryBound dataSet)))
    (Support.incidentPositiveBondsLength
      (Dyadic.projectDyadicSite (first fine)))
    (Primary.finiteSumBelowCardinalityScale
      (algebra dataSet) (entryBound dataSet)
      (allMappedBelow
        (algebra dataSet)
        (adjointKernelAbsolute dataSet fine)
        (entryBound dataSet)
        (Support.incidentPositiveBonds
          (Dyadic.projectDyadicSite (first fine)))
        (adjointEntryBelow dataSet fine)))

record PhysicalDyadicEnvelopeDomination
    (coarseN : Nat) (Scalar : Set) : Set₁ where
  field
    envelope : DyadicEnvelopeKernelData coarseN Scalar

    physicalRowSum : PositiveBond (suc coarseN) → Scalar
    physicalColumnSum :
      PositiveBond (suc (Dyadic.dyadicFineN coarseN)) → Scalar

    physicalRowBelowEnvelope : ∀ coarse →
      Primary.LessEqual (algebra envelope)
        (physicalRowSum coarse) (rowEnvelopeSum envelope coarse)

    physicalColumnBelowEnvelope : ∀ fine →
      Primary.LessEqual (algebra envelope)
        (physicalColumnSum fine) (columnEnvelopeSum envelope fine)

open PhysicalDyadicEnvelopeDomination public

physicalRowBelow128Entries :
  ∀ {coarseN Scalar}
    (dataSet : PhysicalDyadicEnvelopeDomination coarseN Scalar)
    coarse →
  Primary.LessEqual (algebra (envelope dataSet))
    (physicalRowSum dataSet coarse)
    (Primary.natScale (algebra (envelope dataSet))
      Dyadic.oneTwentyEight (entryBound (envelope dataSet)))
physicalRowBelow128Entries dataSet coarse =
  Primary.transitive (algebra (envelope dataSet))
    (physicalRowBelowEnvelope dataSet coarse)
    (rowEnvelopeBelow128Entries (envelope dataSet) coarse)

physicalColumnBelow8Entries :
  ∀ {coarseN Scalar}
    (dataSet : PhysicalDyadicEnvelopeDomination coarseN Scalar)
    fine →
  Primary.LessEqual (algebra (envelope dataSet))
    (physicalColumnSum dataSet fine)
    (Primary.natScale (algebra (envelope dataSet))
      Dyadic.eight (entryBound (envelope dataSet)))
physicalColumnBelow8Entries dataSet fine =
  Primary.transitive (algebra (envelope dataSet))
    (physicalColumnBelowEnvelope dataSet fine)
    (columnEnvelopeBelow8Entries (envelope dataSet) fine)

cmp109DyadicRow128EntryBudgetLevel : ProofLevel
cmp109DyadicRow128EntryBudgetLevel = machineChecked

cmp109DyadicColumn8EntryBudgetLevel : ProofLevel
cmp109DyadicColumn8EntryBudgetLevel = machineChecked

physicalDyadicEnvelopeDominationInputsLevel : ProofLevel
physicalDyadicEnvelopeDominationInputsLevel = conditional

physicalDyadicEntryNormBoundInputsLevel : ProofLevel
physicalDyadicEntryNormBoundInputsLevel = conditional
