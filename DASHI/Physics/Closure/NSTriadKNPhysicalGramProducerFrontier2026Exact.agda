module DASHI.Physics.Closure.NSTriadKNPhysicalGramProducerFrontier2026Exact where

------------------------------------------------------------------------
-- 2026 NS PHYSICAL GRAM PRODUCER FRONTIER
--
-- Source calibration / related literature:
--   Fabian Waleffe, "The nature of triad interactions in homogeneous
--   turbulence", Physics of Fluids A 4 (1992), 350--363.
--   DOI: 10.1063/1.858309.
--
--   Mischa Cotlar; Elias M. Stein,
--   "A unified theory of Hilbert transforms and ergodic theorems" (1955).
--   No DOI is known for the cited conference article.
--
--   RequestProject/NavierStokes/AlmostOrthogonalGramSchur.lean
--   (Lean sibling module supplied in the 2026-09-06 handoff archive).
--
-- The DataSchur/OperatorSchur definitions now live in the authoritative R30
-- owner. This module supplies only alternative physical producer interfaces.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNCutoffUniformCotlarSteinRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNPhysicalHeterochiralMinorityWaleffeWeldRound134Exact as R134
import DASHI.Physics.Closure.NSTriadKNCriticalConeRelativeCovarianceTargetRound284Exact as R284

record FixedOutputGramSurface (Mode : Set) : Set where
  field
    modes : List Mode
    absoluteRealGram : Mode → Mode → ℚ
    size : Mode → ℚ
    gramNonnegative : ∀ p q → 0ℚ ≤ absoluteRealGram p q
    sizeNonnegative : ∀ p → 0ℚ ≤ size p

open FixedOutputGramSurface public

record AngularSchurProducer
    {Mode : Set}
    (S : FixedOutputGramSurface Mode)
    (A : ℚ) : Set where
  field
    angularEnvelope : Mode → Mode → ℚ
    angularEnvelopeNonnegative : ∀ p q → 0ℚ ≤ angularEnvelope p q
    angularEnvelopeSymmetric : ∀ p q →
      angularEnvelope p q ≡ angularEnvelope q p
    angularGramDecay : ∀ p q →
      absoluteRealGram S p q
      ≤ angularEnvelope p q * (size S p * size S q)
    angularRowSummable : ∀ p →
      R30.sumRational (modes S) (angularEnvelope p) ≤ A

open AngularSchurProducer public

angularProducerToDataSchur :
  ∀ {Mode : Set}
    {S : FixedOutputGramSurface Mode}
    {A : ℚ} →
  AngularSchurProducer S A →
  R30.DataSchur (modes S) (absoluteRealGram S) (size S) A
angularProducerToDataSchur P = record
  { dataKernel = angularEnvelope P
  ; dataKernelNonnegative = angularEnvelopeNonnegative P
  ; dataKernelSymmetric = angularEnvelopeSymmetric P
  ; dataPairwiseDomination = angularGramDecay P
  ; dataRowMassBound = angularRowSummable P
  }

data Helicity : Set where
  plus : Helicity
  minus : Helicity

record HelicitySchurProducer
    {Mode : Set}
    (S : FixedOutputGramSurface Mode)
    (A : ℚ) : Set where
  field
    channelEnvelope : Helicity → Helicity → Mode → Mode → ℚ
    aggregateEnvelope : Mode → Mode → ℚ
    aggregateEnvelopeNonnegative : ∀ p q → 0ℚ ≤ aggregateEnvelope p q
    aggregateEnvelopeSymmetric : ∀ p q →
      aggregateEnvelope p q ≡ aggregateEnvelope q p
    helicalRecombinationDomination : ∀ p q →
      absoluteRealGram S p q
      ≤ aggregateEnvelope p q * (size S p * size S q)
    helicalRowSummable : ∀ p →
      R30.sumRational (modes S) (aggregateEnvelope p) ≤ A

open HelicitySchurProducer public

helicityProducerToDataSchur :
  ∀ {Mode : Set}
    {S : FixedOutputGramSurface Mode}
    {A : ℚ} →
  HelicitySchurProducer S A →
  R30.DataSchur (modes S) (absoluteRealGram S) (size S) A
helicityProducerToDataSchur P = record
  { dataKernel = aggregateEnvelope P
  ; dataKernelNonnegative = aggregateEnvelopeNonnegative P
  ; dataKernelSymmetric = aggregateEnvelopeSymmetric P
  ; dataPairwiseDomination = helicalRecombinationDomination P
  ; dataRowMassBound = helicalRowSummable P
  }

record PhaseOperatorSchurProducer
    {Mode : Set}
    (S : FixedOutputGramSurface Mode)
    (operatorCoherence : Mode → Mode → ℚ)
    (A : ℚ) : Set where
  field
    structuralOperatorSchur :
      R30.OperatorSchur (modes S) operatorCoherence A
    sameObjectRealization :
      R30.OperatorToDataRealization
        {absoluteRealGram = absoluteRealGram S}
        {size = size S}
        structuralOperatorSchur

open PhaseOperatorSchurProducer public

phaseOperatorProducerToDataSchur :
  ∀ {Mode : Set}
    {S : FixedOutputGramSurface Mode}
    {operatorCoherence : Mode → Mode → ℚ}
    {A : ℚ} →
  PhaseOperatorSchurProducer S operatorCoherence A →
  R30.DataSchur (modes S) (absoluteRealGram S) (size S) A
phaseOperatorProducerToDataSchur P =
  R30.operatorSchurImpliesDataSchur
    (structuralOperatorSchur P)
    (sameObjectRealization P)

data ProgrammeOwner : Set where
  abstractCotlarStein
  leanFiniteSchurCompiler
  localizationNoGo
  physicalCriticalConeProducer
  physicalWaleffeHelicity

round29And30Owner : ProgrammeOwner
round29And30Owner = abstractCotlarStein

leanAlmostOrthogonalOwner : ProgrammeOwner
leanAlmostOrthogonalOwner = leanFiniteSchurCompiler

round203And214Owner : ProgrammeOwner
round203And214Owner = localizationNoGo

round284Owner : ProgrammeOwner
round284Owner = physicalCriticalConeProducer

round134Owner : ProgrammeOwner
round134Owner = physicalWaleffeHelicity

angularProducerCompilerClosed : Bool
angularProducerCompilerClosed = true

helicityProducerCompilerClosed : Bool
helicityProducerCompilerClosed = true

phaseOperatorProducerCompilerClosed : Bool
phaseOperatorProducerCompilerClosed = true

physicalAngularUniformSchurClosed : Bool
physicalAngularUniformSchurClosed = false

physicalHelicityUniformSchurClosed : Bool
physicalHelicityUniformSchurClosed = false

physicalPhaseOperatorUniformSchurClosed : Bool
physicalPhaseOperatorUniformSchurClosed = false

physicalCriticalConeGramOperatorUniformlyBounded : Bool
physicalCriticalConeGramOperatorUniformlyBounded = false

packageAClosedFromTheseProducers : Bool
packageAClosedFromTheseProducers = false

clayPromotion : Bool
clayPromotion = false

angularProducerCompilerClosedIsTrue : angularProducerCompilerClosed ≡ true
angularProducerCompilerClosedIsTrue = refl

physicalAngularUniformSchurClosedIsFalse :
  physicalAngularUniformSchurClosed ≡ false
physicalAngularUniformSchurClosedIsFalse = refl

physicalHelicityUniformSchurClosedIsFalse :
  physicalHelicityUniformSchurClosed ≡ false
physicalHelicityUniformSchurClosedIsFalse = refl

physicalPhaseOperatorUniformSchurClosedIsFalse :
  physicalPhaseOperatorUniformSchurClosed ≡ false
physicalPhaseOperatorUniformSchurClosedIsFalse = refl

physicalCriticalConeGramOperatorUniformlyBoundedIsFalse :
  physicalCriticalConeGramOperatorUniformlyBounded ≡ false
physicalCriticalConeGramOperatorUniformlyBoundedIsFalse = refl
