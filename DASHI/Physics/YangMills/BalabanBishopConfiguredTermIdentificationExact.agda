module DASHI.Physics.YangMills.BalabanBishopConfiguredTermIdentificationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, April 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- Code continuation: Viktor Csimma, viktorcsimma/bishop, pinned by DASHI at
-- vendor/bishop commit 240e38c7f6938f20f865b1f956c5f084da48bd54.
--
-- PURPOSE
-- Reduce the remaining elementary-series seam to literal term definitions.
-- If the configured sine and cosine term functions are propositionally equal
-- to the concrete signed factorial terms, the setoid identification required
-- by all parity/interlacing consumers follows without a new analytic proof.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Concrete
open import DASHI.Physics.YangMills.CompactLieProofLevel

record ConfiguredConcreteTermDefinitions
    (dataSet : Elementary.BishopElementaryPowerSeriesData) : Set₁ where
  field
    sineTermDefinition : ∀ point index →
      Elementary.sineTerm dataSet point index
      ≡ Concrete.sineSignedTerm point index

    cosineTermDefinition : ∀ point index →
      Elementary.cosineTerm dataSet point index
      ≡ Concrete.cosineSignedTerm point index

open ConfiguredConcreteTermDefinitions public

configuredConcreteTermIdentification :
  ∀ {dataSet} →
  ConfiguredConcreteTermDefinitions dataSet →
  Concrete.ConcreteSineCosineTermIdentification dataSet
configuredConcreteTermIdentification definitions = record
  { sineTermIsConcrete = λ point index →
      rewrite sineTermDefinition definitions point index =
        BishopProperties.≃-refl
  ; cosineTermIsConcrete = λ point index →
      rewrite cosineTermDefinition definitions point index =
        BishopProperties.≃-refl
  }

configuredTermDefinitionReducerLevel : ProofLevel
configuredTermDefinitionReducerLevel = machineChecked

configuredSineCosineDefinitionsLevel : ProofLevel
configuredSineCosineDefinitionsLevel = conditional

configuredTermIdentificationFromDefinitionsLevel : ProofLevel
configuredTermIdentificationFromDefinitionsLevel = machineChecked
