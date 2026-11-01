module DASHI.Physics.YangMills.BalabanClayT5PhysicalTwoWeightKoteckyPreissExact where

open import Data.Rational using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PublishedTerminalCriterionReuseExact as Terminal
import DASHI.Physics.YangMills.BalabanClayT5KoteckyPreissTwoWeightPrimaryExact as KP

------------------------------------------------------------------------
-- Primary provenance.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- Roberto Fernández and Aldo Procacci,
-- "Cluster Expansion for Abstract Polymer Models. New Bounds from an Old
-- Approach", Communications in Mathematical Physics 274 (2007), 123--140.
-- DOI: 10.1007/s00220-007-0279-2; arXiv:math-ph/0605041.
--
-- This adapter connects DASHI's physical terminal rooted-shell identification
-- to the exact primary two-weight KP criterion. It does not assume that the
-- physical activity or incompatibility sum has already been identified; that
-- meaning is retained as an explicit field.
------------------------------------------------------------------------

record PhysicalTerminalTwoWeightKPPackage
    (Scale Volume Root Polymer Link Cluster FiniteVolume : Set) : Set₁ where
  field
    physicalRootedIdentification :
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale Volume Root Polymer Link

    kpData : KP.KoteckyPreissTwoWeightData
      Polymer ℚ Cluster FiniteVolume

    twoWeightMeaning :
      KP.RootedTerminalToTwoWeightKPIdentification
        (Terminal.asTerminalKPSmallness physicalRootedIdentification)
        kpData

    publishedKP : KP.PublishedKoteckyPreissTwoWeightTheorem kpData

open PhysicalTerminalTwoWeightKPPackage public

physicalTerminalTwoWeightKPCondition :
  ∀ {Scale Volume Root Polymer Link Cluster FiniteVolume} →
  (package : PhysicalTerminalTwoWeightKPPackage
    Scale Volume Root Polymer Link Cluster FiniteVolume) →
  KP.KoteckyPreissTwoWeightCondition (kpData package)
physicalTerminalTwoWeightKPCondition package =
  KP.rootedTerminalImpliesExactTwoWeightCondition
    (twoWeightMeaning package)

physicalTerminalPublishedKPConclusion :
  ∀ {Scale Volume Root Polymer Link Cluster FiniteVolume} →
  (package : PhysicalTerminalTwoWeightKPPackage
    Scale Volume Root Polymer Link Cluster FiniteVolume) →
  KP.KoteckyPreissTwoWeightConclusion (kpData package)
physicalTerminalPublishedKPConclusion package =
  KP.rootedTerminalPublishedKPConclusion
    (twoWeightMeaning package)
    (publishedKP package)

physicalTerminalTwoWeightKPAssemblyLevel : ProofLevel
physicalTerminalTwoWeightKPAssemblyLevel = machineChecked

physicalTerminalPublishedKPConclusionLevel : ProofLevel
physicalTerminalPublishedKPConclusionLevel = machineChecked

physicalTerminalTwoWeightMeaningInputsLevel : ProofLevel
physicalTerminalTwoWeightMeaningInputsLevel = conditional

physicalTerminalFernandezProcacciFallbackInputsLevel : ProofLevel
physicalTerminalFernandezProcacciFallbackInputsLevel = conditional
