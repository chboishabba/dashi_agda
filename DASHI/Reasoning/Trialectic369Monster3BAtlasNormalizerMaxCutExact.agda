module DASHI.Reasoning.Trialectic369Monster3BAtlasNormalizerMaxCutExact where

------------------------------------------------------------------------
-- MONSTER 3B NORMALIZER / HEISENBERG REALIZATION CURRENT MAX-CUT
--
-- The former source-data wall has been narrowed materially.
--
-- PAID BY EXTERNAL CERTIFIED SOURCE RECEIPTS:
--
-- * ATLAS publishes an absolutely irreducible 12-dimensional GF(3) module for
--   2.Suz:2;
-- * Breuer--Magaard--Wilson Appendix 9.2 uses the ATLAS 38-dimensional GF(3)
--   representation of `3^(1+12):6.Suz.2` and explicitly states that the
--   12-dimensional 2.Suz.2 module preserves a symplectic form and embeds in
--   Sp(12,3), the automorphism group of the extraspecial `3_+^(1+12)`;
-- * the exact 38-dimensional generator filenames are known.
--
-- PAID IN-REPO:
--
-- * the standard repository quotient carrier `X6 + X6*` and alternating form;
-- * the exact Heisenberg central extension and its translation/modulation axes;
-- * the typed source-to-repository symplectic action interface;
-- * the necessary central-cocycle correction condition for lifting a
--   symplectic quotient action to the repository's asymmetric Heisenberg
--   cocycle;
-- * the downstream normalizer-translation descent compiler.
--
-- EXACT REMAINING RECEIPTS:
--
-- 1. import the published 12x12 GF(3) generator entries;
-- 2. compute the alternating form they preserve;
-- 3. compute a symplectic change of basis to the repository standard
--    `X6 + X6*` form;
-- 4. compute the central correction for the chosen Heisenberg cocycle;
-- 5. instantiate the already-owned output-translation equivariance compiler.
--
-- Thus the remaining wall is now concrete matrix acquisition/intertwining, not
-- existence of a Monster-normalizer module or an unspecified action hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.Monster3BAtlasSymplectic12SourceReceiptExact as Source
import DASHI.Moonshine.Monster3BAtlasSymplecticBasisIntertwinerCompilerExact as Weld
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Reasoning.Trialectic369MultiplicityNormalizerTranslationDescentExact as Descent

record Monster3BAtlasNormalizerBoundary : Set where
  constructor monster-3b-atlas-normalizer-boundary
  field
    certifiedDirectTwelveModuleLocated : Bool
    certifiedMonsterNormalizerRepresentationLocated : Bool
    sourceSymplecticActionExists : Bool
    sourceSp12ExtraspecialInterpretationPaid : Bool
    repositoryHeisenbergCarrierPaid : Bool
    symplecticBasisIntertwinerInterfacePaid : Bool
    centralCorrectionConditionExposed : Bool
    acquisitionScriptInstalled : Bool
    rawAtlasMatricesImported : Bool
    concreteAlternatingFormComputed : Bool
    concreteSymplecticBasisChangePaid : Bool
    concreteHeisenbergCentralCorrectionPaid : Bool
    actualMonsterOutputTranslationEquivariancePaid : Bool
    physicalNormalizerRealizationPaid : Bool
    terminalNote : String
open Monster3BAtlasNormalizerBoundary public

canonicalMonster3BAtlasNormalizerBoundary : Monster3BAtlasNormalizerBoundary
canonicalMonster3BAtlasNormalizerBoundary =
  monster-3b-atlas-normalizer-boundary
    Source.canonicalBoundary.certifiedDirectTwelveModuleLocated
    Source.canonicalBoundary.certifiedAtlasNormalizerRepresentationLocated
    Source.canonicalBoundary.sourceSymplectic12ActionExists
    Source.canonicalBoundary.sourceExplainsActionOnExtraspecialQuotient
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false
    "ATLAS/CTblLib source existence is paid: direct 12-dimensional GF(3) 2.Suz:2 module plus the Monster 3B semidirect-product realization. Remaining work is import of actual matrix entries, exact symplectic basis normalization into X6+X6*, the cocycle phase correction, and instantiation of the existing normalizer-translation descent compiler."
