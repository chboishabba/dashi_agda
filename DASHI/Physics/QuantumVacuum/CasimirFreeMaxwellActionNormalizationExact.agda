module DASHI.Physics.QuantumVacuum.CasimirFreeMaxwellActionNormalizationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Kernel
import DASHI.Promotion.StandardModelGaugeCouplingAuthorityFrontier as CouplingAuthority

------------------------------------------------------------------------
-- FREE MAXWELL / CARTAN-YM NORMALIZATION BOUNDARY
--
-- The ideal parallel-plate kernel owned by CasimirParallelPlateKernel is written
-- only in terms of pi, hbar, c and plate separation.  It has no measured
-- alpha_EM / electric-charge coordinate.  Conversely, identifying a Cartan
-- restriction of one Yang-Mills action with the canonical Maxwell action does
-- require the SAME field normalization, generator/pairing convention and action
-- prefactor on both sides.
--
-- These are different payments.  The latter is a convention/same-object action
-- normalization.  A CODATA/PDG charge or alpha payload is empirical
-- phenomenology/matter-coupling calibration and is not manufactured here.
------------------------------------------------------------------------

record FreeMaxwellActionNormalization : Set₁ where
  field
    SamePhysicalFieldNormalization : Set
    samePhysicalFieldNormalization : SamePhysicalFieldNormalization

    SameGeneratorPairingNormalization : Set
    sameGeneratorPairingNormalization : SameGeneratorPairingNormalization

    actionPrefactor : ℝ

    normalizationReading : String

open FreeMaxwellActionNormalization public

casimirKernelOwner : String
casimirKernelOwner =
  "DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel"

standardModelCouplingAuthorityOwner : String
standardModelCouplingAuthorityOwner =
  "DASHI.Promotion.StandardModelGaugeCouplingAuthorityFrontier"

-- Keep the imports live as provenance anchors without pretending the metadata
-- frontier supplies a promoted numeric coupling.
casimirKernelSurface : Set₁
casimirKernelSurface = Kernel.CasimirScalarModel

couplingAuthoritySymbolSurface : Set
couplingAuthoritySymbolSurface = CouplingAuthority.GaugeCouplingSymbol

data NumericAlphaAutomaticallyFixesCartanYMMaxwellNormalization : Set where

numericAlphaDoesNotFixCartanYMMaxwellNormalization :
  NumericAlphaAutomaticallyFixesCartanYMMaxwellNormalization → ⊥
numericAlphaDoesNotFixCartanYMMaxwellNormalization ()

record CasimirFreeMaxwellNormalizationBoundary : Set where
  constructor casimir-free-maxwell-normalization-boundary
  field
    idealParallelPlateKernelRequiresMeasuredAlphaEM : Bool
    sameFieldAndGeneratorNormalizationRequiredForYMMaxwellWeld : Bool
    empiricalChargeCouplingCalibrationIsSeparatePhenomenology : Bool
    standardModelNumericAuthorityCurrentlyPromotedForCasimir : Bool

open CasimirFreeMaxwellNormalizationBoundary public

canonicalFreeMaxwellNormalizationBoundary :
  CasimirFreeMaxwellNormalizationBoundary
canonicalFreeMaxwellNormalizationBoundary =
  casimir-free-maxwell-normalization-boundary false true true false

casimirFreeMaxwellNormalizationReading : String
casimirFreeMaxwellNormalizationReading =
  "For the ideal free-field Casimir lane, a measured alpha_EM value is not an input to the repository's parallel-plate kernel. The YM-to-Maxwell same-action weld still needs an explicit common field normalization, generator/pairing convention and action prefactor. Empirical electric-charge/fine-structure calibration remains a separate matter-coupling/phenomenology boundary and the StandardModelGaugeCouplingAuthorityFrontier remains metadata-only rather than being silently promoted into this Casimir proof."
