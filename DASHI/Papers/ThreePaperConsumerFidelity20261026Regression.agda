module DASHI.Papers.ThreePaperConsumerFidelity20261026Regression where

-- Synthetic regression for the exact source-hypothesis collision owners.
-- Attribution: Miller (2021), DOI 10.1090/bproc/74; Yan/Rădulescu
-- (2021), DOI 10.1007/s12215-020-00540-3.
-- The generic nonfactorability proof belongs to the pre-existing DASHI
-- core; these two concrete source-domain/force-divergence instantiations
-- belong to this research tranche. No empirical or Clay promotion.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Papers.ThreePaperConsumerFidelity20261026Exact as Fidelity

printedPressureCannotDistinguishForcingCases :
  Fidelity.eraseForceDivergence Fidelity.divergenceFreeForcing ≡
  Fidelity.eraseForceDivergence Fidelity.forcingWithNonzeroDivergence
printedPressureCannotDistinguishForcingCases = refl

forcingStatusIsLost :
  NF.FactorsThrough
    Fidelity.eraseForceDivergence
    Fidelity.requiredPressureCorrection → ⊥
forcingStatusIsLost =
  Fidelity.erasedForcingCannotRecoverSourcePressureCorrection

r3AndT3ShareErasedLabel :
  Fidelity.erasePhysicalDomain Fidelity.unforcedWholeSpaceR3 ≡
  Fidelity.erasePhysicalDomain Fidelity.periodicGalerkinT3
r3AndT3ShareErasedLabel = refl

domainErasureCannotProduceMillerSource :
  NF.FactorsThrough
    Fidelity.erasePhysicalDomain Fidelity.actualPhysicalDomain → ⊥
domainErasureCannotProduceMillerSource =
  Fidelity.domainBlindEstimateCannotDetermineMillerSource


-- A vanishing projected-vorticity observation cannot itself certify
-- the independently required spatial direction regularity.
bothDirectionWorldsProjectToZero :
  Fidelity.forgetDirectionVariation Fidelity.lowVariationUnitDirection ≡
  Fidelity.forgetDirectionVariation Fidelity.arbitrarilySteepUnitDirection
bothDirectionWorldsProjectToZero = refl

gradientObligationCannotBeEliminated :
  NF.FactorsThrough
    Fidelity.forgetDirectionVariation
    Fidelity.requiredDirectionVariation → ⊥
gradientObligationCannotBeEliminated =
  Fidelity.zeroProjectedVorticityCannotInferDirectionRegularity
