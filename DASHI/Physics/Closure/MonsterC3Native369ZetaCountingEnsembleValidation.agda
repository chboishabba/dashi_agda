module DASHI.Physics.Closure.MonsterC3Native369ZetaCountingEnsembleValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Closure.MonsterC3Native369ZetaCountingEnsembleExact as E
import DASHI.Physics.Laws.ThermodynamicStatisticalLaws as Thermo

zetaBasisLabelCountIs65610 : E.zetaBasisLabelCount ≡ 65610
zetaBasisLabelCountIs65610 = refl

normalizationPaid :
  E.zetaWeightNumerator * E.zetaBasisLabelCount ≡ E.zetaWeightDenominator
normalizationPaid = refl

nativeFiniteBasisLabelCarrierPaid :
  E.NativeZetaEnsembleBoundary.native369FiniteBasisLabelCarrierPaid
    E.canonicalNativeZetaEnsembleBoundary ≡ true
nativeFiniteBasisLabelCarrierPaid = refl

finiteBasisLabelsAreNotAllLinearWZetaStates :
  E.NativeZetaEnsembleBoundary.finiteBasisLabelsAreAllLinearWZetaStates
    E.canonicalNativeZetaEnsembleBoundary ≡ false
finiteBasisLabelsAreNotAllLinearWZetaStates = refl

actualRepresentationNativeBasisStillOpen :
  E.NativeZetaEnsembleBoundary.actualRepresentationNativeBasisRecognitionPaidHere
    E.canonicalNativeZetaEnsembleBoundary ≡ false
actualRepresentationNativeBasisStillOpen = refl

physicalThermalPromotionStillBlocked :
  E.NativeZetaEnsembleBoundary.nativeUniformCountingIsPhysicalThermalEnsemble
    E.canonicalNativeZetaEnsembleBoundary ≡ false
physicalThermalPromotionStillBlocked = refl

ensembleNormalised :
  Thermo.StatisticalEnsemble.Normalised E.native369ZetaCountingEnsemble tt
ensembleNormalised = refl
