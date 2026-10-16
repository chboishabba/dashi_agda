module DASHI.Physics.Closure.MonsterC3Native369ZetaCountingEnsembleValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Closure.MonsterC3Native369ZetaCountingEnsembleExact as E
import DASHI.Physics.Laws.ThermodynamicStatisticalLaws as Thermo

zetaCountIs65610 : E.zetaStateCount ≡ 65610
zetaCountIs65610 = refl

normalizationPaid :
  E.zetaWeightNumerator * E.zetaStateCount ≡ E.zetaWeightDenominator
normalizationPaid = refl

nativeMicrostateCarrierPaid :
  E.NativeZetaEnsembleBoundary.native369MicrostateCarrierPaid
    E.canonicalNativeZetaEnsembleBoundary ≡ true
nativeMicrostateCarrierPaid = refl

physicalThermalPromotionStillBlocked :
  E.NativeZetaEnsembleBoundary.nativeUniformCountingIsPhysicalThermalEnsemble
    E.canonicalNativeZetaEnsembleBoundary ≡ false
physicalThermalPromotionStillBlocked = refl

ensembleNormalised :
  Thermo.StatisticalEnsemble.Normalised E.native369ZetaCountingEnsemble tt
ensembleNormalised = refl
