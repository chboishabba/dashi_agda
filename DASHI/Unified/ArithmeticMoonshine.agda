module DASHI.Unified.ArithmeticMoonshine where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Algebra.MoonshineBridge as MoonshineBridge
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Interop.UnifiedMathLanguageAssertedProofs as Asserted
import DASHI.Interop.UnifiedMathLanguageSpine as Unified
import DASHI.Physics.Closure.MonsterMoonshineJDistributionSupportReceipt as JDistribution
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as PrimeLane
import DASHI.Physics.Moonshine.ModularJInvariantAlphaReceipt as ModularJ
import DASHI.Unified.InvariantSpine as Spine

moonshineScalarBridgeSurface : MoonshineBridge.MoonshineScalarBridge
moonshineScalarBridgeSurface =
  MoonshineBridge.moonshineScalarBridgeSurface

modularJAlphaStatus : ModularJ.ModularJInvariantAlphaStatus
modularJAlphaStatus =
  ModularJ.modularAnchorsRecordedNoAlphaDerivation

arithmeticMoonshineObject : Spine.UnifiedObjectInvariant
arithmeticMoonshineObject =
  Spine.unifiedObjectInvariant
    "arithmetic-moonshine-parent"
    Unified.qftMoonshineLane
    "modular-j, moonshine coefficient, Monster carrier, and prime-lane observations"
    "arithmetic/moonshine carrier -> literal j anchor -> non-promoting receipt"
    Unified.jInvariantCarrier
    (Spine.defaultRoleVector "arithmetic-moonshine-parent")
    Residual.exact
    Asserted.internalConditionalProof
    Spine.stronglyInvariant
    (Spine.literalModularJProjection "modular-j authority is literal only for this arithmetic/moonshine carrier")
    (Spine.arithmeticMoonshineProjectionBundle "arithmetic/moonshine has literal modular-j and Hecke parent projections; other projections remain non-promoting")

canonicalArithmeticMoonshineObjects : List Spine.UnifiedObjectInvariant
canonicalArithmeticMoonshineObjects =
  arithmeticMoonshineObject ∷ []

arithmeticMoonshineJStatusIsLiteral :
  Spine.JProjection.status (Spine.jProjection arithmeticMoonshineObject)
    ≡
    Spine.literalModularJ
arithmeticMoonshineJStatusIsLiteral =
  refl

arithmeticMoonshineJPromotionBlocked :
  Spine.objectExternalJPromotion arithmeticMoonshineObject ≡ false
arithmeticMoonshineJPromotionBlocked =
  refl
