module DASHI.Unified.CarrierGrammar where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Interop.PNFRoleVectorAlgebra as Role
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Interop.UnifiedMathLanguageAssertedProofs as Asserted
import DASHI.Interop.UnifiedMathLanguageSpine as Unified
import DASHI.Unified.InvariantSpine as Spine

carrierGrammarObject : Spine.UnifiedObjectInvariant
carrierGrammarObject =
  Spine.unifiedObjectInvariant
    "carrier-grammar-parent"
    Unified.dialecticalReasoningLane
    "repo lanes share observation and carrier vocabulary"
    "observation -> projection -> carrier/role vector -> residual"
    Unified.observationProjectionCarrier
    (Spine.defaultRoleVector "carrier-grammar-parent")
    Residual.exact
    Asserted.carrierOnly
    Spine.softInvariant
    (Spine.softJProjection "carrier grammar keeps a required non-promoting j-projection field")
    (Spine.softFormalProjectionBundle "carrier grammar inherits the DASHI formal projection parent family")

canonicalCarrierGrammarObjects : List Spine.UnifiedObjectInvariant
canonicalCarrierGrammarObjects =
  carrierGrammarObject ∷ []

carrierGrammarJPromotionBlocked :
  Spine.objectExternalJPromotion carrierGrammarObject ≡ false
carrierGrammarJPromotionBlocked =
  refl
