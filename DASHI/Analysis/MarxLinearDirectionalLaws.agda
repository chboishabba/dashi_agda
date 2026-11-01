module DASHI.Analysis.MarxLinearDirectionalLaws where

open import Agda.Primitive using (Set₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import DASHI.Analysis.MarxDifferentialCore
open import DASHI.Analysis.MarxHigherCalculus

------------------------------------------------------------------------
-- Pointwise addition of linear maps requires the additive interchange law on
-- the codomain module.  It is isolated here rather than silently assuming that
-- every Module record has a commutative additive carrier.

record ModuleAddInterchange
  {A : MarxAlgebra}
  (W : Module A)
  : Set₁ where
  field
    addInterchange :
      ∀ a b c d →
      _+V_ W (_+V_ W a b) (_+V_ W c d)
      ≡ _+V_ W (_+V_ W a c) (_+V_ W b d)

open ModuleAddInterchange public

linearAdd :
  {A : MarxAlgebra} →
  {V W : Module A} →
  ModuleAddInterchange W →
  LinearMap A V W →
  LinearMap A V W →
  LinearMap A V W
linearAdd {W = W} interchange F G =
  record
    { apply = λ v → _+V_ W (apply F v) (apply G v)
    ; mapZero =
        trans
          (cong₂ (_+V_ W) (mapZero F) (mapZero G))
          (addZeroLeftV W (zeroV W))
    ; mapAdd = λ u v →
        trans
          (cong₂ (_+V_ W) (mapAdd F u v) (mapAdd G u v))
          (addInterchange interchange
            (apply F u) (apply F v)
            (apply G u) (apply G v))
    ; mapScale = λ scalar v →
        trans
          (cong₂ (_+V_ W)
            (mapScale F scalar v)
            (mapScale G scalar v))
          (sym
            (scaleDistributesAddV W scalar (apply F v) (apply G v)))
    }

linearAddPointwise :
  {A : MarxAlgebra} →
  {V W : Module A} →
  (interchange : ModuleAddInterchange W) →
  (F G : LinearMap A V W) →
  ∀ v →
  apply (linearAdd interchange F G) v
  ≡ _+V_ W (apply F v) (apply G v)
linearAddPointwise interchange F G v = refl

------------------------------------------------------------------------
-- Directional derivative and chain rule.

frechetImpliesDirectional :
  {A : MarxAlgebra} →
  {V W : Module A} →
  {R : VectorLittleOStructure A V W} →
  {f : Vector V → Vector W} →
  {x : Vector V} →
  FrechetDerivativeAt R f x →
  Vector V → Vector W
frechetImpliesDirectional = DirectionalDerivativeAt

directionalChainRule :
  {A : MarxAlgebra} →
  {U V W : Module A} →
  {RUV : VectorLittleOStructure A U V} →
  {RVW : VectorLittleOStructure A V W} →
  {RUW : VectorLittleOStructure A U W} →
  {f : Vector V → Vector W} →
  {g : Vector U → Vector V} →
  {x : Vector U} →
  (F : FrechetDerivativeAt RVW f (g x)) →
  (G : FrechetDerivativeAt RUV g x) →
  (data : FrechetChainRuleData RUV RVW RUW F G) →
  ∀ direction →
  DirectionalDerivativeAt (frechetChainRule F G data) direction
  ≡ apply (derivative F)
      (DirectionalDerivativeAt G direction)
directionalChainRule F G data direction = refl
