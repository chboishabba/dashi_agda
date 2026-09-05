module DASHI.Physics.Plasma.MHDCurlLerayProjectionInvariantExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (cong; _≡_; refl)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical

------------------------------------------------------------------------
-- CURL DOES NOT SEE THE LONGITUDINAL LERAY CORRECTION
------------------------------------------------------------------------

crossIgnoresLongitudinalCorrection :
  ∀ {r : Level} {F : C3.RealField r}
    (wave value : C3.Complex3 F)
    (alpha : C3.Complex F) →
  Helical.complex3Cross wave
    (C3.complex3Subtract value (C3.complex3Scale alpha wave))
  ≡ Helical.complex3Cross wave value
crossIgnoresLongitudinalCorrection {F = F}
    (C3.complex3 kx ky kz)
    (C3.complex3 vx vy vz)
    alpha =
  Field.complex3Ext
    (R.solve 7
      (λ kx ky kz vx vy vz a →
        ((ky R.⊗ (vz R.⊕ (R.⊝ (a R.⊗ kz))))
          R.⊕
          (R.⊝ (kz R.⊗ (vy R.⊕ (R.⊝ (a R.⊗ ky))))))
        R.⊜
        ((ky R.⊗ vz) R.⊕ (R.⊝ (kz R.⊗ vy))))
      refl kx ky kz vx vy vz alpha)
    (R.solve 7
      (λ kx ky kz vx vy vz a →
        ((kz R.⊗ (vx R.⊕ (R.⊝ (a R.⊗ kx))))
          R.⊕
          (R.⊝ (kx R.⊗ (vz R.⊕ (R.⊝ (a R.⊗ kz))))))
        R.⊜
        ((kz R.⊗ vx) R.⊕ (R.⊝ (kx R.⊗ vz))))
      refl kx ky kz vx vy vz alpha)
    (R.solve 7
      (λ kx ky kz vx vy vz a →
        ((kx R.⊗ (vy R.⊕ (R.⊝ (a R.⊗ ky))))
          R.⊕
          (R.⊝ (ky R.⊗ (vx R.⊕ (R.⊝ (a R.⊗ kx))))))
        R.⊜
        ((kx R.⊗ vy) R.⊕ (R.⊝ (ky R.⊗ vx))))
      refl kx ky kz vx vy vz alpha)
  where module R = Ring.Solver F

curlLerayProjectionInvariant :
  ∀ {r : Level} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  Helical.curlSymbol E k (C3.lerayProject3 E I k value)
  ≡ Helical.curlSymbol E k value
curlLerayProjectionInvariant {F = F} E I k value =
  cong
    (C3.complex3Scale (C3.complexI F))
    (crossIgnoresLongitudinalCorrection
      (C3.modeVector E k)
      value
      (C3.complexMultiply
        (C3.realEmbed F (C3.inverseNormSquared I k))
        (C3.bilinearDot3 (C3.modeVector E k) value)))

record CurlLerayProjectionBoundary : Set where
  constructor curl-leray-projection-boundary
  field
    longitudinalLerayCorrectionInvisibleToCurl : Bool
    longitudinalLerayCorrectionInvisibleToCurlIsTrue :
      longitudinalLerayCorrectionInvisibleToCurl ≡ true

    curlProjectionInvariantOwned : Bool
    curlProjectionInvariantOwnedIsTrue : curlProjectionInvariantOwned ≡ true

    projectionMayStillMatterToOtherObservers : Bool
    projectionMayStillMatterToOtherObserversIsTrue :
      projectionMayStillMatterToOtherObservers ≡ true

canonicalCurlLerayProjectionBoundary : CurlLerayProjectionBoundary
canonicalCurlLerayProjectionBoundary =
  curl-leray-projection-boundary true refl true refl true refl
