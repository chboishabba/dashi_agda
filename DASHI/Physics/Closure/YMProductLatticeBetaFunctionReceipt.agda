module DASHI.Physics.Closure.YMProductLatticeBetaFunctionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Product-lattice one-loop Yang-Mills beta-function receipt.

data YMProductLatticeBetaFunctionStatus : Set where
  oneLoopStandard4DWeakCouplingUVReceiptOnly :
    YMProductLatticeBetaFunctionStatus

data ProductLatticeGeometryFeature : Set where
  productLatticeWeakCouplingUV :
    ProductLatticeGeometryFeature

  fourDimensionalSUNGaugeTheory :
    ProductLatticeGeometryFeature

  nonHypercubicTriangularSquareAnisotropy :
    ProductLatticeGeometryFeature

  geometryIndependentOneLoopCoefficient :
    ProductLatticeGeometryFeature

canonicalProductLatticeGeometryFeatures :
  List ProductLatticeGeometryFeature
canonicalProductLatticeGeometryFeatures =
  productLatticeWeakCouplingUV
  ∷ fourDimensionalSUNGaugeTheory
  ∷ nonHypercubicTriangularSquareAnisotropy
  ∷ geometryIndependentOneLoopCoefficient
  ∷ []

data ProductLatticeBetaFunctionOpenItem : Set where
  higherLoopGeometryDependenceNotAddressed :
    ProductLatticeBetaFunctionOpenItem

  continuumClayMassGapProofNotSupplied :
    ProductLatticeBetaFunctionOpenItem

  fullConstructiveYMMeasureNotSupplied :
    ProductLatticeBetaFunctionOpenItem

canonicalProductLatticeBetaFunctionOpenItems :
  List ProductLatticeBetaFunctionOpenItem
canonicalProductLatticeBetaFunctionOpenItems =
  higherLoopGeometryDependenceNotAddressed
  ∷ continuumClayMassGapProofNotSupplied
  ∷ fullConstructiveYMMeasureNotSupplied
  ∷ []

data ProductLatticeBetaFunctionPromotion : Set where

productLatticeBetaFunctionPromotionImpossibleHere :
  ProductLatticeBetaFunctionPromotion →
  ⊥
productLatticeBetaFunctionPromotionImpossibleHere ()

productLatticeWeakCouplingUVStatementLabel : String
productLatticeWeakCouplingUVStatementLabel =
  "Product lattice weak-coupling UV structure is 3+1D SU(N) gauge theory with non-hypercubic triangular/square anisotropic geometry."

standard4DOneLoopB0Label : String
standard4DOneLoopB0Label =
  "Standard 4D SU(N) one-loop coefficient: b0 = 11N/3 - 2nf/3."

su2PureOneLoopB0Label : String
su2PureOneLoopB0Label =
  "Pure SU(2) specialization: b0 = 22/3."

geometryIndependenceLabel : String
geometryIndependenceLabel =
  "At leading one-loop order the universal beta-function coefficient is independent of triangular/square anisotropic lattice geometry."

record YMProductLatticeBetaFunctionReceipt : Setω where
  field
    status :
      YMProductLatticeBetaFunctionStatus

    geometryFeatures :
      List ProductLatticeGeometryFeature

    geometryFeaturesAreCanonical :
      geometryFeatures ≡ canonicalProductLatticeGeometryFeatures

    openItems :
      List ProductLatticeBetaFunctionOpenItem

    openItemsAreCanonical :
      openItems ≡ canonicalProductLatticeBetaFunctionOpenItems

    weakCouplingUVStatement :
      String

    weakCouplingUVStatementIsCanonical :
      weakCouplingUVStatement ≡ productLatticeWeakCouplingUVStatementLabel

    standard4DOneLoopB0 :
      String

    standard4DOneLoopB0IsCanonical :
      standard4DOneLoopB0 ≡ standard4DOneLoopB0Label

    su2PureOneLoopB0 :
      String

    su2PureOneLoopB0IsCanonical :
      su2PureOneLoopB0 ≡ su2PureOneLoopB0Label

    geometryIndependenceStatement :
      String

    geometryIndependenceStatementIsCanonical :
      geometryIndependenceStatement ≡ geometryIndependenceLabel

    productLatticeBetaFunctionEqualsStandard4D :
      Bool

    productLatticeBetaFunctionEqualsStandard4DIsTrue :
      productLatticeBetaFunctionEqualsStandard4D ≡ true

    equalityScopeIsOneLoop :
      Bool

    equalityScopeIsOneLoopIsTrue :
      equalityScopeIsOneLoop ≡ true

    latticeGeometryDoesNotAffectOneLoopBeta :
      Bool

    latticeGeometryDoesNotAffectOneLoopBetaIsTrue :
      latticeGeometryDoesNotAffectOneLoopBeta ≡ true

    fullProofSupplied :
      Bool

    fullProofSuppliedIsFalse :
      fullProofSupplied ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List ProductLatticeBetaFunctionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open YMProductLatticeBetaFunctionReceipt public

canonicalYMProductLatticeBetaFunctionReceipt :
  YMProductLatticeBetaFunctionReceipt
canonicalYMProductLatticeBetaFunctionReceipt =
  record
    { status =
        oneLoopStandard4DWeakCouplingUVReceiptOnly
    ; geometryFeatures =
        canonicalProductLatticeGeometryFeatures
    ; geometryFeaturesAreCanonical =
        refl
    ; openItems =
        canonicalProductLatticeBetaFunctionOpenItems
    ; openItemsAreCanonical =
        refl
    ; weakCouplingUVStatement =
        productLatticeWeakCouplingUVStatementLabel
    ; weakCouplingUVStatementIsCanonical =
        refl
    ; standard4DOneLoopB0 =
        standard4DOneLoopB0Label
    ; standard4DOneLoopB0IsCanonical =
        refl
    ; su2PureOneLoopB0 =
        su2PureOneLoopB0Label
    ; su2PureOneLoopB0IsCanonical =
        refl
    ; geometryIndependenceStatement =
        geometryIndependenceLabel
    ; geometryIndependenceStatementIsCanonical =
        refl
    ; productLatticeBetaFunctionEqualsStandard4D =
        true
    ; productLatticeBetaFunctionEqualsStandard4DIsTrue =
        refl
    ; equalityScopeIsOneLoop =
        true
    ; equalityScopeIsOneLoopIsTrue =
        refl
    ; latticeGeometryDoesNotAffectOneLoopBeta =
        true
    ; latticeGeometryDoesNotAffectOneLoopBetaIsTrue =
        refl
    ; fullProofSupplied =
        false
    ; fullProofSuppliedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

productLatticeBetaFunctionEqualsStandard4DAtOneLoop :
  productLatticeBetaFunctionEqualsStandard4D
    canonicalYMProductLatticeBetaFunctionReceipt
    ≡ true
productLatticeBetaFunctionEqualsStandard4DAtOneLoop =
  refl

latticeGeometryDoesNotAffectOneLoopBetaFlag :
  latticeGeometryDoesNotAffectOneLoopBeta
    canonicalYMProductLatticeBetaFunctionReceipt
    ≡ true
latticeGeometryDoesNotAffectOneLoopBetaFlag =
  refl

productLatticeBetaFunctionReceiptKeepsClayFalse :
  clayYangMillsPromoted canonicalYMProductLatticeBetaFunctionReceipt
    ≡ false
productLatticeBetaFunctionReceiptKeepsClayFalse =
  refl
