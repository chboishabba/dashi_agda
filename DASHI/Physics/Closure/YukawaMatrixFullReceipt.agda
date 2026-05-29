module DASHI.Physics.Closure.YukawaMatrixFullReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Explicit carrier down-type Yukawa matrix diagnostic.
--
-- The matrix is recorded symbolically.  The receipt does not diagonalise it
-- into physical masses and does not promote CKM authority.

data YukawaMatrixFullStatus : Set where
  downTypeCarrierMatrixStructureRecorded :
    YukawaMatrixFullStatus

data YukawaMatrixOpenEntry : Set where
  y13P2P5PhysicalAuthorityNotYetDerived :
    YukawaMatrixOpenEntry

data YukawaMatrixFullPromotion : Set where

yukawaMatrixFullPromotionImpossibleHere :
  YukawaMatrixFullPromotion →
  ⊥
yukawaMatrixFullPromotionImpossibleHere ()

record YukawaMatrixFullReceipt : Set where
  field
    status :
      YukawaMatrixFullStatus

    alphaSymbol :
      String

    yd11SelfCoupling :
      String

    yd22SelfCoupling :
      String

    yd33SelfCoupling :
      String

    yd12Entry :
      String

    yd23Entry :
      String

    yd13Entry :
      String

    matrixShape :
      String

    ydDaggerYdSymbolicShape :
      String

    diagonalEntriesAreHeegnerSelfCouplings :
      Bool

    diagonalEntriesAreHeegnerSelfCouplingsIsTrue :
      diagonalEntriesAreHeegnerSelfCouplings ≡ true

    yukawaMatrixStructureInhabited :
      Bool

    yukawaMatrixStructureInhabitedIsTrue :
      yukawaMatrixStructureInhabited ≡ true

    y13OpenEntries :
      List YukawaMatrixOpenEntry

    y13OpenEntriesCanonical :
      y13OpenEntries ≡ y13P2P5PhysicalAuthorityNotYetDerived ∷ []

    yukawaPhysicalEigenbasis :
      Bool

    yukawaPhysicalEigenbasisIsFalse :
      yukawaPhysicalEigenbasis ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    promotionFlags :
      List YukawaMatrixFullPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YukawaMatrixFullReceipt public

canonicalYukawaMatrixFullReceipt :
  YukawaMatrixFullReceipt
canonicalYukawaMatrixFullReceipt =
  record
    { status =
        downTypeCarrierMatrixStructureRecorded
    ; alphaSymbol =
        "alpha1"
    ; yd11SelfCoupling =
        "(Y_d)11 = 2*pi"
    ; yd22SelfCoupling =
        "(Y_d)22 = 4*pi/3"
    ; yd33SelfCoupling =
        "(Y_d)33 = 8*pi/3"
    ; yd12Entry =
        "(Y_d)12 = alpha1 * pi * sqrt(3)"
    ; yd23Entry =
        "(Y_d)23 = alpha1^2 * (14/sqrt(24)) * (8*pi/3)"
    ; yd13Entry =
        "(Y_d)13 diagnostic = alpha1^3 * (24*pi/sqrt(6)) * exp(i*delta_29); physical authority remains open"
    ; matrixShape =
        "upper triangular Y_d with Heegner self-couplings on the diagonal"
    ; ydDaggerYdSymbolicShape =
        "Y_d^dagger Y_d has diagonal norm sums and off-diagonal products from y12,y13,y23"
    ; diagonalEntriesAreHeegnerSelfCouplings =
        true
    ; diagonalEntriesAreHeegnerSelfCouplingsIsTrue =
        refl
    ; yukawaMatrixStructureInhabited =
        true
    ; yukawaMatrixStructureInhabitedIsTrue =
        refl
    ; y13OpenEntries =
        y13P2P5PhysicalAuthorityNotYetDerived ∷ []
    ; y13OpenEntriesCanonical =
        refl
    ; yukawaPhysicalEigenbasis =
        false
    ; yukawaPhysicalEigenbasisIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The full carrier down-type matrix structure is recorded"
        ∷ "The p2-p5 y13 diagnostic entry is recorded separately; physical authority remains open"
        ∷ "Physical eigenbasis and CKM promotion remain false until diagonalisation authority is supplied"
        ∷ []
    }

yukawaMatrixFullStructureInhabited :
  yukawaMatrixStructureInhabited canonicalYukawaMatrixFullReceipt ≡ true
yukawaMatrixFullStructureInhabited =
  refl

yukawaMatrixFullPhysicalEigenbasisStillFalse :
  yukawaPhysicalEigenbasis canonicalYukawaMatrixFullReceipt ≡ false
yukawaMatrixFullPhysicalEigenbasisStillFalse =
  refl
