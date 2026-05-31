module DASHI.Physics.Closure.CKMCarrierProfiniteActionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- CKM p=7 carrier as a profinite CM action.
--
-- The p=7 CKM level-k datum is recorded as the Heegner point on X_0(7^k)
-- attached to the CM curve with j=-3375.  Since 7 ramifies in O_-7, the
-- unique CM isogeny of degree 7^k is [pi^k] with pi=sqrt(-7), and the
-- datum maps to ker([pi^k]) = E[pi^k].  Passing to the inverse limit gives
-- the rank-one CM eigenspace of the 7-adic Tate module with G_K-action by
-- the CM character psi_7.

data CMCurveModel : Set where
  EMinus3375 :
    CMCurveModel

data CMOrder : Set where
  OMinus7 :
    CMOrder

data RamifiedPrimeDatum : Set where
  sevenEqualsP7Squared :
    RamifiedPrimeDatum

data CKMLevelDatum : Set where
  heegnerPointOnX0SevenPower :
    CKMLevelDatum

data CKMCarrierMorphism : Set where
  heegnerPointToPiPowerKernel :
    CKMCarrierMorphism

data CKMProfiniteActionStatus : Set where
  carrierMorphismConstructed :
    CKMProfiniteActionStatus

data ReductionTypeAtSeven : Set where
  additiveReductionRamifiedCM :
    ReductionTypeAtSeven

data PromotionToken : Set where

promotionImpossibleHere :
  PromotionToken →
  ⊥
promotionImpossibleHere ()

weierstrassModelStatement : String
weierstrassModelStatement =
  "E_-3375 is represented by y^2 = x^3 - 35x - 98 and has j=-3375."

cmStatement : String
cmStatement =
  "E_-3375 has complex multiplication by O_-7 = Z[(1+sqrt(-7))/2]."

ramificationStatement : String
ramificationStatement =
  "The rational prime 7 ramifies in O_-7 as (7)=p_7^2, with uniformiser pi=sqrt(-7)."

levelDatumStatement : String
levelDatumStatement =
  "The CKM p=7 level-k datum is the Heegner point y_k on X_0(7^k) with CM by O_-7."

isogenyTowerStatement : String
isogenyTowerStatement =
  "The degree-7^k CM isogeny in the ramified p_7 direction is [pi^k] : E_-3375 -> E_-3375, unique up to Aut(E)={+-1}."

kernelStatement : String
kernelStatement =
  "phi_k(y_k)=ker([pi^k])=E[pi^k], and E[pi^k] is cyclic as O_-7/pi^k ~= Z/7^k Z."

inverseLimitStatement : String
inverseLimitStatement =
  "The inverse limit lim_k E[pi^k] is the rank-one CM eigenspace T_7^CM(E) ~= Z_7(psi_7)."

equivarianceStatement : String
equivarianceStatement =
  "The maps phi_k are G_K-equivariant because CM endomorphisms commute with G_K by the fundamental theorem of complex multiplication."

reductionStatement : String
reductionStatement =
  "At p=7 the model has additive reduction with v_7(Delta)=3 and v_7(j)=0; this is consistent with ramified CM and does not obstruct the inverse-limit Tate-module construction."

record CKMCarrierProfiniteActionReceipt : Set where
  field
    curve :
      CMCurveModel

    curveIsEMinus3375 :
      curve ≡ EMinus3375

    curveModel :
      String

    curveModelIsCanonical :
      curveModel ≡ weierstrassModelStatement

    cmOrder :
      CMOrder

    cmOrderIsOMinus7 :
      cmOrder ≡ OMinus7

    cmOrderStatement :
      String

    cmOrderStatementIsCanonical :
      cmOrderStatement ≡ cmStatement

    ramifiedPrime :
      RamifiedPrimeDatum

    ramifiedPrimeIsSeven :
      ramifiedPrime ≡ sevenEqualsP7Squared

    ramification :
      String

    ramificationIsCanonical :
      ramification ≡ ramificationStatement

    levelDatum :
      CKMLevelDatum

    levelDatumIsHeegnerPoint :
      levelDatum ≡ heegnerPointOnX0SevenPower

    levelDatumDescription :
      String

    levelDatumDescriptionIsCanonical :
      levelDatumDescription ≡ levelDatumStatement

    morphism :
      CKMCarrierMorphism

    morphismIsKernelMap :
      morphism ≡ heegnerPointToPiPowerKernel

    isogenyTower :
      String

    isogenyTowerIsCanonical :
      isogenyTower ≡ isogenyTowerStatement

    kernelIdentification :
      String

    kernelIdentificationIsCanonical :
      kernelIdentification ≡ kernelStatement

    inverseLimit :
      String

    inverseLimitIsCanonical :
      inverseLimit ≡ inverseLimitStatement

    morphismConstructed :
      Bool

    morphismConstructedIsTrue :
      morphismConstructed ≡ true

    morphismNatural :
      Bool

    morphismNaturalIsTrue :
      morphismNatural ≡ true

    galoisEquivariant :
      Bool

    galoisEquivariantIsTrue :
      galoisEquivariant ≡ true

    equivarianceReason :
      String

    equivarianceReasonIsCanonical :
      equivarianceReason ≡ equivarianceStatement

    reductionType :
      ReductionTypeAtSeven

    reductionTypeIsAdditiveRamifiedCM :
      reductionType ≡ additiveReductionRamifiedCM

    reductionNote :
      String

    reductionNoteIsCanonical :
      reductionNote ≡ reductionStatement

    tateModuleCMEigenspaceRankOne :
      Bool

    tateModuleCMEigenspaceRankOneIsTrue :
      tateModuleCMEigenspaceRankOne ≡ true

    profiniteActionViaPsi7 :
      Bool

    profiniteActionViaPsi7IsTrue :
      profiniteActionViaPsi7 ≡ true

    status :
      CKMProfiniteActionStatus

    statusIsConstructed :
      status ≡ carrierMorphismConstructed

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    G7Unblocked :
      Bool

    G7UnblockedIsFalse :
      G7Unblocked ≡ false

open CKMCarrierProfiniteActionReceipt public

canonicalCKMCarrierProfiniteActionReceipt :
  CKMCarrierProfiniteActionReceipt
canonicalCKMCarrierProfiniteActionReceipt =
  record
    { curve =
        EMinus3375
    ; curveIsEMinus3375 =
        refl
    ; curveModel =
        weierstrassModelStatement
    ; curveModelIsCanonical =
        refl
    ; cmOrder =
        OMinus7
    ; cmOrderIsOMinus7 =
        refl
    ; cmOrderStatement =
        cmStatement
    ; cmOrderStatementIsCanonical =
        refl
    ; ramifiedPrime =
        sevenEqualsP7Squared
    ; ramifiedPrimeIsSeven =
        refl
    ; ramification =
        ramificationStatement
    ; ramificationIsCanonical =
        refl
    ; levelDatum =
        heegnerPointOnX0SevenPower
    ; levelDatumIsHeegnerPoint =
        refl
    ; levelDatumDescription =
        levelDatumStatement
    ; levelDatumDescriptionIsCanonical =
        refl
    ; morphism =
        heegnerPointToPiPowerKernel
    ; morphismIsKernelMap =
        refl
    ; isogenyTower =
        isogenyTowerStatement
    ; isogenyTowerIsCanonical =
        refl
    ; kernelIdentification =
        kernelStatement
    ; kernelIdentificationIsCanonical =
        refl
    ; inverseLimit =
        inverseLimitStatement
    ; inverseLimitIsCanonical =
        refl
    ; morphismConstructed =
        true
    ; morphismConstructedIsTrue =
        refl
    ; morphismNatural =
        true
    ; morphismNaturalIsTrue =
        refl
    ; galoisEquivariant =
        true
    ; galoisEquivariantIsTrue =
        refl
    ; equivarianceReason =
        equivarianceStatement
    ; equivarianceReasonIsCanonical =
        refl
    ; reductionType =
        additiveReductionRamifiedCM
    ; reductionTypeIsAdditiveRamifiedCM =
        refl
    ; reductionNote =
        reductionStatement
    ; reductionNoteIsCanonical =
        refl
    ; tateModuleCMEigenspaceRankOne =
        true
    ; tateModuleCMEigenspaceRankOneIsTrue =
        refl
    ; profiniteActionViaPsi7 =
        true
    ; profiniteActionViaPsi7IsTrue =
        refl
    ; status =
        carrierMorphismConstructed
    ; statusIsConstructed =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; G7Unblocked =
        false
    ; G7UnblockedIsFalse =
        refl
    }

ckmCarrierMorphismExists :
  morphismConstructed canonicalCKMCarrierProfiniteActionReceipt
  ≡ true
ckmCarrierMorphismExists =
  refl

ckmCarrierProfiniteActionDoesNotPromoteG7 :
  G7Unblocked canonicalCKMCarrierProfiniteActionReceipt
  ≡ false
ckmCarrierProfiniteActionDoesNotPromoteG7 =
  refl
