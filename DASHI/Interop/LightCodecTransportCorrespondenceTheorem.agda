module DASHI.Interop.LightCodecTransportCorrespondenceTheorem where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.MDL.MDLDescentTradeoff as MDL
import DASHI.Interop.LightCodecTransportDischarge as LCD

------------------------------------------------------------------------
-- Conservative light/codec transport correspondence theorem.
--
-- This is not a promotion of the analogy into identity.  It says only:
-- once a concrete dashiRTX-style refresh/reuse update is bound to an
-- MDLParts package and supplies model/residual drop witnesses, the existing
-- MDLDescentTradeoff theorem gives MDL descent.

bool-select :
  ∀ {ℓ : Level} {A : Set ℓ} →
  Bool →
  A →
  A →
  A
bool-select true  x _ = x
bool-select false _ y = y

data LightCodecCorrespondenceStatus : Set where
  conditionalMDLInstance_analogyIdentityStillFalse :
    LightCodecCorrespondenceStatus

data LightCodecBinding : Set where
  modelLenIsRateComputeTv :
    LightCodecBinding
  residLenIsDistance :
    LightCodecBinding
  updateIsRefreshReuseStep :
    LightCodecBinding
  admissibleIsDistanceAboveThreshold :
    LightCodecBinding
  descentComesOnlyFromMDLTradeoff :
    LightCodecBinding

canonicalLightCodecBindings :
  List LightCodecBinding
canonicalLightCodecBindings =
  modelLenIsRateComputeTv
  ∷ residLenIsDistance
  ∷ updateIsRefreshReuseStep
  ∷ admissibleIsDistanceAboveThreshold
  ∷ descentComesOnlyFromMDLTradeoff
  ∷ []

record LightCodecTransportMDLBinding
  {ℓx ℓn : Level}
  (X : Set ℓx)
  (O : MDL.OrderedMonoid {ℓn})
  : Set (lsuc (ℓx ⊔ ℓn)) where
  private
    Carrier : Set ℓn
    Carrier = MDL.AddMonoid.N (MDL.OrderedMonoid.M O)

    _⊕_ : Carrier → Carrier → Carrier
    _⊕_ = MDL.AddMonoid._+_ (MDL.OrderedMonoid.M O)

  field
    Parts :
      MDL.MDLParts X O

    rate comp tv dist :
      X → Carrier

    threshold :
      Carrier

    _>_ :
      Carrier → Carrier → Set ℓn

    refresh reuse :
      X → X

    refreshMask :
      X → Bool

    modelLenIsRatePlusCompPlusTv :
      ∀ x →
        MDL.MDLParts.ModelLen Parts x
        ≡ _⊕_ (_⊕_ (rate x) (comp x)) (tv x)

    residLenIsDist :
      ∀ x →
        MDL.MDLParts.ResidLen Parts x
        ≡ dist x

    TIsRefreshReuseUpdateStep :
      ∀ x →
        MDL.MDLParts.T Parts x
        ≡ bool-select (refreshMask x) (refresh x) (reuse x)

  admissible :
    X → Set ℓn
  admissible x = _>_ (dist x) threshold

open LightCodecTransportMDLBinding public

data LightCodecCorrespondenceNonClaim : Set where
  codecIsNotLightPhysics :
    LightCodecCorrespondenceNonClaim
  noGlobalRenderingExactness :
    LightCodecCorrespondenceNonClaim
  noResidualSuppressionWithoutAccounting :
    LightCodecCorrespondenceNonClaim
  noEmpiricalBenchmarkPromotion :
    LightCodecCorrespondenceNonClaim
  noAnalogyIdentityPromotion :
    LightCodecCorrespondenceNonClaim

canonicalLightCodecCorrespondenceNonClaims :
  List LightCodecCorrespondenceNonClaim
canonicalLightCodecCorrespondenceNonClaims =
  codecIsNotLightPhysics
  ∷ noGlobalRenderingExactness
  ∷ noResidualSuppressionWithoutAccounting
  ∷ noEmpiricalBenchmarkPromotion
  ∷ noAnalogyIdentityPromotion
  ∷ []

lightCodecTransportAnalogyPromotesIdentityIsFalse :
  (discharge : LCD.LightCodecTransportAnalogyDischarge) →
  LCD.LightCodecTransportAnalogyDischarge.analogyPromotesIdentity discharge
    ≡ false
lightCodecTransportAnalogyPromotesIdentityIsFalse discharge =
  LCD.LightCodecTransportAnalogyDischarge.analogyPromotesIdentityIsFalse
    discharge

lightCodecTransportMDLDescent :
  ∀ {ℓx ℓn : Level} {X : Set ℓx}
    {O : MDL.OrderedMonoid {ℓn}} →
  (discharge : LCD.LightCodecTransportAnalogyDischarge) →
  (Parts : MDL.MDLParts X O) →
  (model-drop :
    ∀ x →
      MDL.OrderedMonoid._≤_ O
        (MDL.MDLParts.ModelLen Parts
          (MDL.MDLParts.P Parts (MDL.MDLParts.T Parts x)))
        (MDL.MDLParts.ModelLen Parts
          (MDL.MDLParts.P Parts x))) →
  (resid-drop :
    ∀ x →
      MDL.OrderedMonoid._≤_ O
        (MDL.MDLParts.ResidLen Parts
          (MDL.MDLParts.D Parts (MDL.MDLParts.T Parts x)))
        (MDL.MDLParts.ResidLen Parts
          (MDL.MDLParts.D Parts x))) →
  ∀ x →
    MDL.OrderedMonoid._≤_ O
      (MDL.MDLParts.MDL Parts (MDL.MDLParts.T Parts x))
      (MDL.MDLParts.MDL Parts x)
lightCodecTransportMDLDescent _ Parts model-drop resid-drop x =
  MDL.MDLDescent Parts
    (record
      { model-drop =
          model-drop
      ; resid-drop =
          resid-drop
      })
    x

lightCodecTransportAdmissibleMDLDescent :
  ∀ {ℓx ℓn : Level} {X : Set ℓx}
    {O : MDL.OrderedMonoid {ℓn}} →
  (discharge : LCD.LightCodecTransportAnalogyDischarge) →
  (binding : LightCodecTransportMDLBinding X O) →
  (tradeoff : MDL.TradeoffLemma (Parts binding)) →
  ∀ x →
    admissible binding x →
    MDL.OrderedMonoid._≤_ O
      (MDL.MDLParts.MDL (Parts binding)
        (MDL.MDLParts.T (Parts binding) x))
      (MDL.MDLParts.MDL (Parts binding) x)
lightCodecTransportAdmissibleMDLDescent _ binding tradeoff x _ =
  MDL.MDLDescent (Parts binding) tradeoff x

correspondenceReading :
  String
correspondenceReading =
  "Conditional bridge: with ModelLen=rate+comp+tv, ResidLen=dist, T=refresh/reuse, and admissible=dist>threshold, MDL descent follows only from MDLDescentTradeoff; codec/light identity remains false."

record LightCodecTransportCorrespondenceReceipt : Set₁ where
  field
    status :
      LightCodecCorrespondenceStatus

    statusIsConditional :
      status
      ≡ conditionalMDLInstance_analogyIdentityStillFalse

    discharge :
      LCD.LightCodecTransportAnalogyDischarge

    dischargeIsCanonical :
      discharge ≡ LCD.canonicalLightCodecTransportAnalogyDischarge

    analogyPromotesIdentity :
      Bool

    analogyPromotesIdentityMatchesDischarge :
      analogyPromotesIdentity
      ≡ LCD.LightCodecTransportAnalogyDischarge.analogyPromotesIdentity
          discharge

    analogyPromotesIdentityIsFalse :
      analogyPromotesIdentity ≡ false

    bindings :
      List LightCodecBinding

    bindingsAreCanonical :
      bindings ≡ canonicalLightCodecBindings

    nonClaims :
      List LightCodecCorrespondenceNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalLightCodecCorrespondenceNonClaims

    reading :
      String

    readingIsCanonical :
      reading ≡ correspondenceReading

    theoremUsesOnlyMDLTradeoff :
      Bool

    theoremUsesOnlyMDLTradeoffIsTrue :
      theoremUsesOnlyMDLTradeoff ≡ true

    physicsIdentityPromoted :
      Bool

    physicsIdentityPromotedIsFalse :
      physicsIdentityPromoted ≡ false

canonicalLightCodecTransportCorrespondenceReceipt :
  LightCodecTransportCorrespondenceReceipt
canonicalLightCodecTransportCorrespondenceReceipt =
  record
    { status =
        conditionalMDLInstance_analogyIdentityStillFalse
    ; statusIsConditional =
        refl
    ; discharge =
        LCD.canonicalLightCodecTransportAnalogyDischarge
    ; dischargeIsCanonical =
        refl
    ; analogyPromotesIdentity =
        LCD.LightCodecTransportAnalogyDischarge.analogyPromotesIdentity
          LCD.canonicalLightCodecTransportAnalogyDischarge
    ; analogyPromotesIdentityMatchesDischarge =
        refl
    ; analogyPromotesIdentityIsFalse =
        LCD.LightCodecTransportAnalogyDischarge.analogyPromotesIdentityIsFalse
          LCD.canonicalLightCodecTransportAnalogyDischarge
    ; bindings =
        canonicalLightCodecBindings
    ; bindingsAreCanonical =
        refl
    ; nonClaims =
        canonicalLightCodecCorrespondenceNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; reading =
        correspondenceReading
    ; readingIsCanonical =
        refl
    ; theoremUsesOnlyMDLTradeoff =
        true
    ; theoremUsesOnlyMDLTradeoffIsTrue =
        refl
    ; physicsIdentityPromoted =
        false
    ; physicsIdentityPromotedIsFalse =
        refl
    }

canonicalCorrespondenceStatus :
  LightCodecCorrespondenceStatus
canonicalCorrespondenceStatus =
  LightCodecTransportCorrespondenceReceipt.status
    canonicalLightCodecTransportCorrespondenceReceipt
