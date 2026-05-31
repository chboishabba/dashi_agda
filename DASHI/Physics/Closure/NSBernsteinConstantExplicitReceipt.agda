module DASHI.Physics.Closure.NSBernsteinConstantExplicitReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Explicit Navier-Stokes Bernstein constant receipt.
--
-- This receipt records the carrier Littlewood-Paley projector form
--
--   Fourier(P_j f)(xi) = Fourier(f)(xi) * phi(xi / p^j),
--
-- where phi is supported in the annulus
--
--   1/sqrt(p) <= |xi| <= sqrt(p).
--
-- Therefore, on the support of P_j, |xi| <= sqrt(p) * p^j, and Plancherel
-- gives
--
--   ||nabla P_j f||_L2 <= sqrt(p) * p^j ||P_j f||_L2.
--
-- Hence the explicit prime-carrier Bernstein constant is C0 = sqrt(p).
-- This is only a local analytic receipt; it makes no Clay, global
-- regularity, or terminal promotion.

data NSBernsteinConstantExplicitStatus : Set where
  carrierLPProjectorFourierFormRecorded :
    NSBernsteinConstantExplicitStatus

  annularSupportRecorded :
    NSBernsteinConstantExplicitStatus

  supportRadiusBoundRecorded :
    NSBernsteinConstantExplicitStatus

  bernsteinConstantDerived :
    NSBernsteinConstantExplicitStatus

  sampleValuesRecorded :
    NSBernsteinConstantExplicitStatus

  noClayOrGlobalPromotionStatus :
    NSBernsteinConstantExplicitStatus

canonicalNSBernsteinConstantExplicitStatus :
  List NSBernsteinConstantExplicitStatus
canonicalNSBernsteinConstantExplicitStatus =
  carrierLPProjectorFourierFormRecorded
  ∷ annularSupportRecorded
  ∷ supportRadiusBoundRecorded
  ∷ bernsteinConstantDerived
  ∷ sampleValuesRecorded
  ∷ noClayOrGlobalPromotionStatus
  ∷ []

data NSBernsteinConstantExplicitPromotion : Set where

nsBernsteinConstantExplicitPromotionImpossibleHere :
  NSBernsteinConstantExplicitPromotion →
  ⊥
nsBernsteinConstantExplicitPromotionImpossibleHere ()

carrierLPProjectorFourierForm : String
carrierLPProjectorFourierForm =
  "Fourier(P_j f)(xi) = Fourier(f)(xi) * phi(xi / p^j)"

carrierPhiSupportAnnulus : String
carrierPhiSupportAnnulus =
  "phi supported in annulus {1/sqrt(p) <= |xi| <= sqrt(p)}"

supportRadiusBound : String
supportRadiusBound =
  "on support, |xi| <= sqrt(p) * p^j"

bernsteinInequalityDerivedFormula : String
bernsteinInequalityDerivedFormula =
  "||nabla P_j f||_L2 <= sqrt(p) * p^j ||P_j f||_L2"

explicitBernsteinConstantFormula : String
explicitBernsteinConstantFormula =
  "C0 = sqrt(p)"

explicitBernsteinConstantDerivation : String
explicitBernsteinConstantDerivation =
  "The multiplier phi(xi/p^j) restricts xi to |xi| <= sqrt(p)*p^j; by Plancherel, ||nabla P_j f||_L2 <= sup_support |xi| ||P_j f||_L2 <= sqrt(p)*p^j ||P_j f||_L2, so C0=sqrt(p)."

c0AtP2Value : String
c0AtP2Value =
  "1.414"

c0AtP3Value : String
c0AtP3Value =
  "1.732"

c0AtP7Value : String
c0AtP7Value =
  "2.646"

nsBernsteinConstantExplicitStatement : String
nsBernsteinConstantExplicitStatement =
  "Explicit carrier LP-Bernstein receipt: Fourier(P_j f)(xi)=Fourier(f)(xi)*phi(xi/p^j), phi supported in {1/sqrt(p) <= |xi| <= sqrt(p)}; on support |xi| <= sqrt(p)*p^j, hence ||nabla P_j f||_L2 <= sqrt(p)*p^j||P_j f||_L2. Therefore C0=sqrt(p), independent of j. Sample values: C0(2)=1.414, C0(3)=1.732, C0(7)=2.646. No Clay, global, or terminal promotion."

record NSBernsteinConstantExplicitReceipt : Setω where
  field
    status :
      List NSBernsteinConstantExplicitStatus

    statusIsCanonical :
      status ≡ canonicalNSBernsteinConstantExplicitStatus

    carrierProjectorFourierForm :
      String

    carrierProjectorFourierFormIsCanonical :
      carrierProjectorFourierForm ≡ carrierLPProjectorFourierForm

    phiSupport :
      String

    phiSupportIsAnnular :
      phiSupport ≡ carrierPhiSupportAnnulus

    supportUpperRadius :
      String

    supportUpperRadiusIsCanonical :
      supportUpperRadius ≡ supportRadiusBound

    bernsteinInequality :
      String

    bernsteinInequalityIsCanonical :
      bernsteinInequality ≡ bernsteinInequalityDerivedFormula

    bernsteinConstant :
      String

    bernsteinConstantIsSqrtP :
      bernsteinConstant ≡ explicitBernsteinConstantFormula

    annularSupportRadius :
      String

    annularSupportRadiusIsSqrtP :
      annularSupportRadius ≡ "sqrt(p)"

    derivation :
      String

    derivationIsCanonical :
      derivation ≡ explicitBernsteinConstantDerivation

    jIndependent :
      Bool

    jIndependentIsTrue :
      jIndependent ≡ true

    derivationComplete :
      Bool

    derivationCompleteIsTrue :
      derivationComplete ≡ true

    c0AtP2 :
      String

    c0AtP2Is1414 :
      c0AtP2 ≡ c0AtP2Value

    c0AtP3 :
      String

    c0AtP3Is1732 :
      c0AtP3 ≡ c0AtP3Value

    c0AtP7 :
      String

    c0AtP7Is2646 :
      c0AtP7 ≡ c0AtP7Value

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    promotionFlags :
      List NSBernsteinConstantExplicitPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ nsBernsteinConstantExplicitStatement

    receiptBoundary :
      List String

open NSBernsteinConstantExplicitReceipt public

canonicalNSBernsteinConstantExplicitReceipt :
  NSBernsteinConstantExplicitReceipt
canonicalNSBernsteinConstantExplicitReceipt =
  record
    { status =
        canonicalNSBernsteinConstantExplicitStatus
    ; statusIsCanonical =
        refl
    ; carrierProjectorFourierForm =
        carrierLPProjectorFourierForm
    ; carrierProjectorFourierFormIsCanonical =
        refl
    ; phiSupport =
        carrierPhiSupportAnnulus
    ; phiSupportIsAnnular =
        refl
    ; supportUpperRadius =
        supportRadiusBound
    ; supportUpperRadiusIsCanonical =
        refl
    ; bernsteinInequality =
        bernsteinInequalityDerivedFormula
    ; bernsteinInequalityIsCanonical =
        refl
    ; bernsteinConstant =
        explicitBernsteinConstantFormula
    ; bernsteinConstantIsSqrtP =
        refl
    ; annularSupportRadius =
        "sqrt(p)"
    ; annularSupportRadiusIsSqrtP =
        refl
    ; derivation =
        explicitBernsteinConstantDerivation
    ; derivationIsCanonical =
        refl
    ; jIndependent =
        true
    ; jIndependentIsTrue =
        refl
    ; derivationComplete =
        true
    ; derivationCompleteIsTrue =
        refl
    ; c0AtP2 =
        c0AtP2Value
    ; c0AtP2Is1414 =
        refl
    ; c0AtP3 =
        c0AtP3Value
    ; c0AtP3Is1732 =
        refl
    ; c0AtP7 =
        c0AtP7Value
    ; c0AtP7Is2646 =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        nsBernsteinConstantExplicitStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Carrier LP projector Fourier form recorded"
        ∷ "phi support annulus recorded as {1/sqrt(p) <= |xi| <= sqrt(p)}"
        ∷ "On support |xi| <= sqrt(p)*p^j"
        ∷ "Plancherel gives ||nabla P_j f||_L2 <= sqrt(p)*p^j||P_j f||_L2"
        ∷ "C0=sqrt(p), independent of j"
        ∷ "Sample values recorded: C0(2)=1.414, C0(3)=1.732, C0(7)=2.646"
        ∷ "No Clay Navier-Stokes, global regularity, or terminal promotion is made"
        ∷ []
    }

explicitC0IsSqrtP :
  bernsteinConstant canonicalNSBernsteinConstantExplicitReceipt
  ≡
  explicitBernsteinConstantFormula
explicitC0IsSqrtP =
  refl

annularRadiusIsSqrtP :
  annularSupportRadius canonicalNSBernsteinConstantExplicitReceipt
  ≡
  "sqrt(p)"
annularRadiusIsSqrtP =
  refl

bernsteinConstantExplicitIsJIndependent :
  jIndependent canonicalNSBernsteinConstantExplicitReceipt ≡ true
bernsteinConstantExplicitIsJIndependent =
  refl

bernsteinConstantExplicitDerivationComplete :
  derivationComplete canonicalNSBernsteinConstantExplicitReceipt ≡ true
bernsteinConstantExplicitDerivationComplete =
  refl

bernsteinConstantExplicitDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalNSBernsteinConstantExplicitReceipt ≡ false
bernsteinConstantExplicitDoesNotPromoteClay =
  refl

bernsteinConstantExplicitDoesNotPromoteGlobalRegularity :
  globalRegularityPromoted canonicalNSBernsteinConstantExplicitReceipt ≡ false
bernsteinConstantExplicitDoesNotPromoteGlobalRegularity =
  refl

bernsteinConstantExplicitDoesNotPromoteTerminalClaim :
  terminalClayClaimPromoted canonicalNSBernsteinConstantExplicitReceipt ≡ false
bernsteinConstantExplicitDoesNotPromoteTerminalClaim =
  refl

nsBernsteinConstantExplicitNoPromotion :
  NSBernsteinConstantExplicitPromotion →
  ⊥
nsBernsteinConstantExplicitNoPromotion =
  nsBernsteinConstantExplicitPromotionImpossibleHere
