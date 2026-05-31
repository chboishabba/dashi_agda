module DASHI.Physics.Closure.NSLowBandBoundReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Navier-Stokes low-band bound receipt.
--
-- This receipt records only the finite low-band estimate obtained from the
-- Leray band bound.  It does not promote a Clay/global regularity theorem.

data NSLowBandBoundStatus : Set where
  lerayBandBoundAppliedToLowModes :
    NSLowBandBoundStatus

  finiteLowBandSumRecorded :
    NSLowBandBoundStatus

  viscosityCutoffBoundRecorded :
    NSLowBandBoundStatus

  noClayOrGlobalTerminalPromotion :
    NSLowBandBoundStatus

canonicalNSLowBandBoundStatus :
  List NSLowBandBoundStatus
canonicalNSLowBandBoundStatus =
  lerayBandBoundAppliedToLowModes
  ∷ finiteLowBandSumRecorded
  ∷ viscosityCutoffBoundRecorded
  ∷ noClayOrGlobalTerminalPromotion
  ∷ []

data NSLowBandBoundPromotion : Set where

nsLowBandBoundPromotionImpossibleHere :
  NSLowBandBoundPromotion →
  ⊥
nsLowBandBoundPromotionImpossibleHere ()

lowBandBoundFormula : String
lowBandBoundFormula =
  "For j <= j_nu, e_j = p^(11j/4) a_j <= p^(11j/4) M_0^2 by the Leray band bound; E_low = sum_{j=0}^{j_nu} e_j <= M_0^2 * (p^(11(j_nu+1)/4) - 1) / (p^(11/4) - 1), finite for j_nu < infinity and hence for any nu > 0; using p^j_nu <= C/nu, E_low <= M_0^2 * (C/nu)^(11/4) / (p^(11/4) - 1)."

lowBandBoundStatement : String
lowBandBoundStatement =
  "The low-band energy sum is finitely bounded for every positive viscosity cutoff nu by the Leray band bound and the finite geometric sum up to j_nu."

record NSLowBandBoundReceipt : Setω where
  field
    status :
      List NSLowBandBoundStatus

    statusIsCanonical :
      status ≡ canonicalNSLowBandBoundStatus

    lowBandBound :
      String

    lowBandBoundIsCanonical :
      lowBandBound ≡ lowBandBoundFormula

    pointwiseLowBandEnergyBoundRecorded :
      Bool

    pointwiseLowBandEnergyBoundRecordedIsTrue :
      pointwiseLowBandEnergyBoundRecorded ≡ true

    lowBandGeometricSumBoundRecorded :
      Bool

    lowBandGeometricSumBoundRecordedIsTrue :
      lowBandGeometricSumBoundRecorded ≡ true

    viscosityCutoffSubstitutionRecorded :
      Bool

    viscosityCutoffSubstitutionRecordedIsTrue :
      viscosityCutoffSubstitutionRecorded ≡ true

    finiteForAllNuGreaterThanZero :
      Bool

    finiteForAllNuGreaterThanZeroIsTrue :
      finiteForAllNuGreaterThanZero ≡ true

    usesLerayBandBound :
      Bool

    usesLerayBandBoundIsTrue :
      usesLerayBandBound ≡ true

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ lowBandBoundStatement

    promotionFlags :
      List NSLowBandBoundPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSLowBandBoundReceipt public

canonicalNSLowBandBoundReceipt :
  NSLowBandBoundReceipt
canonicalNSLowBandBoundReceipt =
  record
    { status =
        canonicalNSLowBandBoundStatus
    ; statusIsCanonical =
        refl
    ; lowBandBound =
        lowBandBoundFormula
    ; lowBandBoundIsCanonical =
        refl
    ; pointwiseLowBandEnergyBoundRecorded =
        true
    ; pointwiseLowBandEnergyBoundRecordedIsTrue =
        refl
    ; lowBandGeometricSumBoundRecorded =
        true
    ; lowBandGeometricSumBoundRecordedIsTrue =
        refl
    ; viscosityCutoffSubstitutionRecorded =
        true
    ; viscosityCutoffSubstitutionRecordedIsTrue =
        refl
    ; finiteForAllNuGreaterThanZero =
        true
    ; finiteForAllNuGreaterThanZeroIsTrue =
        refl
    ; usesLerayBandBound =
        true
    ; usesLerayBandBoundIsTrue =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        lowBandBoundStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Only the low-band range j <= j_nu is bounded here"
        ∷ "The pointwise input is e_j = p^(11j/4) a_j <= p^(11j/4) M_0^2 from the Leray band bound"
        ∷ "The finite geometric sum gives E_low <= M_0^2 * (p^(11(j_nu+1)/4) - 1) / (p^(11/4) - 1)"
        ∷ "The cutoff relation p^j_nu <= C/nu gives E_low <= M_0^2 * (C/nu)^(11/4) / (p^(11/4) - 1)"
        ∷ "This receipt records finiteForAllNuGreaterThanZero=true and usesLerayBandBound=true"
        ∷ "No Clay/global terminal promotion is made"
        ∷ []
    }

lowBandBoundFormulaRecorded :
  lowBandBound canonicalNSLowBandBoundReceipt ≡ lowBandBoundFormula
lowBandBoundFormulaRecorded =
  refl

finiteForAllNuGreaterThanZeroTrue :
  finiteForAllNuGreaterThanZero canonicalNSLowBandBoundReceipt ≡ true
finiteForAllNuGreaterThanZeroTrue =
  refl

usesLerayBandBoundTrue :
  usesLerayBandBound canonicalNSLowBandBoundReceipt ≡ true
usesLerayBandBoundTrue =
  refl

clayNavierStokesPromotedFalse :
  clayNavierStokesPromoted canonicalNSLowBandBoundReceipt ≡ false
clayNavierStokesPromotedFalse =
  refl
