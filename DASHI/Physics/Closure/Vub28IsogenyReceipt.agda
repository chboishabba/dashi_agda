module DASHI.Physics.Closure.Vub28IsogenyReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Y13AlternativeFormulasReceipt as Y13

------------------------------------------------------------------------
-- Degree-28 compositum diagnostic for |V_ub|.

data Vub28Status : Set where
  vubDegreeTwentyEightDiagnosticRecorded :
    Vub28Status

data Vub28Blocker : Set where
  degreeTwentyEightIsCompositumHypothesis :
    Vub28Blocker

  nloQcdCorrectionNotCarrierDerived :
    Vub28Blocker

  physicalVubAuthorityNotBound :
    Vub28Blocker

canonicalVub28Blockers : List Vub28Blocker
canonicalVub28Blockers =
  degreeTwentyEightIsCompositumHypothesis
  ∷ nloQcdCorrectionNotCarrierDerived
  ∷ physicalVubAuthorityNotBound
  ∷ []

data Vub28Promotion : Set where

vub28PromotionImpossibleHere :
  Vub28Promotion →
  ⊥
vub28PromotionImpossibleHere ()

record Vub28IsogenyReceipt : Set where
  field
    status :
      Vub28Status

    previousY13Sweep :
      Y13.Y13AlternativeFormulasReceipt

    previousY13SweepIsCanonical :
      previousY13Sweep ≡ Y13.canonicalY13AlternativeFormulasReceipt

    sourceCMRing :
      String

    targetCMRing :
      String

    compositumField :
      String

    degreeTwentyEightExplanation :
      String

    directDegree :
      Nat

    alpha1 :
      Float

    alpha1Cubed :
      Float

    geometricDenominator :
      Float

    y13Degree28NoResummation :
      Float

    vubDegree28NoResummation :
      Float

    y13Degree28Geometric :
      Float

    vubDegree28Geometric :
      Float

    pdgVubReference :
      Float

    vubDegree28GeometricRelativeError :
      Float

    alphaStrongAtMb :
      Float

    alphaStrongOverPi :
      Float

    vubDegree28WithNLOQCD :
      Float

    vubDegree28NLORelativeError :
      Float

    vubNLOCorrectionHypothesis :
      Bool

    vubNLOCorrectionHypothesisIsTrue :
      vubNLOCorrectionHypothesis ≡ true

    nloQcdCorrectionCarrierDerived :
      Bool

    nloQcdCorrectionCarrierDerivedIsFalse :
      nloQcdCorrectionCarrierDerived ≡ false

    physicalVubPromoted :
      Bool

    physicalVubPromotedIsFalse :
      physicalVubPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List Vub28Blocker

    blockersAreCanonical :
      blockers ≡ canonicalVub28Blockers

    promotionFlags :
      List Vub28Promotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open Vub28IsogenyReceipt public

canonicalVub28IsogenyReceipt :
  Vub28IsogenyReceipt
canonicalVub28IsogenyReceipt =
  record
    { status =
        vubDegreeTwentyEightDiagnosticRecorded
    ; previousY13Sweep =
        Y13.canonicalY13AlternativeFormulasReceipt
    ; previousY13SweepIsCanonical =
        refl
    ; sourceCMRing =
        "Z[i], D=-4, j=1728"
    ; targetCMRing =
        "Z[(1+sqrt(-7))/2], D=-7, j=-3375"
    ; compositumField =
        "Q(i,sqrt(-7))"
    ; degreeTwentyEightExplanation =
        "lcm(4,7)=28 as a compositum/norm diagnostic, not a proved physical isogeny"
    ; directDegree =
        28
    ; alpha1 =
        0.041240
    ; alpha1Cubed =
        0.000070151814464
    ; geometricDenominator =
        0.97938
    ; y13Degree28NoResummation =
        47.88141588159849
    ; vubDegree28NoResummation =
        0.003359365905360842
    ; y13Degree28Geometric =
        48.88951062506585
    ; vubDegree28Geometric =
        0.003430064354130741
    ; pdgVubReference =
        0.00369
    ; vubDegree28GeometricRelativeError =
        -0.07044223600806501
    ; alphaStrongAtMb =
        0.2275
    ; alphaStrongOverPi =
        0.0724
    ; vubDegree28WithNLOQCD =
        0.003678001014969407
    ; vubDegree28NLORelativeError =
        -0.003251757461948024
    ; vubNLOCorrectionHypothesis =
        true
    ; vubNLOCorrectionHypothesisIsTrue =
        refl
    ; nloQcdCorrectionCarrierDerived =
        false
    ; nloQcdCorrectionCarrierDerivedIsFalse =
        refl
    ; physicalVubPromoted =
        false
    ; physicalVubPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalVub28Blockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The degree-28 route improves the Vub diagnostic but is not a derivation"
        ∷ "The NLO QCD factor uses an external alpha_s-sized correction and is not carrier-derived"
        ∷ "No physical Vub or CKM promotion is asserted"
        ∷ []
    }

vub28DoesNotPromoteVub :
  physicalVubPromoted canonicalVub28IsogenyReceipt ≡ false
vub28DoesNotPromoteVub =
  refl

