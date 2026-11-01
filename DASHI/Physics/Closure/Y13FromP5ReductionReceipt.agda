module DASHI.Physics.Closure.Y13FromP5ReductionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.RRY13DerivationAttempt as RR

------------------------------------------------------------------------
-- Negative diagnostic for the speculative p5-reduction y13 path.

data Y13P5ReductionStatus : Set where
  y13P5ReductionDiagnosticRecorded :
    Y13P5ReductionStatus

data Y13P5ReductionBlocker : Set where
  extraPathFormulaDoesNotMatchVub :
    Y13P5ReductionBlocker

  missingIsogenyPathMultiplicityProof :
    Y13P5ReductionBlocker

  missingPhysicalYukawaNormalisation :
    Y13P5ReductionBlocker

canonicalY13P5ReductionBlockers :
  List Y13P5ReductionBlocker
canonicalY13P5ReductionBlockers =
  extraPathFormulaDoesNotMatchVub
  ∷ missingIsogenyPathMultiplicityProof
  ∷ missingPhysicalYukawaNormalisation
  ∷ []

data Y13P5ReductionPromotion : Set where

y13P5ReductionPromotionImpossibleHere :
  Y13P5ReductionPromotion →
  ⊥
y13P5ReductionPromotionImpossibleHere ()

record Y13FromP5ReductionReceipt : Set where
  field
    status :
      Y13P5ReductionStatus

    rrAttemptReceipt :
      RR.RRY13DerivationAttemptReceipt

    rrAttemptReceiptIsCanonical :
      rrAttemptReceipt ≡ RR.canonicalRRY13DerivationAttemptReceipt

    p5ReductionFact :
      String

    jMinus3375Abs :
      Nat

    jMinus3375AbsIs3375 :
      jMinus3375Abs ≡ 3375

    p5ReductionModulus :
      Nat

    p5ReductionModulusIsFive :
      p5ReductionModulus ≡ 5

    jMinus3375Mod5Remainder :
      Nat

    jMinus3375Mod5RemainderIsZero :
      jMinus3375Mod5Remainder ≡ 0

    speculativeDegreeFormula :
      String

    speculativeExtendedDegree :
      Float

    bridgeNormalisedY13Formula :
      String

    bridgeNormalisedY13 :
      Float

    speculativeVub :
      Float

    pdgVubTarget :
      Float

    pdgOverSpeculativeVub :
      Float

    speculativeVubOverPDG :
      Float

    absoluteVubError :
      Float

    p5ReductionPathTested :
      Bool

    p5ReductionPathTestedIsTrue :
      p5ReductionPathTested ≡ true

    p5ReductionClosesVub :
      Bool

    p5ReductionClosesVubIsFalse :
      p5ReductionClosesVub ≡ false

    y13PhysicalValueDerived :
      Bool

    y13PhysicalValueDerivedIsFalse :
      y13PhysicalValueDerived ≡ false

    vubPhysicalValueDerived :
      Bool

    vubPhysicalValueDerivedIsFalse :
      vubPhysicalValueDerived ≡ false

    physicalVubPromoted :
      Bool

    physicalVubPromotedIsFalse :
      physicalVubPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List Y13P5ReductionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalY13P5ReductionBlockers

    promotionFlags :
      List Y13P5ReductionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open Y13FromP5ReductionReceipt public

canonicalY13FromP5ReductionReceipt :
  Y13FromP5ReductionReceipt
canonicalY13FromP5ReductionReceipt =
  record
    { status =
        y13P5ReductionDiagnosticRecorded
    ; rrAttemptReceipt =
        RR.canonicalRRY13DerivationAttemptReceipt
    ; rrAttemptReceiptIsCanonical =
        refl
    ; p5ReductionFact =
        "j(-3375) ≡ 0 mod 5, matching the D=-3 supersingular class over F_5"
    ; jMinus3375Abs =
        3375
    ; jMinus3375AbsIs3375 =
        refl
    ; p5ReductionModulus =
        5
    ; p5ReductionModulusIsFive =
        refl
    ; jMinus3375Mod5Remainder =
        0
    ; jMinus3375Mod5RemainderIsZero =
        refl
    ; speculativeDegreeFormula =
        "deg13 = 18 * (1 + 5*alpha1), with alpha1=0.041240"
    ; speculativeExtendedDegree =
        21.7116
    ; bridgeNormalisedY13Formula =
        "y13_p5 = deg13 * (8*pi/3)/sqrt(24)"
    ; bridgeNormalisedY13 =
        37.12827852338977
    ; speculativeVub =
        0.0026041187418619797
    ; pdgVubTarget =
        0.00369
    ; pdgOverSpeculativeVub =
        1.4169860769718976
    ; speculativeVubOverPDG =
        0.7057232389292621
    ; absoluteVubError =
        0.0010858812581380204
    ; p5ReductionPathTested =
        true
    ; p5ReductionPathTestedIsTrue =
        refl
    ; p5ReductionClosesVub =
        false
    ; p5ReductionClosesVubIsFalse =
        refl
    ; y13PhysicalValueDerived =
        false
    ; y13PhysicalValueDerivedIsFalse =
        refl
    ; vubPhysicalValueDerived =
        false
    ; vubPhysicalValueDerivedIsFalse =
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
        canonicalY13P5ReductionBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The p5 reduction records j(-3375) ≡ 0 mod 5"
        ∷ "The speculative extra p5-isomorphism path formula is deg13 = 18(1 + 5 alpha1)"
        ∷ "Using the existing p2-p5 bridge normalization gives |Vub| approximately 0.002604"
        ∷ "The PDG comparison target is approximately 0.00369, about 1.42 times larger than the diagnostic"
        ∷ "The simple extra-path degree formula undershoots |Vub| and is recorded as a negative diagnostic"
        ∷ "No physical y13, physical Vub, or CKM promotion is asserted"
        ∷ []
    }

y13P5ReductionDoesNotCloseVub :
  p5ReductionClosesVub canonicalY13FromP5ReductionReceipt ≡ false
y13P5ReductionDoesNotCloseVub =
  refl

y13P5ReductionDoesNotDerivePhysicalVub :
  vubPhysicalValueDerived canonicalY13FromP5ReductionReceipt ≡ false
y13P5ReductionDoesNotDerivePhysicalVub =
  refl

y13P5ReductionDoesNotPromoteCKM :
  physicalCKMPromoted canonicalY13FromP5ReductionReceipt ≡ false
y13P5ReductionDoesNotPromoteCKM =
  refl
