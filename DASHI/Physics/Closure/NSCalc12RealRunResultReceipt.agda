module DASHI.Physics.Closure.NSCalc12RealRunResultReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NS Calc12 real run result receipt.
--
-- This module records the committed real-run Calc12 output as literal
-- strings only.  It is candidate-only, with no proof blocking, no theorem
-- authority, and no Clay promotion.

record NSCalc12RealRunResultReceipt : Set where
  field
    candidateOnly :
      Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true

    proofBlocking :
      Bool
    proofBlockingIsFalse :
      proofBlocking ≡ false

    theoremAuthority :
      Bool
    theoremAuthorityIsFalse :
      theoremAuthority ≡ false

    clayPromotion :
      Bool
    clayPromotionIsFalse :
      clayPromotion ≡ false

    beta :
      String
    betaIsCanonical :
      beta ≡ "2.2754974180523737"

    ciLower :
      String
    ciLowerIsCanonical :
      ciLower ≡ "2.129779448947756"

    ciUpper :
      String
    ciUpperIsCanonical :
      ciUpper ≡ "2.4212153871569915"

    rSquared :
      String
    rSquaredIsCanonical :
      rSquared ≡ "0.13893110418597066"

    decision :
      String
    decisionIsCanonical :
      decision ≡ "regularity_consistent"

    nPairsUsed :
      String
    nPairsUsedIsCanonical :
      nPairsUsed ≡ "5808"

    artifactPath :
      String
    artifactPathIsCanonical :
      artifactPath
      ≡ "scripts/data/outputs/ns_clay_calc12_route_selector_real_N128_20260619.json"

open NSCalc12RealRunResultReceipt public

canonicalNSCalc12RealRunResultReceipt :
  NSCalc12RealRunResultReceipt
canonicalNSCalc12RealRunResultReceipt =
  record
    { candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    ; proofBlocking =
        false
    ; proofBlockingIsFalse =
        refl
    ; theoremAuthority =
        false
    ; theoremAuthorityIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; beta =
        "2.2754974180523737"
    ; betaIsCanonical =
        refl
    ; ciLower =
        "2.129779448947756"
    ; ciLowerIsCanonical =
        refl
    ; ciUpper =
        "2.4212153871569915"
    ; ciUpperIsCanonical =
        refl
    ; rSquared =
        "0.13893110418597066"
    ; rSquaredIsCanonical =
        refl
    ; decision =
        "regularity_consistent"
    ; decisionIsCanonical =
        refl
    ; nPairsUsed =
        "5808"
    ; nPairsUsedIsCanonical =
        refl
    ; artifactPath =
        "scripts/data/outputs/ns_clay_calc12_route_selector_real_N128_20260619.json"
    ; artifactPathIsCanonical =
        refl
    }
