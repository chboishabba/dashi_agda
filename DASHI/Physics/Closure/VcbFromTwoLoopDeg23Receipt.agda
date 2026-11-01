module DASHI.Physics.Closure.VcbFromTwoLoopDeg23Receipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.TwoLoopResummationReceipt as TwoLoop

vcbTwoLoopStatement : String
vcbTwoLoopStatement =
  "The two-loop deg23 diagnostic makes the effective degree nearly 14.302, but Vcb remains about 1.9 percent high; the dominant issue is Yukawa normalisation."

record VcbFromTwoLoopDeg23Receipt : Setω where
  field
    twoLoopReceipt :
      TwoLoop.TwoLoopResummationReceipt

    twoLoopCandidateRecorded :
      TwoLoop.deg23TwoLoopFormulaCandidate twoLoopReceipt ≡ true

    vcbPredictionPPM :
      Nat

    vcbPredictionPPMIsAbout41590 :
      vcbPredictionPPM ≡ 41590

    pdgReferencePPM :
      Nat

    pdgReferencePPMIsAbout40800 :
      pdgReferencePPM ≡ 40800

    vcbRelativeErrorPPM :
      Nat

    vcbRelativeErrorPPMIsAbout19300 :
      vcbRelativeErrorPPM ≡ 19300

    vcbErrorNotFromDeg23 :
      Bool

    vcbErrorNotFromDeg23IsTrue :
      vcbErrorNotFromDeg23 ≡ true

    normalisationProblemDominates :
      Bool

    normalisationProblemDominatesIsTrue :
      normalisationProblemDominates ≡ true

    physicalVcbPromoted :
      Bool

    physicalVcbPromotedIsFalse :
      physicalVcbPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ vcbTwoLoopStatement

open VcbFromTwoLoopDeg23Receipt public

canonicalVcbFromTwoLoopDeg23Receipt :
  VcbFromTwoLoopDeg23Receipt
canonicalVcbFromTwoLoopDeg23Receipt =
  record
    { twoLoopReceipt =
        TwoLoop.canonicalTwoLoopResummationReceipt
    ; twoLoopCandidateRecorded =
        refl
    ; vcbPredictionPPM =
        41590
    ; vcbPredictionPPMIsAbout41590 =
        refl
    ; pdgReferencePPM =
        40800
    ; pdgReferencePPMIsAbout40800 =
        refl
    ; vcbRelativeErrorPPM =
        19300
    ; vcbRelativeErrorPPMIsAbout19300 =
        refl
    ; vcbErrorNotFromDeg23 =
        true
    ; vcbErrorNotFromDeg23IsTrue =
        refl
    ; normalisationProblemDominates =
        true
    ; normalisationProblemDominatesIsTrue =
        refl
    ; physicalVcbPromoted =
        false
    ; physicalVcbPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; statement =
        vcbTwoLoopStatement
    ; statementIsCanonical =
        refl
    }
