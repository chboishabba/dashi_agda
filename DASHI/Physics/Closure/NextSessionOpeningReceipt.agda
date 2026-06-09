module DASHI.Physics.Closure.NextSessionOpeningReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Next-session opening problems.
--
-- This receipt records the three concrete computations that should open the
-- next research session.  It is an agenda receipt only.

data NextOpeningProblem : Set where
  deg23CMCorrectionToT13 :
    NextOpeningProblem

  wMassCarrierRGFactor :
    NextOpeningProblem

  su2su3LevelRankDecoupling :
    NextOpeningProblem

canonicalNextOpeningProblems :
  List NextOpeningProblem
canonicalNextOpeningProblems =
  deg23CMCorrectionToT13
  ∷ wMassCarrierRGFactor
  ∷ su2su3LevelRankDecoupling
  ∷ []

deg23OpeningStatement : String
deg23OpeningStatement =
  "Compute the splitting of 13 in Q(sqrt(-3)), Q(sqrt(-7)), and the biquadratic CM field, then compute the CM-specialised T13 Hecke degree at the joint CM point."

wMassOpeningStatement : String
wMassOpeningStatement =
  "Test whether the naive WZW W-mass overshoot factor near e is a carrier RG effect or a numerical coincidence; the Planck-to-electroweak e-fold count is not one."

levelRankOpeningStatement : String
levelRankOpeningStatement =
  "Find a formal mechanism by which SU(2)_3 <-> SU(3)_1 level-rank duality decouples into independent low-energy SU(2)_L and SU(3)_c factors in 3+1D fermionic matter."

data NextSessionOpeningPromotion : Set where

nextSessionOpeningPromotionImpossibleHere :
  NextSessionOpeningPromotion →
  ⊥
nextSessionOpeningPromotionImpossibleHere ()

record NextSessionOpeningReceipt : Setω where
  field
    problems :
      List NextOpeningProblem

    problemsAreCanonical :
      problems ≡ canonicalNextOpeningProblems

    deg23ProblemRecorded :
      Bool

    deg23ProblemRecordedIsTrue :
      deg23ProblemRecorded ≡ true

    deg23ProblemStatement :
      String

    deg23ProblemStatementIsCanonical :
      deg23ProblemStatement ≡ deg23OpeningStatement

    wMassProblemRecorded :
      Bool

    wMassProblemRecordedIsTrue :
      wMassProblemRecorded ≡ true

    wMassProblemStatement :
      String

    wMassProblemStatementIsCanonical :
      wMassProblemStatement ≡ wMassOpeningStatement

    levelRankProblemRecorded :
      Bool

    levelRankProblemRecordedIsTrue :
      levelRankProblemRecorded ≡ true

    levelRankProblemStatement :
      String

    levelRankProblemStatementIsCanonical :
      levelRankProblemStatement ≡ levelRankOpeningStatement

    deg23ResidualSolved :
      Bool

    deg23ResidualSolvedIsFalse :
      deg23ResidualSolved ≡ false

    wMassDerivedFromCarrier :
      Bool

    wMassDerivedFromCarrierIsFalse :
      wMassDerivedFromCarrier ≡ false

    su2su3DecouplingDerived :
      Bool

    su2su3DecouplingDerivedIsFalse :
      su2su3DecouplingDerived ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    promotionFlags :
      List NextSessionOpeningPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open NextSessionOpeningReceipt public

canonicalNextSessionOpeningReceipt :
  NextSessionOpeningReceipt
canonicalNextSessionOpeningReceipt =
  record
    { problems =
        canonicalNextOpeningProblems
    ; problemsAreCanonical =
        refl
    ; deg23ProblemRecorded =
        true
    ; deg23ProblemRecordedIsTrue =
        refl
    ; deg23ProblemStatement =
        deg23OpeningStatement
    ; deg23ProblemStatementIsCanonical =
        refl
    ; wMassProblemRecorded =
        true
    ; wMassProblemRecordedIsTrue =
        refl
    ; wMassProblemStatement =
        wMassOpeningStatement
    ; wMassProblemStatementIsCanonical =
        refl
    ; levelRankProblemRecorded =
        true
    ; levelRankProblemRecordedIsTrue =
        refl
    ; levelRankProblemStatement =
        levelRankOpeningStatement
    ; levelRankProblemStatementIsCanonical =
        refl
    ; deg23ResidualSolved =
        false
    ; deg23ResidualSolvedIsFalse =
        refl
    ; wMassDerivedFromCarrier =
        false
    ; wMassDerivedFromCarrierIsFalse =
        refl
    ; su2su3DecouplingDerived =
        false
    ; su2su3DecouplingDerivedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

nextSessionOpeningAgendaRecorded :
  terminalClaimPromoted canonicalNextSessionOpeningReceipt
  ≡
  false
nextSessionOpeningAgendaRecorded =
  terminalClaimPromotedIsFalse canonicalNextSessionOpeningReceipt

