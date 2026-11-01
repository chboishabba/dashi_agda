module DASHI.Physics.Closure.PrimeBandLPDefinitionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSLittlewoodPaleyCarrierReceipt as LP

------------------------------------------------------------------------
-- Prime-band Littlewood-Paley definition receipt.
--
-- This receipt records the formal prime-band LP projector surface for
-- p in {2,3,5}.  A low-frequency residual is included.  Completeness is
-- recorded only because the dyadic p=2 bands cover the ordinary LP frequency
-- axis; triadic and pentadic bands are additional carrier diagnostics, not an
-- independent proof of completeness.

data PrimeBandLPDefinitionStatus : Set where
  primeBandLPProjectorsRecorded :
    PrimeBandLPDefinitionStatus

data PrimeBand : Set where
  p2Band :
    PrimeBand

  p3Band :
    PrimeBand

  p5Band :
    PrimeBand

canonicalPrimeBands :
  List PrimeBand
canonicalPrimeBands =
  p2Band
  ∷ p3Band
  ∷ p5Band
  ∷ []

data PrimeBandLPComponent : Set where
  lowFrequencyResidual :
    PrimeBandLPComponent

  dyadicProjectors :
    PrimeBandLPComponent

  triadicProjectors :
    PrimeBandLPComponent

  pentadicProjectors :
    PrimeBandLPComponent

  dyadicCompletenessCover :
    PrimeBandLPComponent

canonicalPrimeBandLPComponents :
  List PrimeBandLPComponent
canonicalPrimeBandLPComponents =
  lowFrequencyResidual
  ∷ dyadicProjectors
  ∷ triadicProjectors
  ∷ pentadicProjectors
  ∷ dyadicCompletenessCover
  ∷ []

data PrimeBandLPBlocker : Set where
  missingSmoothMultiplierConstruction :
    PrimeBandLPBlocker

  missingBesovNormEquivalenceProof :
    PrimeBandLPBlocker

  missingNonlinearNSPassage :
    PrimeBandLPBlocker

canonicalPrimeBandLPBlockers :
  List PrimeBandLPBlocker
canonicalPrimeBandLPBlockers =
  missingSmoothMultiplierConstruction
  ∷ missingBesovNormEquivalenceProof
  ∷ missingNonlinearNSPassage
  ∷ []

data PrimeBandLPPromotion : Set where

primeBandLPPromotionImpossibleHere :
  PrimeBandLPPromotion →
  ⊥
primeBandLPPromotionImpossibleHere ()

primeBandLPFormula : String
primeBandLPFormula =
  "Delta_{p,j} is the LP projector to prime band |xi| approximately p^j for p in {2,3,5}; S_0 is the low-frequency residual"

dyadicCompletenessStatement : String
dyadicCompletenessStatement =
  "Completeness is true because the dyadic p=2 bands plus S_0 cover the standard LP frequency axis"

record PrimeBandLPDefinitionReceipt : Setω where
  field
    lpCarrierReceipt :
      LP.NSLittlewoodPaleyCarrierReceipt

    lpCarrierCandidateRecorded :
      LP.carrierLPDecompositionDefined lpCarrierReceipt ≡ true

    status :
      PrimeBandLPDefinitionStatus

    primeBands :
      List PrimeBand

    primeBandsAreCanonical :
      primeBands ≡ canonicalPrimeBands

    components :
      List PrimeBandLPComponent

    componentsAreCanonical :
      components ≡ canonicalPrimeBandLPComponents

    bandCount :
      Nat

    bandCountIsThree :
      bandCount ≡ 3

    lowFrequencyResidualRecorded :
      Bool

    lowFrequencyResidualRecordedIsTrue :
      lowFrequencyResidualRecorded ≡ true

    projectorFormula :
      String

    projectorFormulaIsCanonical :
      projectorFormula ≡ primeBandLPFormula

    dyadicBandsCover :
      Bool

    dyadicBandsCoverIsTrue :
      dyadicBandsCover ≡ true

    completenessRecorded :
      Bool

    completenessRecordedIsTrue :
      completenessRecorded ≡ true

    completenessStatement :
      String

    completenessStatementIsCanonical :
      completenessStatement ≡ dyadicCompletenessStatement

    smoothMultiplierConstructionProved :
      Bool

    smoothMultiplierConstructionProvedIsFalse :
      smoothMultiplierConstructionProved ≡ false

    navierStokesRegularityPromoted :
      Bool

    navierStokesRegularityPromotedIsFalse :
      navierStokesRegularityPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    blockers :
      List PrimeBandLPBlocker

    blockersAreCanonical :
      blockers ≡ canonicalPrimeBandLPBlockers

    promotionFlags :
      List PrimeBandLPPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open PrimeBandLPDefinitionReceipt public

canonicalPrimeBandLPDefinitionReceipt :
  PrimeBandLPDefinitionReceipt
canonicalPrimeBandLPDefinitionReceipt =
  record
    { lpCarrierReceipt =
        LP.canonicalNSLittlewoodPaleyCarrierReceipt
    ; lpCarrierCandidateRecorded =
        refl
    ; status =
        primeBandLPProjectorsRecorded
    ; primeBands =
        canonicalPrimeBands
    ; primeBandsAreCanonical =
        refl
    ; components =
        canonicalPrimeBandLPComponents
    ; componentsAreCanonical =
        refl
    ; bandCount =
        3
    ; bandCountIsThree =
        refl
    ; lowFrequencyResidualRecorded =
        true
    ; lowFrequencyResidualRecordedIsTrue =
        refl
    ; projectorFormula =
        primeBandLPFormula
    ; projectorFormulaIsCanonical =
        refl
    ; dyadicBandsCover =
        true
    ; dyadicBandsCoverIsTrue =
        refl
    ; completenessRecorded =
        true
    ; completenessRecordedIsTrue =
        refl
    ; completenessStatement =
        dyadicCompletenessStatement
    ; completenessStatementIsCanonical =
        refl
    ; smoothMultiplierConstructionProved =
        false
    ; smoothMultiplierConstructionProvedIsFalse =
        refl
    ; navierStokesRegularityPromoted =
        false
    ; navierStokesRegularityPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; blockers =
        canonicalPrimeBandLPBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "B1 records prime-band LP projectors for p in {2,3,5} and a low-frequency residual"
        ∷ "Completeness is recorded because dyadic bands cover the standard LP decomposition"
        ∷ "No NS regularity or Clay promotion is asserted"
        ∷ []
    }

primeBandLPDefinitionDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalPrimeBandLPDefinitionReceipt ≡ false
primeBandLPDefinitionDoesNotPromoteClay =
  refl
