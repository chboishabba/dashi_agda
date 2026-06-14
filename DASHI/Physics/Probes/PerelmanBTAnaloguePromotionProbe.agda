module DASHI.Physics.Probes.PerelmanBTAnaloguePromotionProbe where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.PerelmanBTGeometrizationAnalogueIndex as Index
import DASHI.Physics.Closure.PerelmanRicciFlowAndGeometrizationBoundaryReceipt as Boundary

------------------------------------------------------------------------
-- Regression guard for the Perelman/BT analogue boundary.
--
-- The probe is intentionally green: it typechecks only while the available
-- Perelman/BT evidence remains discrete/analogue and the smooth authority
-- sockets remain non-promoting.

data PerelmanBTAnaloguePromotionToken : Set where

perelmanBTAnaloguePromotionTokenUnavailableHere :
  PerelmanBTAnaloguePromotionToken →
  Index.⊥
perelmanBTAnaloguePromotionTokenUnavailableHere ()

perelmanBTAnaloguePromotionProbePath : String
perelmanBTAnaloguePromotionProbePath =
  "DASHI.Physics.Probes.PerelmanBTAnaloguePromotionProbe"

perelmanBTAnaloguePromotionProbeInterpretation : String
perelmanBTAnaloguePromotionProbeInterpretation =
  "Green regression guard: the BT analogue rows remain constructible bookkeeping, while smooth Ricci-flow, Perelman monotonicity, surgery, JSJ, geometrization, and Clay authority stay unavailable."

canonicalPerelmanBTAnaloguePromotionProbeBoundary :
  List String
canonicalPerelmanBTAnaloguePromotionProbeBoundary =
  "Imports the Perelman/BT analogue index and Ricci-flow/geometrization boundary receipt"
  ∷ "Confirms the nine smooth authority blocker rows remain canonical and non-promoting"
  ∷ "Confirms the boundary receipt keeps smooth authority sockets unavailable"
  ∷ "Introduces no promotion token"
  ∷ []

record PerelmanBTAnaloguePromotionProbeReceipt : Setω where
  field
    probePath :
      String

    probePathIsCanonical :
      probePath ≡ perelmanBTAnaloguePromotionProbePath

    analogueIndex :
      Index.PerelmanBTGeometrizationAnalogueIndex

    boundaryReceipt :
      Boundary.PerelmanRicciFlowAndGeometrizationBoundaryReceipt

    smoothAuthorityBlockers :
      List Index.SmoothAuthorityBlockerRow

    smoothAuthorityBlockersAreCanonical :
      smoothAuthorityBlockers ≡ Index.canonicalSmoothAuthorityBlockerRows

    smoothAuthorityBlockerCount :
      Nat

    smoothAuthorityBlockerCountIs9 :
      smoothAuthorityBlockerCount ≡ 9

    smoothAuthorityBlockerCountMatchesRows :
      smoothAuthorityBlockerCount
      ≡
      Index.listLength smoothAuthorityBlockers

    smoothRicciFlowBlockerNotPromoted :
      Index.promoted
        (Index.mkSmoothAuthorityBlockerRow
          Index.noSmoothRicciFlowAuthority)
      ≡
      false

    perelmanMonotonicityBlockerNotPromoted :
      Index.promoted
        (Index.mkSmoothAuthorityBlockerRow
          Index.noPerelmanMonotonicityAuthority)
      ≡
      false

    smoothS2NeckBlockerNotPromoted :
      Index.promoted
        (Index.mkSmoothAuthorityBlockerRow
          Index.noSmoothS2NeckAuthority)
      ≡
      false

    canonicalNeighborhoodBlockerNotPromoted :
      Index.promoted
        (Index.mkSmoothAuthorityBlockerRow
          Index.noCanonicalNeighborhoodAuthority)
      ≡
      false

    surgeryContinuationBlockerNotPromoted :
      Index.promoted
        (Index.mkSmoothAuthorityBlockerRow
          Index.noSurgeryContinuationAuthority)
      ≡
      false

    jsjUniquenessBlockerNotPromoted :
      Index.promoted
        (Index.mkSmoothAuthorityBlockerRow
          Index.noJSJUniquenessAuthority)
      ≡
      false

    thurstonGeometrizationBlockerNotPromoted :
      Index.promoted
        (Index.mkSmoothAuthorityBlockerRow
          Index.noThurstonGeometrizationAuthority)
      ≡
      false

    clayPromotionBlockerNotPromoted :
      Index.promoted
        (Index.mkSmoothAuthorityBlockerRow
          Index.noClayPromotionAuthority)
      ≡
      false

    ricciFlowAuthorityUnavailable :
      Boundary.authorityAvailable
        (Boundary.smoothRicciFlowExistenceUniquenessSocket boundaryReceipt)
      ≡
      false

    perelmanMonotonicityAuthorityUnavailable :
      Boundary.authorityAvailable
        (Boundary.reducedVolumeMonotonicitySocket boundaryReceipt)
      ≡
      false

    surgeryAuthorityUnavailable :
      Boundary.authorityAvailable
        (Boundary.surgeryContinuationSocket boundaryReceipt)
      ≡
      false

    jsjAuthorityUnavailable :
      Boundary.authorityAvailable
        (Boundary.jsjDecompositionSocket boundaryReceipt)
      ≡
      false

    geometrizationAuthorityUnavailable :
      Boundary.authorityAvailable
        (Boundary.thurstonGeometrizationSocket boundaryReceipt)
      ≡
      false

    nsYmDependenceAuthorityUnavailable :
      Boundary.authorityAvailable
        (Boundary.nsYmDependenceOnPerelmanSocket boundaryReceipt)
      ≡
      false

    promotionTokens :
      List PerelmanBTAnaloguePromotionToken

    promotionTokensAreEmpty :
      promotionTokens ≡ []

    interpretation :
      String

    interpretationIsCanonical :
      interpretation ≡ perelmanBTAnaloguePromotionProbeInterpretation

    probeBoundary :
      List String

    probeBoundaryIsCanonical :
      probeBoundary ≡ canonicalPerelmanBTAnaloguePromotionProbeBoundary

open PerelmanBTAnaloguePromotionProbeReceipt public

canonicalPerelmanBTAnaloguePromotionProbeReceipt :
  PerelmanBTAnaloguePromotionProbeReceipt
canonicalPerelmanBTAnaloguePromotionProbeReceipt =
  record
    { probePath =
        perelmanBTAnaloguePromotionProbePath
    ; probePathIsCanonical =
        refl
    ; analogueIndex =
        Index.canonicalPerelmanBTGeometrizationAnalogueIndex
    ; boundaryReceipt =
        Boundary.canonicalPerelmanRicciFlowAndGeometrizationBoundaryReceipt
    ; smoothAuthorityBlockers =
        Index.smoothAuthorityBlockers
          Index.canonicalPerelmanBTGeometrizationAnalogueIndex
    ; smoothAuthorityBlockersAreCanonical =
        Index.smoothAuthorityBlockersAreCanonical
          Index.canonicalPerelmanBTGeometrizationAnalogueIndex
    ; smoothAuthorityBlockerCount =
        Index.smoothAuthorityBlockerCountField
          Index.canonicalPerelmanBTGeometrizationAnalogueIndex
    ; smoothAuthorityBlockerCountIs9 =
        Index.smoothAuthorityBlockerCountFieldIs9
          Index.canonicalPerelmanBTGeometrizationAnalogueIndex
    ; smoothAuthorityBlockerCountMatchesRows =
        Index.smoothAuthorityBlockerCountMatchesRows
          Index.canonicalPerelmanBTGeometrizationAnalogueIndex
    ; smoothRicciFlowBlockerNotPromoted =
        refl
    ; perelmanMonotonicityBlockerNotPromoted =
        refl
    ; smoothS2NeckBlockerNotPromoted =
        refl
    ; canonicalNeighborhoodBlockerNotPromoted =
        refl
    ; surgeryContinuationBlockerNotPromoted =
        refl
    ; jsjUniquenessBlockerNotPromoted =
        refl
    ; thurstonGeometrizationBlockerNotPromoted =
        refl
    ; clayPromotionBlockerNotPromoted =
        refl
    ; ricciFlowAuthorityUnavailable =
        Boundary.canonicalReceiptKeepsRicciFlowClosed
    ; perelmanMonotonicityAuthorityUnavailable =
        Boundary.canonicalReceiptKeepsPerelmanMonotonicityClosed
    ; surgeryAuthorityUnavailable =
        Boundary.canonicalReceiptKeepsSurgeryClosed
    ; jsjAuthorityUnavailable =
        Boundary.canonicalReceiptKeepsJSJClosed
    ; geometrizationAuthorityUnavailable =
        Boundary.canonicalReceiptKeepsGeometrizationClosed
    ; nsYmDependenceAuthorityUnavailable =
        Boundary.canonicalReceiptKeepsNSYMDependenceClosed
    ; promotionTokens =
        []
    ; promotionTokensAreEmpty =
        refl
    ; interpretation =
        perelmanBTAnaloguePromotionProbeInterpretation
    ; interpretationIsCanonical =
        refl
    ; probeBoundary =
        canonicalPerelmanBTAnaloguePromotionProbeBoundary
    ; probeBoundaryIsCanonical =
        refl
    }

perelmanBTAnaloguePromotionProbeNoPromotion :
  PerelmanBTAnaloguePromotionToken →
  Index.⊥
perelmanBTAnaloguePromotionProbeNoPromotion =
  perelmanBTAnaloguePromotionTokenUnavailableHere
