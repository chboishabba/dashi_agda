module DASHI.Physics.Closure.ClayBlockerUpdateReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayBothBlockerMapReceipt as Prior
import DASHI.Physics.Closure.MultiBaseWaveletCompactnessReceipt as MultiBase
import DASHI.Physics.Closure.OSPositivityCorrectObjectReceipt as OSObject
import DASHI.Physics.Closure.RGOperatorNormFormalProof as RGProof

data UpdatedYangMillsBlocker : Set where
  su3GaugeIdentificationOpen : UpdatedYangMillsBlocker
  continuumRGConvergenceOpen : UpdatedYangMillsBlocker

canonicalUpdatedYangMillsBlockers : List UpdatedYangMillsBlocker
canonicalUpdatedYangMillsBlockers =
  su3GaugeIdentificationOpen
  ∷ continuumRGConvergenceOpen
  ∷ []

data UpdatedNavierStokesBlocker : Set where
  multiBaseRieszWaveletBridgeOpen : UpdatedNavierStokesBlocker
  nonlinearTermPassageOpen : UpdatedNavierStokesBlocker

canonicalUpdatedNavierStokesBlockers : List UpdatedNavierStokesBlocker
canonicalUpdatedNavierStokesBlockers =
  multiBaseRieszWaveletBridgeOpen
  ∷ nonlinearTermPassageOpen
  ∷ []

updatedYMStatement : String
updatedYMStatement =
  "Updated YM blocker: Clay YM now reduces to SU3/gauge identification plus continuum RG convergence; scalar OS is dissolved only for the scalar sector."

updatedNSStatement : String
updatedNSStatement =
  "Updated NS blocker: Clay NS now reduces to the multi-base Riesz/wavelet bridge plus nonlinear term passage."

record ClayBlockerUpdateReceipt : Setω where
  field
    priorBlockerMap :
      Prior.ClayBothBlockerMapReceipt

    priorClayFlagsFalse :
      Prior.bothClayProblemsClosed priorBlockerMap ≡ false

    rgOperatorNormFormalProof :
      RGProof.RGOperatorNormFormalProofReceipt

    normalizedRGContractionRecorded :
      RGProof.rgContractionForNormalizedMap rgOperatorNormFormalProof
      ≡
      true

    osCorrectObjectReceipt :
      OSObject.OSPositivityCorrectObjectReceipt

    scalarOSSubBlockerDissolved :
      OSObject.osPositivityForScalarSector osCorrectObjectReceipt ≡ true

    fullOSStillOpen :
      OSObject.fullOSPositivityInhabited osCorrectObjectReceipt ≡ false

    multiBaseWaveletReceipt :
      MultiBase.MultiBaseWaveletCompactnessReceipt

    multiBaseBridgeCandidateRecorded :
      MultiBase.padicToArchimedeanBridgeCandidate multiBaseWaveletReceipt
      ≡
      true

    archimedeanCompactnessStillOpen :
      MultiBase.archimedeanCompactnessPromoted multiBaseWaveletReceipt
      ≡
      false

    yangMillsBlockers :
      List UpdatedYangMillsBlocker

    yangMillsBlockersAreCanonical :
      yangMillsBlockers ≡ canonicalUpdatedYangMillsBlockers

    navierStokesBlockers :
      List UpdatedNavierStokesBlocker

    navierStokesBlockersAreCanonical :
      navierStokesBlockers ≡ canonicalUpdatedNavierStokesBlockers

    ymStatement :
      String

    ymStatementIsCanonical :
      ymStatement ≡ updatedYMStatement

    nsStatement :
      String

    nsStatementIsCanonical :
      nsStatement ≡ updatedNSStatement

    yangMillsMassGapClayPromoted :
      Bool

    yangMillsMassGapClayPromotedIsFalse :
      yangMillsMassGapClayPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    receiptBoundary :
      List String

open ClayBlockerUpdateReceipt public

canonicalClayBlockerUpdateReceipt : ClayBlockerUpdateReceipt
canonicalClayBlockerUpdateReceipt =
  record
    { priorBlockerMap =
        Prior.canonicalClayBothBlockerMapReceipt
    ; priorClayFlagsFalse =
        refl
    ; rgOperatorNormFormalProof =
        RGProof.canonicalRGOperatorNormFormalProofReceipt
    ; normalizedRGContractionRecorded =
        refl
    ; osCorrectObjectReceipt =
        OSObject.canonicalOSPositivityCorrectObjectReceipt
    ; scalarOSSubBlockerDissolved =
        refl
    ; fullOSStillOpen =
        refl
    ; multiBaseWaveletReceipt =
        MultiBase.canonicalMultiBaseWaveletCompactnessReceipt
    ; multiBaseBridgeCandidateRecorded =
        refl
    ; archimedeanCompactnessStillOpen =
        refl
    ; yangMillsBlockers =
        canonicalUpdatedYangMillsBlockers
    ; yangMillsBlockersAreCanonical =
        refl
    ; navierStokesBlockers =
        canonicalUpdatedNavierStokesBlockers
    ; navierStokesBlockersAreCanonical =
        refl
    ; ymStatement =
        updatedYMStatement
    ; ymStatementIsCanonical =
        refl
    ; nsStatement =
        updatedNSStatement
    ; nsStatementIsCanonical =
        refl
    ; yangMillsMassGapClayPromoted =
        false
    ; yangMillsMassGapClayPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; receiptBoundary =
        "The Clay blocker map is refined, not promoted"
        ∷ "Scalar-sector OS positivity is recorded only for the correct finite scalar transfer object"
        ∷ "YM still needs SU3/gauge identification and continuum RG convergence"
        ∷ "NS still needs the multi-base Riesz/wavelet bridge and nonlinear term passage"
        ∷ []
    }

clayBlockerUpdateKeepsClayFalse :
  terminalClayClaimPromoted canonicalClayBlockerUpdateReceipt ≡ false
clayBlockerUpdateKeepsClayFalse =
  refl

clayBlockerUpdateKeepsYangMillsClayFalse :
  yangMillsMassGapClayPromoted canonicalClayBlockerUpdateReceipt ≡ false
clayBlockerUpdateKeepsYangMillsClayFalse =
  refl

clayBlockerUpdateKeepsNavierStokesClayFalse :
  clayNavierStokesPromoted canonicalClayBlockerUpdateReceipt ≡ false
clayBlockerUpdateKeepsNavierStokesClayFalse =
  refl

clayBlockerUpdateKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalClayBlockerUpdateReceipt ≡ false
clayBlockerUpdateKeepsTerminalFalse =
  refl
