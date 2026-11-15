module DASHI.Moonshine.OggSSPClimbingGymRigorousCertificateExact where

------------------------------------------------------------------------
-- EXTERNAL RIGOROUS ENCLOSURE -> KERNEL-CHECKED NATIVE OGG RADIX CELL
--
-- This is the intended producer/checker seam for the next climbing-gym phase.
-- An external ball-arithmetic program may isolate a numbered zeta zero and
-- propagate it through
--
--   x_p(t) = frac(t log(p) / (2*pi)).
--
-- The external producer records exact dyadic enclosures.  DASHI does not trust
-- a label such as "FLINT" as proof.  Instead, the finite consumer accepts only
-- a `CertifiedDyadicRadixCell`, whose cell inequalities are explicit Nat
-- propositions checked by Agda.
--
-- This establishes the implication
--
--   supplied phase enclosure lies wholly in cell j
--     -> native p-radix address is j,
--
-- while keeping the upstream statement
--
--   supplied enclosure really contains the n-th zeta-zero phase
--
-- as separately attributed external numerical authority unless and until a
-- formal same-object enclosure theorem is imported/reconstructed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.DyadicPhaseCellCertificateExact as Dyadic
import DASHI.Foundations.RadixValuationStageBridge as Radix
import DASHI.Moonshine.OggSSPSignedRadixClimbingGymExact as Gym

record ExternalRigorousPhaseEnclosure
    (form : Gym.WallForm) : Set where
  constructor external-rigorous-phase-enclosure
  field
    zeroIndex : Nat
    zeroOrdinateInterval : Dyadic.DyadicInterval
    phaseInterval : Dyadic.DyadicInterval

    producerName : String
    producerVersion : String
    producerMethod : String
    artifactHash : String

    producerClaimsNthZeroIsolation : Bool
    producerClaimsUniqueZeroInOrdinateInterval : Bool
    producerClaimsBallArithmeticPhaseContainment : Bool

    -- Source/provenance assertions are metadata.  They are intentionally not
    -- proof fields equating the interval with an analytic zeta-zero object.
    producerReceiptIsExternal : Bool

open ExternalRigorousPhaseEnclosure public

record CheckedRigorousWallCertificate
    (form : Gym.WallForm) : Set where
  constructor checked-rigorous-wall-certificate
  field
    externalEnclosure : ExternalRigorousPhaseEnclosure form
    checkedCell :
      Dyadic.CertifiedDyadicRadixCell
        (Gym.oggPrimeRadixChart (Gym.formLane form))
        (Gym.formExponent form)
        (phaseInterval externalEnclosure)

open CheckedRigorousWallCertificate public

checkedWallAddress :
  ∀ {form} →
  CheckedRigorousWallCertificate form →
  Radix.RadialTreeAddress
    (Gym.oggPrimeRadixChart (Gym.formLane form))
    (Gym.formExponent form)
checkedWallAddress certificate =
  Dyadic.certifiedRadialAddress (checkedCell certificate)

checkedWallCellIndex :
  ∀ {form} →
  CheckedRigorousWallCertificate form → Nat
checkedWallCellIndex certificate =
  Dyadic.cellIndex (checkedCell certificate)

------------------------------------------------------------------------
-- Producer-bundle status and claim boundary.
------------------------------------------------------------------------

record RigorousClimbingGymCertificateBoundary : Set where
  constructor rigorous-climbing-gym-certificate-boundary
  field
    exactDyadicProducerSchemaDefined : Bool
    externalZeroAndPhaseIntervalsSeparated : Bool
    nativeRadixCellArithmeticKernelChecked : Bool
    existingOggWallChartReused : Bool
    totalConstructiveRealFloorAvoided : Bool

    externalRigorousProducerIsAgdaKernelProof : Bool
    producerLabelAloneCreatesEnclosureTruth : Bool
    certifiedPhaseCellProvesInputIsZetaZero : Bool
    certifiedPhaseCellProvesRiemannHypothesis : Bool
    certifiedPhaseCellProvesMonsterSpecificity : Bool
    sourceRandomShiftSeedRecovered : Bool

open RigorousClimbingGymCertificateBoundary public

canonicalRigorousClimbingGymCertificateBoundary :
  RigorousClimbingGymCertificateBoundary
canonicalRigorousClimbingGymCertificateBoundary =
  rigorous-climbing-gym-certificate-boundary
    true true true true true
    false false false false false false
