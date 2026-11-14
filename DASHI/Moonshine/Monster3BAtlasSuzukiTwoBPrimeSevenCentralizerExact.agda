module DASHI.Moonshine.Monster3BAtlasSuzukiTwoBPrimeSevenCentralizerExact where

------------------------------------------------------------------------
-- ORIGINAL AUTHORITIES / ATTRIBUTION INVARIANT
-- ATLAS of Finite Group Representations, Suz centralizer orders:
-- https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Suz/
-- Suzuki involutions 2A, 2B have centralizers 3317760, 161280.
-- ATLAS original 2.Suz:2 12D GF3 standard-generator matrices were
-- manifest-pinned by existing #1098; this module adds no new matrix root.
-- Original D4 r=m*(gmg^-1) belongs to prior #1098 source-word owner.
--
-- NEW actual finite-word calculation in SAME source matrices:
-- g = DcDCDcdC; u = r*(g^-1*r*g); t = g*u^6.
-- u^13=-I12, t^7=-I12, tr=rt.
-- Hence -t has order7 and centralizes r; g has even outer C parity.
-- The image of r in Suz has involution order2 and centralizer
-- divisible by7. Suz 2A centralizer is NOT divisible by7, so Suz 2B.
--
-- This source typing does NOT itself Agda-kernel-check 12x12 matrices.
-- Monster order4 class r=4A/4C/4D, original BW H/D_i quotient,
-- selected 6.Suz degree78 and actual Hom_E remain independently open.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

suzukiTwoACentralizerOrder : Nat
suzukiTwoACentralizerOrder = 3317760
suzukiTwoBCentralizerOrder : Nat
suzukiTwoBCentralizerOrder = 161280

suzukiTwoACentralizerHasRemainderFive :
  7 * 473965 + 5 ≡ suzukiTwoACentralizerOrder
suzukiTwoACentralizerHasRemainderFive = refl

suzukiTwoBCentralizerIsDivisibleBySeven :
  7 * 23040 ≡ suzukiTwoBCentralizerOrder
suzukiTwoBCentralizerIsDivisibleBySeven = refl

data SuzukiInvolutionClass : Set where
  twoA twoB : SuzukiInvolutionClass

-- A selected source quotient class, conditional on SOURCE MATRIX
-- certificate of an order7 element in the centralizer of bar(r).
-- Arithmetic witnesses alone are NOT a substitute for that certificate.
record SevenCentralizerSourceCertificate : Set where
  constructor sevenCentralizerSourceCertificate
  field
    originalGeneratorWord : String
    sourceRIsInnerTwoSuz : Bool
    sourceRSquareIsNegativeIdentity : Bool
    uThirteenthPowerIsNegativeIdentity : Bool
    tSeventhPowerIsNegativeIdentity : Bool
    minusTHasExactOrderSeven : Bool
    minusTCommutesWithR : Bool
    originalATLASMatrixSHA256Verified : Bool
    originalSuzukiCentralizerOrdersReused : Bool
    inferredQuotientClass : SuzukiInvolutionClass
    actualMonsterClassDetermined : Bool
    actualSelected6SuzDegree78Paid : Bool
    agdaKernelVerifiedSourceMatrices : Bool

currentSourceCertificate : SevenCentralizerSourceCertificate
currentSourceCertificate = sevenCentralizerSourceCertificate
  "DcDCDcdC"
  true true true true true true true true
  twoB
  false false false
