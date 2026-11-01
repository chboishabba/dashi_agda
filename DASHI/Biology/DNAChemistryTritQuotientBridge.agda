module DASHI.Biology.DNAChemistryTritQuotientBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.DNAChemistryCarrier as DNA
import DASHI.Biology.DNAChemistryHamiltonianBoundary as Chem
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Geometry.DNAFourAdicSheetLift as Lift

------------------------------------------------------------------------
-- Ternary quotient bridge.
--
-- Ternary is not imposed as the DNA alphabet.  CAGT remains the exact carrier.
-- The SSP trit is used only as a signed quotient coordinate for sheet residuals
-- and chemistry-margin classes: negative, neutral, positive.  This preserves
-- the existing DASHI trit/involution spine without claiming that every valid
-- DNA branch has arity three or that trits alone reconstruct base identity.

data ChemistryMargin : Set where
  negativeMargin : ChemistryMargin
  neutralMargin : ChemistryMargin
  positiveMargin : ChemistryMargin

marginToTrit : ChemistryMargin → SSP.SSPTrit
marginToTrit negativeMargin = SSP.sspNegOne
marginToTrit neutralMargin = SSP.sspZero
marginToTrit positiveMargin = SSP.sspPosOne

tritToMargin : SSP.SSPTrit → ChemistryMargin
tritToMargin SSP.sspNegOne = negativeMargin
tritToMargin SSP.sspZero = neutralMargin
tritToMargin SSP.sspPosOne = positiveMargin

margin-roundtrip :
  ∀ m → tritToMargin (marginToTrit m) ≡ m
margin-roundtrip negativeMargin = refl
margin-roundtrip neutralMargin = refl
margin-roundtrip positiveMargin = refl

trit-roundtrip :
  ∀ t → marginToTrit (tritToMargin t) ≡ t
trit-roundtrip SSP.sspNegOne = refl
trit-roundtrip SSP.sspZero = refl
trit-roundtrip SSP.sspPosOne = refl

------------------------------------------------------------------------
-- Sheet quotient coordinate.

record ChemistrySheetTrit : Set where
  constructor mkChemistrySheetTrit
  field
    rank : Lift.FourLiftRank
    channel : Chem.SheetChannel
    margin : ChemistryMargin
    trit : SSP.SSPTrit
    tritMatchesMargin : trit ≡ marginToTrit margin
    preservesBaseIdentity : Bool
    isCompleteChemistryCoordinate : Bool

open ChemistrySheetTrit public

canonicalUTrit : ChemistrySheetTrit
canonicalUTrit =
  mkChemistrySheetTrit
    Lift.sheetRank
    Chem.UChannel
    neutralMargin
    SSP.sspZero
    refl
    false
    false

canonicalReverseComplementTrit : ChemistrySheetTrit
canonicalReverseComplementTrit =
  mkChemistrySheetTrit
    Lift.voxelRank
    Chem.reverseComplementChannel
    positiveMargin
    SSP.sspPosOne
    refl
    false
    false

------------------------------------------------------------------------
-- Variable-arity transport boundary.
--
-- Payload transport must use the actual admissible fibre size.  The ternary
-- quotient may describe a typical three-way chemistry margin or residual sign,
-- but it must not silently discard two-way, four-way, or forced transitions.

data AdmissibleFibreArity : Set where
  forcedArity : AdmissibleFibreArity
  twoWayArity : AdmissibleFibreArity
  threeWayArity : AdmissibleFibreArity
  fourWayArity : AdmissibleFibreArity

record DNAEncodingTransportBoundary : Set where
  constructor mkDNAEncodingTransportBoundary
  field
    carrierAlphabetIsCAGT : Bool
    transportUsesActualFibreArity : Bool
    ternaryMayIndexThreeWayFibre : Bool
    ternaryRequiredAtEveryStep : Bool
    entropyCoderAllowed : Bool
    tightEventsMayFeedLiftedChecks : Bool
    payloadRoundtripRequired : Bool

open DNAEncodingTransportBoundary public

canonicalDNAEncodingTransportBoundary : DNAEncodingTransportBoundary
canonicalDNAEncodingTransportBoundary =
  mkDNAEncodingTransportBoundary
    true
    true
    true
    false
    true
    true
    true

------------------------------------------------------------------------
-- Quotient scope receipt.

record DNAChemistryTritQuotientReceipt : Set where
  constructor mkDNAChemistryTritQuotientReceipt
  field
    canonicalCoordinates : List ChemistrySheetTrit
    transportBoundary : DNAEncodingTransportBoundary
    cagtRemainsPrimitiveCarrier : Bool
    tritIsSignedSheetCoordinate : Bool
    tritIsExactBaseEncoding : Bool
    variableArityIsPreserved : Bool
    chemistryQuotientApproximationOnly : Bool
    quotientBridgeHolds : Bool
    quotientBridgeHoldsIsTrue : quotientBridgeHolds ≡ true

open DNAChemistryTritQuotientReceipt public

canonicalDNAChemistryTritQuotientReceipt :
  DNAChemistryTritQuotientReceipt
canonicalDNAChemistryTritQuotientReceipt =
  mkDNAChemistryTritQuotientReceipt
    (canonicalUTrit ∷ canonicalReverseComplementTrit ∷ [])
    canonicalDNAEncodingTransportBoundary
    true
    true
    false
    true
    true
    true
    refl
