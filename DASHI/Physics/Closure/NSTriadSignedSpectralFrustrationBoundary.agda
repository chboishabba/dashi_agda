module DASHI.Physics.Closure.NSTriadSignedSpectralFrustrationBoundary where

-- Fail-closed boundary for the signed XY / spectral-frustration Wall 1a route.
--
-- This boundary records the current candidate surface only:
--   1. the signed Laplacian / signed XY floor is the primary Wall 1a candidate;
--   2. the upper spectral edge still carries XY-floor risk;
--   3. theorem, full-NS, and Clay promotion remain false;
--   4. the discrete signed-XOR distance to the continuous XY-floor bridge
--      remains open.
--
-- Nothing here proves a signed-XY floor, a spectral gap, full Navier-Stokes,
-- or any Clay promotion claim.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Route identity.

modulePath : String
modulePath =
  "DASHI/Physics/Closure/NSTriadSignedSpectralFrustrationBoundary.agda"

boundaryName : String
boundaryName =
  "NSTriadSignedSpectralFrustrationBoundary"

routeName : String
routeName =
  "signed-XY-spectral-frustration-wall-1a"

boundarySummary : String
boundarySummary =
  "Signed Laplacian / signed XY floor candidate remains open, upper spectral edge still carries XY-floor risk, and theorem/full-NS/Clay promotion stays false."

bridgeSummary : String
bridgeSummary =
  "The discrete signed-XOR distance to the continuous XY floor bridge is still open."

------------------------------------------------------------------------
-- Boundary tags and candidate markers.

data NSTriadSignedSpectralFrustrationTag : Set where
  signed-laplacian-floor-candidate :
    NSTriadSignedSpectralFrustrationTag
  signed-xy-floor-candidate :
    NSTriadSignedSpectralFrustrationTag
  upper-spectral-edge-risk :
    NSTriadSignedSpectralFrustrationTag
  theorem-promotion-held-back :
    NSTriadSignedSpectralFrustrationTag
  full-ns-promotion-held-back :
    NSTriadSignedSpectralFrustrationTag
  clay-promotion-held-back :
    NSTriadSignedSpectralFrustrationTag
  signed-xor-bridge-still-open :
    NSTriadSignedSpectralFrustrationTag

canonicalTags : List NSTriadSignedSpectralFrustrationTag
canonicalTags =
  signed-laplacian-floor-candidate
  ∷ signed-xy-floor-candidate
  ∷ upper-spectral-edge-risk
  ∷ theorem-promotion-held-back
  ∷ full-ns-promotion-held-back
  ∷ clay-promotion-held-back
  ∷ signed-xor-bridge-still-open
  ∷ []

tagCount : Bool
tagCount = true

------------------------------------------------------------------------
-- Boundary receipt.

record NSTriadSignedSpectralFrustrationBoundaryReceipt : Set where
  constructor mkNSTriadSignedSpectralFrustrationBoundaryReceipt
  field
    route :
      String
    modulePathField :
      String
    boundarySummaryField :
      String
    bridgeSummaryField :
      String
    primaryWall1aCandidate :
      Bool
    upperSpectralEdgeCarriesXYFloorRisk :
      Bool
    theoremPromoted :
      Bool
    fullNSPromoted :
      Bool
    clayPromoted :
      Bool
    signedXORDistanceBridgeOpen :
      Bool
    promotionFlags :
      List String
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open NSTriadSignedSpectralFrustrationBoundaryReceipt public

canonicalNSTriadSignedSpectralFrustrationBoundaryReceipt :
  NSTriadSignedSpectralFrustrationBoundaryReceipt
canonicalNSTriadSignedSpectralFrustrationBoundaryReceipt =
  mkNSTriadSignedSpectralFrustrationBoundaryReceipt
    routeName
    modulePath
    boundarySummary
    bridgeSummary
    true
    true
    false
    false
    false
    true
    []
    refl

------------------------------------------------------------------------
-- Contract witnesses.

primaryWall1aCandidateIsTrue :
  primaryWall1aCandidate canonicalNSTriadSignedSpectralFrustrationBoundaryReceipt ≡ true
primaryWall1aCandidateIsTrue =
  refl

upperSpectralEdgeCarriesXYFloorRiskIsTrue :
  upperSpectralEdgeCarriesXYFloorRisk canonicalNSTriadSignedSpectralFrustrationBoundaryReceipt ≡ true
upperSpectralEdgeCarriesXYFloorRiskIsTrue =
  refl

theoremPromotionIsFalse :
  theoremPromoted canonicalNSTriadSignedSpectralFrustrationBoundaryReceipt ≡ false
theoremPromotionIsFalse =
  refl

fullNSPromotionIsFalse :
  fullNSPromoted canonicalNSTriadSignedSpectralFrustrationBoundaryReceipt ≡ false
fullNSPromotionIsFalse =
  refl

clayPromotionIsFalse :
  clayPromoted canonicalNSTriadSignedSpectralFrustrationBoundaryReceipt ≡ false
clayPromotionIsFalse =
  refl

signedXORBridgeIsOpen :
  signedXORDistanceBridgeOpen canonicalNSTriadSignedSpectralFrustrationBoundaryReceipt ≡ true
signedXORBridgeIsOpen =
  refl

promotionFlagsAreEmpty :
  promotionFlags canonicalNSTriadSignedSpectralFrustrationBoundaryReceipt ≡ []
promotionFlagsAreEmpty =
  refl

------------------------------------------------------------------------
-- Public boundary statement.

boundaryStatement : String
boundaryStatement =
  "Wall 1a signed Laplacian / signed XY floor remains the primary candidate; the upper spectral edge still carries XY-floor risk; theorem, full-NS, and Clay promotion remain false; the signed-XOR bridge to the continuous XY floor remains open."

