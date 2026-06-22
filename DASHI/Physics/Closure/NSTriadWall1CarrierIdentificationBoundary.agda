module DASHI.Physics.Closure.NSTriadWall1CarrierIdentificationBoundary where

-- Fail-closed boundary for the first theorem bottleneck:
-- CorrectCarrierIdentification.
--
-- This module records the current Wall 1 carrier-identification state only.
-- It says that the observed Wall 1 floor is real, but the current cycle-family,
-- raw signed-XOR, and signed-spectral carriers are insufficient on the active
-- shell extraction.  The remaining live options are a corrected discrete
-- carrier, a plaquette/packing carrier, or a direct continuous XY/operator
-- carrier.  No theorem, full-NS, or Clay promotion is recorded here.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Boundary identity.

modulePath : String
modulePath =
  "DASHI/Physics/Closure/NSTriadWall1CarrierIdentificationBoundary.agda"

boundaryName : String
boundaryName =
  "NSTriadWall1CarrierIdentificationBoundary"

routeName : String
routeName =
  "correct-carrier-identification"

boundarySummary : String
boundarySummary =
  "Observed Wall 1 floor is real, but the current cycle-family, raw signed-XOR, and signed-spectral carriers are insufficient on the active shell extraction."

remainingOptionsSummary : String
remainingOptionsSummary =
  "The remaining carrier options are a corrected discrete carrier, a plaquette/packing carrier, or a direct continuous XY/operator carrier."

------------------------------------------------------------------------
-- Canonical rows and gaps.

data NSTriadWall1CarrierIdentificationRow : Set where
  observed-wall1-floor-is-real :
    NSTriadWall1CarrierIdentificationRow
  cycle-family-carrier-insufficient :
    NSTriadWall1CarrierIdentificationRow
  raw-signed-xor-carrier-insufficient :
    NSTriadWall1CarrierIdentificationRow
  signed-spectral-carrier-insufficient :
    NSTriadWall1CarrierIdentificationRow
  corrected-discrete-carrier-remains-open :
    NSTriadWall1CarrierIdentificationRow
  plaquette-packing-carrier-remains-open :
    NSTriadWall1CarrierIdentificationRow
  continuous-xy-operator-carrier-remains-open :
    NSTriadWall1CarrierIdentificationRow
  theorem-promotion-held-back :
    NSTriadWall1CarrierIdentificationRow
  full-ns-promotion-held-back :
    NSTriadWall1CarrierIdentificationRow
  clay-promotion-held-back :
    NSTriadWall1CarrierIdentificationRow

canonicalRows : List NSTriadWall1CarrierIdentificationRow
canonicalRows =
  observed-wall1-floor-is-real
  ∷ cycle-family-carrier-insufficient
  ∷ raw-signed-xor-carrier-insufficient
  ∷ signed-spectral-carrier-insufficient
  ∷ corrected-discrete-carrier-remains-open
  ∷ plaquette-packing-carrier-remains-open
  ∷ continuous-xy-operator-carrier-remains-open
  ∷ theorem-promotion-held-back
  ∷ full-ns-promotion-held-back
  ∷ clay-promotion-held-back
  ∷ []

data NSTriadWall1CarrierIdentificationGap : Set where
  active-shell-extraction-gap :
    NSTriadWall1CarrierIdentificationGap
  corrected-discrete-carrier-gap :
    NSTriadWall1CarrierIdentificationGap
  plaquette-packing-carrier-gap :
    NSTriadWall1CarrierIdentificationGap
  continuous-xy-operator-gap :
    NSTriadWall1CarrierIdentificationGap
  signed-xor-to-continuous-xy-bridge-gap :
    NSTriadWall1CarrierIdentificationGap

canonicalGaps : List NSTriadWall1CarrierIdentificationGap
canonicalGaps =
  active-shell-extraction-gap
  ∷ corrected-discrete-carrier-gap
  ∷ plaquette-packing-carrier-gap
  ∷ continuous-xy-operator-gap
  ∷ signed-xor-to-continuous-xy-bridge-gap
  ∷ []

------------------------------------------------------------------------
-- Boundary receipt.

record NSTriadWall1CarrierIdentificationBoundaryReceipt : Set where
  constructor mkNSTriadWall1CarrierIdentificationBoundaryReceipt
  field
    o :
      String
    r :
      String
    c :
      String
    s :
      String
    l :
      String
    p :
      String
    g :
      String
    f :
      String
    controlCardSlots :
      List String
    controlCardSlotsAreCanonical :
      controlCardSlots ≡ "O" ∷ "R" ∷ "C" ∷ "S" ∷ "L" ∷ "P" ∷ "G" ∷ "F" ∷ []
    rows :
      List NSTriadWall1CarrierIdentificationRow
    rowsAreCanonical :
      rows ≡ canonicalRows
    gaps :
      List NSTriadWall1CarrierIdentificationGap
    gapsAreCanonical :
      gaps ≡ canonicalGaps
    observedWall1FloorIsReal :
      Bool
    observedWall1FloorIsRealIsTrue :
      observedWall1FloorIsReal ≡ true
    cycleFamilyCarrierSufficient :
      Bool
    cycleFamilyCarrierSufficientIsFalse :
      cycleFamilyCarrierSufficient ≡ false
    rawSignedXORCarrierSufficient :
      Bool
    rawSignedXORCarrierSufficientIsFalse :
      rawSignedXORCarrierSufficient ≡ false
    signedSpectralCarrierSufficient :
      Bool
    signedSpectralCarrierSufficientIsFalse :
      signedSpectralCarrierSufficient ≡ false
    theoremPromoted :
      Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false
    fullNSPromoted :
      Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false
    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false
    remainingOptions :
      List String
    remainingOptionsAreDeclared :
      remainingOptions ≡
      "corrected discrete carrier"
      ∷ "plaquette/packing carrier"
      ∷ "direct continuous XY/operator carrier"
      ∷ []

open NSTriadWall1CarrierIdentificationBoundaryReceipt public

canonicalNSTriadWall1CarrierIdentificationBoundaryReceipt :
  NSTriadWall1CarrierIdentificationBoundaryReceipt
canonicalNSTriadWall1CarrierIdentificationBoundaryReceipt =
  mkNSTriadWall1CarrierIdentificationBoundaryReceipt
    "correct-carrier-identification"
    "Observed Wall 1 floor is real, but the current cycle-family, raw signed-XOR, and signed-spectral carriers are insufficient on the active shell extraction."
    "DASHI/Physics/Closure/NSTriadWall1CarrierIdentificationBoundary.agda"
    "Fail-closed Wall 1 carrier-identification boundary"
    "Active shell extraction keeps the first theorem bottleneck open."
    "Wall 1 carrier identification remains candidate-only and non-promoting."
    "No theorem, full-NS, or Clay promotion follows from the current carriers."
    "The signed-XOR bridge to a continuous XY/operator carrier remains open."
    ("O" ∷ "R" ∷ "C" ∷ "S" ∷ "L" ∷ "P" ∷ "G" ∷ "F" ∷ [])
    refl
    canonicalRows
    refl
    canonicalGaps
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    ("corrected discrete carrier" ∷ "plaquette/packing carrier" ∷ "direct continuous XY/operator carrier" ∷ [])
    refl

------------------------------------------------------------------------
-- Contract witnesses.

observedWall1FloorIsRealProof :
  observedWall1FloorIsReal canonicalNSTriadWall1CarrierIdentificationBoundaryReceipt ≡ true
observedWall1FloorIsRealProof =
  refl

cycleFamilyCarrierSufficientProof :
  cycleFamilyCarrierSufficient canonicalNSTriadWall1CarrierIdentificationBoundaryReceipt ≡ false
cycleFamilyCarrierSufficientProof =
  refl

rawSignedXORCarrierSufficientProof :
  rawSignedXORCarrierSufficient canonicalNSTriadWall1CarrierIdentificationBoundaryReceipt ≡ false
rawSignedXORCarrierSufficientProof =
  refl

signedSpectralCarrierSufficientProof :
  signedSpectralCarrierSufficient canonicalNSTriadWall1CarrierIdentificationBoundaryReceipt ≡ false
signedSpectralCarrierSufficientProof =
  refl

theoremPromotedProof :
  theoremPromoted canonicalNSTriadWall1CarrierIdentificationBoundaryReceipt ≡ false
theoremPromotedProof =
  refl

fullNSPromotedProof :
  fullNSPromoted canonicalNSTriadWall1CarrierIdentificationBoundaryReceipt ≡ false
fullNSPromotedProof =
  refl

clayPromotedProof :
  clayPromoted canonicalNSTriadWall1CarrierIdentificationBoundaryReceipt ≡ false
clayPromotedProof =
  refl

rowsAreCanonicalProof :
  rows canonicalNSTriadWall1CarrierIdentificationBoundaryReceipt ≡ canonicalRows
rowsAreCanonicalProof =
  refl

gapsAreCanonicalProof :
  gaps canonicalNSTriadWall1CarrierIdentificationBoundaryReceipt ≡ canonicalGaps
gapsAreCanonicalProof =
  refl

remainingOptionsAreDeclaredProof :
  remainingOptions canonicalNSTriadWall1CarrierIdentificationBoundaryReceipt ≡
  "corrected discrete carrier"
  ∷ "plaquette/packing carrier"
  ∷ "direct continuous XY/operator carrier"
  ∷ []
remainingOptionsAreDeclaredProof =
  refl

controlCardSlotsAreCanonicalProof :
  controlCardSlots canonicalNSTriadWall1CarrierIdentificationBoundaryReceipt ≡
  "O" ∷ "R" ∷ "C" ∷ "S" ∷ "L" ∷ "P" ∷ "G" ∷ "F" ∷ []
controlCardSlotsAreCanonicalProof =
  refl

------------------------------------------------------------------------
-- Human-readable boundary statement.

boundaryStatement : String
boundaryStatement =
  "Wall 1 floor is real, but the active shell extraction still leaves carrier identification open; cycle-family, raw signed-XOR, and signed-spectral carriers are insufficient, and the remaining options are corrected discrete, plaquette/packing, or direct continuous XY/operator carriers."
