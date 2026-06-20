module DASHI.Physics.Closure.NSVorticityAlignmentObstructionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- NS vorticity alignment obstruction receipt.
--
-- This module records the structural obstruction lane only.  It keeps the
-- boundary case explicit: if |Omega_K| = 0 and the vorticity aligns with the
-- compressive eigenvector, then Pi <= 0 and the enstrophy-growth contribution
-- is nonpositive.  The remaining obstruction is the misaligned-vorticity
-- regime inside the compressive zone.  No theorem promotion is claimed.

data Void : Set where

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

------------------------------------------------------------------------
-- Local carriers for the obstruction decomposition.

data VorticityBoundaryCarrier : Set where
  omegaKAbsoluteValueZeroBoundaryCarrier :
    VorticityBoundaryCarrier

data AlignmentCarrier : Set where
  vorticityAlignedWithCompressiveEigenvectorCarrier :
    AlignmentCarrier

data SignConsequenceCarrier : Set where
  piNonpositiveAndEnstrophyGrowthNonpositiveCarrier :
    SignConsequenceCarrier

data ResidualObstructionCarrier : Set where
  misalignedVorticityInCompressiveZoneCarrier :
    ResidualObstructionCarrier

data NSVorticityAlignmentObstructionPromotion : Set where

nsVorticityAlignmentObstructionPromotionImpossibleHere :
  NSVorticityAlignmentObstructionPromotion →
  Void
nsVorticityAlignmentObstructionPromotionImpossibleHere ()

data NSVorticityAlignmentObstructionRow : Set where
  omegaKZeroBoundaryRecorded :
    NSVorticityAlignmentObstructionRow
  compressiveAlignmentRecorded :
    NSVorticityAlignmentObstructionRow
  piNonpositiveRecorded :
    NSVorticityAlignmentObstructionRow
  enstrophyGrowthNonpositiveRecorded :
    NSVorticityAlignmentObstructionRow
  misalignedCompressiveZoneObstructionRecorded :
    NSVorticityAlignmentObstructionRow
  theoremPromotionBlockedRecorded :
    NSVorticityAlignmentObstructionRow

canonicalNSVorticityAlignmentObstructionRows :
  List NSVorticityAlignmentObstructionRow
canonicalNSVorticityAlignmentObstructionRows =
  omegaKZeroBoundaryRecorded
  ∷ compressiveAlignmentRecorded
  ∷ piNonpositiveRecorded
  ∷ enstrophyGrowthNonpositiveRecorded
  ∷ misalignedCompressiveZoneObstructionRecorded
  ∷ theoremPromotionBlockedRecorded
  ∷ []

NSVorticityAlignmentObstructionRowCount : Nat
NSVorticityAlignmentObstructionRowCount =
  listLength canonicalNSVorticityAlignmentObstructionRows

NSVorticityAlignmentObstructionRowCountIs6 :
  NSVorticityAlignmentObstructionRowCount ≡ 6
NSVorticityAlignmentObstructionRowCountIs6 =
  refl

------------------------------------------------------------------------
-- Canonical O/R/C/S/L/P/G/F strings.

organizationString : String
organizationString =
  "O: Worker lane 5 records the vorticity alignment obstruction as a fail-closed structural receipt."

requirementString : String
requirementString =
  "R: If |Omega_K| = 0 and vorticity aligns with the compressive eigenvector, then Pi <= 0 and enstrophy growth is nonpositive; the remaining obstruction is misaligned vorticity in the compressive zone."

codeArtifactString : String
codeArtifactString =
  "C: This standalone Agda receipt owns only the local boundary carriers, the obstruction decomposition rows, the fail-closed promotion guard, and the canonical O/R/C/S/L/P/G/F strings."

stateString : String
stateString =
  "S: The boundary carrier, alignment route, and nonpositive-sign consequence are recorded; the misaligned compressive-zone obstruction remains open; theorem promotion and Clay promotion stay false."

latticeString : String
latticeString =
  "L: |Omega_K| = 0 boundary carrier -> compressive-eigenvector alignment -> Pi <= 0 -> nonpositive enstrophy growth -> residual misaligned-vorticity obstruction in the compressive zone -> blocked promotion."

proposalString : String
proposalString =
  "P: Treat this as a structural obstruction receipt only; any closure beyond the recorded sign decomposition must come from a separate theorem-bearing route."

governanceString : String
governanceString =
  "G: Fail closed: the receipt records the sign decomposition qualitatively, keeps the residual obstruction explicit, and does not assert theorem promotion."

gapString : String
gapString =
  "F: Remaining gap is the misaligned-vorticity compressive-zone analysis; no theorem promotion or Clay promotion is discharged here."

record NSVorticityAlignmentObstructionORCSLPGF : Set where
  constructor nsVorticityAlignmentObstructionORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ organizationString
    R : String
    RIsCanonical : R ≡ requirementString
    C : String
    CIsCanonical : C ≡ codeArtifactString
    S : String
    SIsCanonical : S ≡ stateString
    L : String
    LIsCanonical : L ≡ latticeString
    P : String
    PIsCanonical : P ≡ proposalString
    G : String
    GIsCanonical : G ≡ governanceString
    F : String
    FIsCanonical : F ≡ gapString

canonicalNSVorticityAlignmentObstructionORCSLPGF :
  NSVorticityAlignmentObstructionORCSLPGF
canonicalNSVorticityAlignmentObstructionORCSLPGF =
  nsVorticityAlignmentObstructionORCSLPGF
    organizationString
    refl
    requirementString
    refl
    codeArtifactString
    refl
    stateString
    refl
    latticeString
    refl
    proposalString
    refl
    governanceString
    refl
    gapString
    refl

------------------------------------------------------------------------
-- Receipt statements and canonical carriers.

omegaKZeroStatement : String
omegaKZeroStatement =
  "|Omega_K| = 0 boundary carrier recorded"

compressiveAlignmentStatement : String
compressiveAlignmentStatement =
  "vorticity aligns with the compressive eigenvector"

piNonpositiveStatement : String
piNonpositiveStatement =
  "Pi <= 0 follows on the aligned boundary lane"

enstrophyGrowthNonpositiveStatement : String
enstrophyGrowthNonpositiveStatement =
  "enstrophy growth contribution is nonpositive on the aligned lane"

residualObstructionStatement : String
residualObstructionStatement =
  "remaining obstruction: misaligned vorticity in the compressive zone"

nsvorticityAlignmentObstructionStatement : String
nsvorticityAlignmentObstructionStatement =
  "The receipt records the boundary sign decomposition qualitatively: when |Omega_K| = 0 and vorticity aligns with the compressive eigenvector, Pi <= 0 and the enstrophy-growth contribution is nonpositive; the only remaining obstruction is misaligned vorticity in the compressive zone. No theorem promotion is claimed."

canonicalVorticityBoundaryCarrier :
  VorticityBoundaryCarrier
canonicalVorticityBoundaryCarrier =
  omegaKAbsoluteValueZeroBoundaryCarrier

canonicalAlignmentCarrier :
  AlignmentCarrier
canonicalAlignmentCarrier =
  vorticityAlignedWithCompressiveEigenvectorCarrier

canonicalSignConsequenceCarrier :
  SignConsequenceCarrier
canonicalSignConsequenceCarrier =
  piNonpositiveAndEnstrophyGrowthNonpositiveCarrier

canonicalResidualObstructionCarrier :
  ResidualObstructionCarrier
canonicalResidualObstructionCarrier =
  misalignedVorticityInCompressiveZoneCarrier

canonicalOmegaKZeroBoundaryRecorded : Bool
canonicalOmegaKZeroBoundaryRecorded =
  true

canonicalCompressiveAlignmentRecorded : Bool
canonicalCompressiveAlignmentRecorded =
  true

canonicalPiNonpositiveRecorded : Bool
canonicalPiNonpositiveRecorded =
  true

canonicalEnstrophyGrowthNonpositiveRecorded : Bool
canonicalEnstrophyGrowthNonpositiveRecorded =
  true

canonicalResidualObstructionOpen : Bool
canonicalResidualObstructionOpen =
  true

canonicalTheoremPromotion : Bool
canonicalTheoremPromotion =
  false

canonicalClayPromotion : Bool
canonicalClayPromotion =
  false

record NSVorticityAlignmentObstructionReceipt : Setω where
  field
    statusRows :
      List NSVorticityAlignmentObstructionRow
    statusRowsAreCanonical :
      statusRows ≡ canonicalNSVorticityAlignmentObstructionRows
    statusRowCountIsCanonical :
      NSVorticityAlignmentObstructionRowCount ≡ 6
    vorticityBoundaryCarrier :
      VorticityBoundaryCarrier
    vorticityBoundaryCarrierIsCanonical :
      vorticityBoundaryCarrier ≡ canonicalVorticityBoundaryCarrier
    alignmentCarrier :
      AlignmentCarrier
    alignmentCarrierIsCanonical :
      alignmentCarrier ≡ canonicalAlignmentCarrier
    signConsequenceCarrier :
      SignConsequenceCarrier
    signConsequenceCarrierIsCanonical :
      signConsequenceCarrier ≡ canonicalSignConsequenceCarrier
    residualObstructionCarrier :
      ResidualObstructionCarrier
    residualObstructionCarrierIsCanonical :
      residualObstructionCarrier ≡ canonicalResidualObstructionCarrier
    omegaKZeroBoundaryRecordedFlag :
      Bool
    omegaKZeroBoundaryRecordedFlagIsTrue :
      omegaKZeroBoundaryRecordedFlag ≡ true
    compressiveAlignmentRecordedFlag :
      Bool
    compressiveAlignmentRecordedFlagIsTrue :
      compressiveAlignmentRecordedFlag ≡ true
    piNonpositiveRecordedFlag :
      Bool
    piNonpositiveRecordedFlagIsTrue :
      piNonpositiveRecordedFlag ≡ true
    enstrophyGrowthNonpositiveRecordedFlag :
      Bool
    enstrophyGrowthNonpositiveRecordedFlagIsTrue :
      enstrophyGrowthNonpositiveRecordedFlag ≡ true
    residualObstructionOpen :
      Bool
    residualObstructionOpenIsTrue :
      residualObstructionOpen ≡ true
    theoremPromotion :
      Bool
    theoremPromotionIsFalse :
      theoremPromotion ≡ false
    clayPromotion :
      Bool
    clayPromotionIsFalse :
      clayPromotion ≡ false
    orcslpgf :
      NSVorticityAlignmentObstructionORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSVorticityAlignmentObstructionORCSLPGF
    statement :
      String
    statementIsCanonical :
      statement ≡ nsvorticityAlignmentObstructionStatement
    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡
        omegaKZeroStatement
        ∷ compressiveAlignmentStatement
        ∷ piNonpositiveStatement
        ∷ enstrophyGrowthNonpositiveStatement
        ∷ residualObstructionStatement
        ∷ "theorem promotion stays false"
        ∷ "Clay promotion stays false"
        ∷ []
    promotionFlags :
      List NSVorticityAlignmentObstructionPromotion
    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open NSVorticityAlignmentObstructionReceipt public

canonicalNSVorticityAlignmentObstructionReceipt :
  NSVorticityAlignmentObstructionReceipt
canonicalNSVorticityAlignmentObstructionReceipt =
  record
    { statusRows =
        canonicalNSVorticityAlignmentObstructionRows
    ; statusRowsAreCanonical =
        refl
    ; statusRowCountIsCanonical =
        refl
    ; vorticityBoundaryCarrier =
        canonicalVorticityBoundaryCarrier
    ; vorticityBoundaryCarrierIsCanonical =
        refl
    ; alignmentCarrier =
        canonicalAlignmentCarrier
    ; alignmentCarrierIsCanonical =
        refl
    ; signConsequenceCarrier =
        canonicalSignConsequenceCarrier
    ; signConsequenceCarrierIsCanonical =
        refl
    ; residualObstructionCarrier =
        canonicalResidualObstructionCarrier
    ; residualObstructionCarrierIsCanonical =
        refl
    ; omegaKZeroBoundaryRecordedFlag =
        canonicalOmegaKZeroBoundaryRecorded
    ; omegaKZeroBoundaryRecordedFlagIsTrue =
        refl
    ; compressiveAlignmentRecordedFlag =
        canonicalCompressiveAlignmentRecorded
    ; compressiveAlignmentRecordedFlagIsTrue =
        refl
    ; piNonpositiveRecordedFlag =
        canonicalPiNonpositiveRecorded
    ; piNonpositiveRecordedFlagIsTrue =
        refl
    ; enstrophyGrowthNonpositiveRecordedFlag =
        canonicalEnstrophyGrowthNonpositiveRecorded
    ; enstrophyGrowthNonpositiveRecordedFlagIsTrue =
        refl
    ; residualObstructionOpen =
        canonicalResidualObstructionOpen
    ; residualObstructionOpenIsTrue =
        refl
    ; theoremPromotion =
        canonicalTheoremPromotion
    ; theoremPromotionIsFalse =
        refl
    ; clayPromotion =
        canonicalClayPromotion
    ; clayPromotionIsFalse =
        refl
    ; orcslpgf =
        canonicalNSVorticityAlignmentObstructionORCSLPGF
    ; orcslpgfIsCanonical =
        refl
    ; statement =
        nsvorticityAlignmentObstructionStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        omegaKZeroStatement
        ∷ compressiveAlignmentStatement
        ∷ piNonpositiveStatement
        ∷ enstrophyGrowthNonpositiveStatement
        ∷ residualObstructionStatement
        ∷ "theorem promotion stays false"
        ∷ "Clay promotion stays false"
        ∷ []
    ; receiptBoundaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

recordsOmegaKZeroBoundary :
  omegaKZeroBoundaryRecordedFlag canonicalNSVorticityAlignmentObstructionReceipt
  ≡ true
recordsOmegaKZeroBoundary =
  refl

recordsCompressiveAlignment :
  compressiveAlignmentRecordedFlag canonicalNSVorticityAlignmentObstructionReceipt
  ≡ true
recordsCompressiveAlignment =
  refl

recordsPiNonpositive :
  piNonpositiveRecordedFlag canonicalNSVorticityAlignmentObstructionReceipt
  ≡ true
recordsPiNonpositive =
  refl

recordsEnstrophyGrowthNonpositive :
  enstrophyGrowthNonpositiveRecordedFlag
    canonicalNSVorticityAlignmentObstructionReceipt
  ≡ true
recordsEnstrophyGrowthNonpositive =
  refl

recordsResidualObstructionOpen :
  residualObstructionOpen canonicalNSVorticityAlignmentObstructionReceipt
  ≡ true
recordsResidualObstructionOpen =
  refl

recordsTheoremPromotionFalse :
  theoremPromotion canonicalNSVorticityAlignmentObstructionReceipt ≡ false
recordsTheoremPromotionFalse =
  refl

recordsClayPromotionFalse :
  clayPromotion canonicalNSVorticityAlignmentObstructionReceipt ≡ false
recordsClayPromotionFalse =
  refl
