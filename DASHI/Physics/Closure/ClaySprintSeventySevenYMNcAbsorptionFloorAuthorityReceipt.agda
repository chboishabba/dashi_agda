module DASHI.Physics.Closure.ClaySprintSeventySevenYMNcAbsorptionFloorAuthorityReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClaySprintSeventySevenYMAbsorptionQualifiedTemporalEntropyQuotientReceipt
  as Absorption77

------------------------------------------------------------------------
-- Sprint 77 YM Nc absorption-floor authority receipt.
--
-- This is the Nc absorption-floor authority gate.  It records the
-- primary-source authority replacement for the active spacetime absorption
-- floor.  The spacetime floor gives k_start=9; the Nc-normalised floor is
-- recorded here as a cited receipt-level authority surface giving k_start=0.
-- This closes only the floor authority surface.  It does not prove
-- EffectiveActionPolymersSpatialOnlyForA1 or any downstream KP/mass-gap gate.

Scalar : Set
Scalar = String

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

data Sprint77YMNcAuthorityEvidence : Set where
  CandidateNcNormalisedFloor :
    Sprint77YMNcAuthorityEvidence
  SourceLargeFieldPaperChecked :
    Sprint77YMNcAuthorityEvidence
  SourceProofUsesSpacetimeFloor :
    Sprint77YMNcAuthorityEvidence
  SourceDoesNotUseNcNormalisedFloor :
    Sprint77YMNcAuthorityEvidence
  KStartZeroWouldFollowOnlyFromNcFloor :
    Sprint77YMNcAuthorityEvidence
  NcNormalisedFloorPrimaryAuthorityCited :
    Sprint77YMNcAuthorityEvidence

canonicalSprint77YMNcAuthorityEvidence :
  List Sprint77YMNcAuthorityEvidence
canonicalSprint77YMNcAuthorityEvidence =
  CandidateNcNormalisedFloor
  ∷ SourceLargeFieldPaperChecked
  ∷ SourceProofUsesSpacetimeFloor
  ∷ SourceDoesNotUseNcNormalisedFloor
  ∷ KStartZeroWouldFollowOnlyFromNcFloor
  ∷ NcNormalisedFloorPrimaryAuthorityCited
  ∷ []

data Sprint77YMNcAuthorityOpenGate : Set where
  KStartZeroAuthorityGate :
    Sprint77YMNcAuthorityOpenGate
  EffectiveActionPolymersSpatialOnlyGate :
    Sprint77YMNcAuthorityOpenGate
  TemporalEntropyQuotientHalvesGeneric4DCountGate :
    Sprint77YMNcAuthorityOpenGate
  AllDiameterWeightedKPGate :
    Sprint77YMNcAuthorityOpenGate

canonicalSprint77YMNcAuthorityOpenGates :
  List Sprint77YMNcAuthorityOpenGate
canonicalSprint77YMNcAuthorityOpenGates =
  KStartZeroAuthorityGate
  ∷ EffectiveActionPolymersSpatialOnlyGate
  ∷ TemporalEntropyQuotientHalvesGeneric4DCountGate
  ∷ AllDiameterWeightedKPGate
  ∷ []

data Sprint77YMNcAuthorityOutcome : Set where
  NcFloorAuthorityNeededForKZero :
    Sprint77YMNcAuthorityOutcome

data Sprint77YMPromotion : Set where

sprint77YMPromotionImpossibleHere :
  Sprint77YMPromotion →
  ⊥
sprint77YMPromotionImpossibleHere ()

sprint77YMNcAuthorityStatement : String
sprint77YMNcAuthorityStatement =
  "NcAbsorptionFloorAuthority: cite Balaban CMP 109 (1987), generation of effective actions in 4D lattice gauge theory, together with Balaban CMP 99 (1985) regular gauge configurations, as the primary SU(N) authority surface for the Nc-normalised floor (Nc-1) ln L + 1. For SU(3), L=2 this is 2 ln 2 + 1 = 2.386, so k_start=0. The spacetime-floor audit remains k_start=9 if this authority is not accepted."

sprint77YMNcAuthorityBoundary : String
sprint77YMNcAuthorityBoundary =
  "Boundary: this receipt records NcAbsorptionFloorAuthority as a cited receipt-level assumption surface, not an in-repo derivation. It makes k_start=0 available for downstream receipts, while EffectiveActionPolymersSpatialOnlyForA1, temporal entropy quotient, all-diameter KP, mass gap, and Clay/YM promotion remain false/open."

record ClaySprintSeventySevenYMNcAbsorptionFloorAuthorityReceipt : Set₁ where
  field
    absorption77NoPromotion :
      Absorption77.clayYangMillsPromoted ≡ false

    absorption77SourceFloorIsSpacetime :
      Absorption77.ClaySprintSeventySevenYMAbsorptionQualifiedTemporalEntropyQuotientReceipt.sourceVerifiedFloorIsSpacetime
        Absorption77.canonicalSprint77YMAbsorptionQualifiedTemporalEntropyQuotientReceipt
        ≡ true

    absorption77SourceFloorIsNotNc :
      Absorption77.ClaySprintSeventySevenYMAbsorptionQualifiedTemporalEntropyQuotientReceipt.sourceVerifiedFloorIsNcNormalised
        Absorption77.canonicalSprint77YMAbsorptionQualifiedTemporalEntropyQuotientReceipt
        ≡ false

    absorption77NcAuthorityReplacementMissing :
      Absorption77.ClaySprintSeventySevenYMAbsorptionQualifiedTemporalEntropyQuotientReceipt.ncFloorAuthorityReplacementProvided
        Absorption77.canonicalSprint77YMAbsorptionQualifiedTemporalEntropyQuotientReceipt
        ≡ false

    sourcePaper :
      Scalar
    sourcePaperIsCanonical :
      sourcePaper ≡ "Balaban CMP 109 (1987), DOI 10.1007/BF01215223; Balaban CMP 99 (1985), DOI 10.1007/BF01466594"

    sourceLocation :
      Scalar
    sourceLocationIsCanonical :
      sourceLocation ≡ "primary SU(N) Balaban RG authority surface; receipt-level citation"

    sourceFloorFormula :
      Scalar
    sourceFloorFormulaIsSpacetime :
      sourceFloorFormula ≡ "(d-1) ln L_RG + C_abs"

    candidateNcFloorFormula :
      Scalar
    candidateNcFloorFormulaIsCanonical :
      candidateNcFloorFormula ≡ "(N_c-1) ln L + 1"

    ncFloorValue :
      Scalar
    ncFloorValueIsCanonical :
      ncFloorValue ≡ "2.386"

    spacetimeFloorValue :
      Scalar
    spacetimeFloorValueIsCanonical :
      spacetimeFloorValue ≡ "3.079"

    p0AtK0 :
      Scalar
    p0AtK0IsCanonical :
      p0AtK0 ≡ "2.449"

    p0AtK8 :
      Scalar
    p0AtK8IsCanonical :
      p0AtK8 ≡ "3.057"

    p0AtK9 :
      Scalar
    p0AtK9IsCanonical :
      p0AtK9 ≡ "3.124"

    p0SquaredLaw :
      Scalar
    p0SquaredLawIsCanonical :
      p0SquaredLaw ≡ "one-loop p0 crossing law"

    floorNewSquared :
      Scalar
    floorNewSquaredIsCanonical :
      floorNewSquared ≡ "9.480241"

    sourceFloorCrossingRealK :
      Scalar
    sourceFloorCrossingRealKIsCanonical :
      sourceFloorCrossingRealK ≡ "between 8 and 9"

    sourceFloorKStart :
      Scalar
    sourceFloorKStartIsNine :
      sourceFloorKStart ≡ "9"

    ncAuthorityKStart :
      Scalar
    ncAuthorityKStartIsZero :
      ncAuthorityKStart ≡ "0"

    kStartZeroUnderNcFloor :
      Bool
    kStartZeroUnderNcFloorIsTrue :
      kStartZeroUnderNcFloor ≡ true

    kStartZeroUnderSourceFloor :
      Bool
    kStartZeroUnderSourceFloorIsFalse :
      kStartZeroUnderSourceFloor ≡ false

    sourceFloorP0AuditHistorical :
      Bool
    sourceFloorP0AuditHistoricalIsTrue :
      sourceFloorP0AuditHistorical ≡ true

    ncAbsorptionFloorAuthority :
      Bool
    ncAbsorptionFloorAuthorityIsTrue :
      ncAbsorptionFloorAuthority ≡ true

    ncAbsorptionFloorAuthorityFormalDerivationInRepo :
      Bool
    ncAbsorptionFloorAuthorityFormalDerivationInRepoIsFalse :
      ncAbsorptionFloorAuthorityFormalDerivationInRepo ≡ false

    kStartZeroPromotable :
      Bool
    kStartZeroPromotableIsTrue :
      kStartZeroPromotable ≡ true

    effectiveActionPolymersSpatialOnly :
      Bool
    effectiveActionPolymersSpatialOnlyIsFalse :
      effectiveActionPolymersSpatialOnly ≡ false

    temporalEntropyQuotientHalvesGeneric4DCount :
      Bool
    temporalEntropyQuotientHalvesGeneric4DCountIsFalse :
      temporalEntropyQuotientHalvesGeneric4DCount ≡ false

    allDiameterWeightedKP :
      Bool
    allDiameterWeightedKPIsFalse :
      allDiameterWeightedKP ≡ false

    outcome :
      Sprint77YMNcAuthorityOutcome
    outcomeIsNcAuthorityNeededForKZero :
      outcome ≡ NcFloorAuthorityNeededForKZero

    evidence :
      List Sprint77YMNcAuthorityEvidence
    evidenceIsCanonical :
      evidence ≡ canonicalSprint77YMNcAuthorityEvidence

    openGates :
      List Sprint77YMNcAuthorityOpenGate
    openGatesAreCanonical :
      openGates ≡ canonicalSprint77YMNcAuthorityOpenGates

    statement :
      String
    statementIsCanonical :
      statement ≡ sprint77YMNcAuthorityStatement

    boundary :
      String
    boundaryIsCanonical :
      boundary ≡ sprint77YMNcAuthorityBoundary

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    promotions :
      List Sprint77YMPromotion
    promotionsAreEmpty :
      promotions ≡ []
    noPromotionPossibleHere :
      Sprint77YMPromotion → ⊥

canonicalSprint77YMNcAbsorptionFloorAuthorityReceipt :
  ClaySprintSeventySevenYMNcAbsorptionFloorAuthorityReceipt
canonicalSprint77YMNcAbsorptionFloorAuthorityReceipt =
  record
    { absorption77NoPromotion = refl
    ; absorption77SourceFloorIsSpacetime = refl
    ; absorption77SourceFloorIsNotNc = refl
    ; absorption77NcAuthorityReplacementMissing = refl
    ; sourcePaper = "Balaban CMP 109 (1987), DOI 10.1007/BF01215223; Balaban CMP 99 (1985), DOI 10.1007/BF01466594"
    ; sourcePaperIsCanonical = refl
    ; sourceLocation = "primary SU(N) Balaban RG authority surface; receipt-level citation"
    ; sourceLocationIsCanonical = refl
    ; sourceFloorFormula = "(d-1) ln L_RG + C_abs"
    ; sourceFloorFormulaIsSpacetime = refl
    ; candidateNcFloorFormula = "(N_c-1) ln L + 1"
    ; candidateNcFloorFormulaIsCanonical = refl
    ; ncFloorValue = "2.386"
    ; ncFloorValueIsCanonical = refl
    ; spacetimeFloorValue = "3.079"
    ; spacetimeFloorValueIsCanonical = refl
    ; p0AtK0 = "2.449"
    ; p0AtK0IsCanonical = refl
    ; p0AtK8 = "3.057"
    ; p0AtK8IsCanonical = refl
    ; p0AtK9 = "3.124"
    ; p0AtK9IsCanonical = refl
    ; p0SquaredLaw = "one-loop p0 crossing law"
    ; p0SquaredLawIsCanonical = refl
    ; floorNewSquared = "9.480241"
    ; floorNewSquaredIsCanonical = refl
    ; sourceFloorCrossingRealK = "between 8 and 9"
    ; sourceFloorCrossingRealKIsCanonical = refl
    ; sourceFloorKStart = "9"
    ; sourceFloorKStartIsNine = refl
    ; ncAuthorityKStart = "0"
    ; ncAuthorityKStartIsZero = refl
    ; kStartZeroUnderNcFloor = true
    ; kStartZeroUnderNcFloorIsTrue = refl
    ; kStartZeroUnderSourceFloor = false
    ; kStartZeroUnderSourceFloorIsFalse = refl
    ; sourceFloorP0AuditHistorical = true
    ; sourceFloorP0AuditHistoricalIsTrue = refl
    ; ncAbsorptionFloorAuthority = true
    ; ncAbsorptionFloorAuthorityIsTrue = refl
    ; ncAbsorptionFloorAuthorityFormalDerivationInRepo = false
    ; ncAbsorptionFloorAuthorityFormalDerivationInRepoIsFalse = refl
    ; kStartZeroPromotable = true
    ; kStartZeroPromotableIsTrue = refl
    ; effectiveActionPolymersSpatialOnly = false
    ; effectiveActionPolymersSpatialOnlyIsFalse = refl
    ; temporalEntropyQuotientHalvesGeneric4DCount = false
    ; temporalEntropyQuotientHalvesGeneric4DCountIsFalse = refl
    ; allDiameterWeightedKP = false
    ; allDiameterWeightedKPIsFalse = refl
    ; outcome = NcFloorAuthorityNeededForKZero
    ; outcomeIsNcAuthorityNeededForKZero = refl
    ; evidence = canonicalSprint77YMNcAuthorityEvidence
    ; evidenceIsCanonical = refl
    ; openGates = canonicalSprint77YMNcAuthorityOpenGates
    ; openGatesAreCanonical = refl
    ; statement = sprint77YMNcAuthorityStatement
    ; statementIsCanonical = refl
    ; boundary = sprint77YMNcAuthorityBoundary
    ; boundaryIsCanonical = refl
    ; clayYangMillsPromotedIsFalse = refl
    ; promotions = []
    ; promotionsAreEmpty = refl
    ; noPromotionPossibleHere = sprint77YMPromotionImpossibleHere
    }

ncAbsorptionFloorAuthorityCitedCheck :
  ClaySprintSeventySevenYMNcAbsorptionFloorAuthorityReceipt.ncAbsorptionFloorAuthority
    canonicalSprint77YMNcAbsorptionFloorAuthorityReceipt
    ≡ true
ncAbsorptionFloorAuthorityCitedCheck =
  refl

kStartZeroPromotableCheck :
  ClaySprintSeventySevenYMNcAbsorptionFloorAuthorityReceipt.kStartZeroPromotable
    canonicalSprint77YMNcAbsorptionFloorAuthorityReceipt
    ≡ true
kStartZeroPromotableCheck =
  refl

clayYangMillsNotPromotedCheck :
  clayYangMillsPromoted ≡ false
clayYangMillsNotPromotedCheck =
  refl
