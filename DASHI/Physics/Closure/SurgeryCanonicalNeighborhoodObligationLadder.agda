module DASHI.Physics.Closure.SurgeryCanonicalNeighborhoodObligationLadder where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.ShellNeighborhoodClass
  using
    ( ShellNeighborhoodClass
    ; definiteShellNeighborhood
    ; oneMinusShellNeighborhood
    ; mixed21ShellNeighborhood
    ; split22ShellNeighborhood
    ; unknownShellNeighborhood
    )

open import DASHI.Physics.Closure.SurgeryCanonicalNeighborhoodObstruction
  using
    ( DiscreteNeighborhoodCandidate
    ; discreteCompactPositiveCandidate
    ; discreteEpsilonNeckCandidate
    ; discreteCapCandidate
    ; discreteSplitCandidate
    ; discreteUnknownCandidate
    ; SmoothCanonicalNeighborhoodKind
    ; smoothEpsilonNeck
    ; smoothCap
    ; smoothCompactPositive
    ; SurgeryObligation
    ; requireSmoothEpsilonNeckModel
    ; requireSmoothCapModel
    ; requireCompactPositiveCanonicalNeighborhoodTheorem
    ; requireSurgeryContinuationLaw
    ; retainDiscreteShellOnlyStatus
    ; candidateFromShellNeighborhoodClass
    ; candidateSmoothTarget
    ; candidateObligations
    ; SurgeryCanonicalNeighborhoodObstruction
    ; obstructionFromShellClass
    ; discreteCandidate
    ; smoothTarget
    ; obligations
    ; smoothCanonicalNeighborhoodAvailable
    ; surgeryContinuationAvailable
    )

open import DASHI.Physics.Closure.BTCanonicalNeckAnalogue
  using
    ( BTCanonicalNeckAnalogue
    ; canonicalP2BTNeckAnalogue
    ; primeLane
    ; crossSectionCardinality
    ; crossSectionCardinalityForLane
    ; crossSectionCardinalityIsPPlusOne
    ; pathCylinderAnalogueConstructed
    ; smoothS2CrossSectionPromoted
    ; epsilonNeckTheoremPromoted
    )

------------------------------------------------------------------------
-- Surgery-obligation ladder.
--
-- The ladder is intentionally stronger than a list of flags.  Each row
-- carries the typed path from a finite shell class to its discrete candidate,
-- from the candidate to the smooth target it would have to realize, then to
-- the still-missing obligations and the resulting promotion status.

data LadderPromotionStatus : Set where
  discreteCandidateOnly :
    LadderPromotionStatus

  smoothTargetNamedButBlocked :
    LadderPromotionStatus

  finiteAnalogueConstructedSmoothTargetBlocked :
    LadderPromotionStatus

statusForCandidate :
  DiscreteNeighborhoodCandidate →
  LadderPromotionStatus
statusForCandidate discreteCompactPositiveCandidate =
  smoothTargetNamedButBlocked
statusForCandidate discreteEpsilonNeckCandidate =
  smoothTargetNamedButBlocked
statusForCandidate discreteCapCandidate =
  smoothTargetNamedButBlocked
statusForCandidate discreteSplitCandidate =
  smoothTargetNamedButBlocked
statusForCandidate discreteUnknownCandidate =
  discreteCandidateOnly

data LadderStage : Set where
  discreteShellCandidateStage :
    DiscreteNeighborhoodCandidate →
    LadderStage

  smoothTargetStage :
    SmoothCanonicalNeighborhoodKind →
    LadderStage

  missingObligationsStage :
    List SurgeryObligation →
    LadderStage

  promotionStatusStage :
    LadderPromotionStatus →
    LadderStage

candidateStage :
  DiscreteNeighborhoodCandidate →
  LadderStage
candidateStage candidate =
  discreteShellCandidateStage candidate

targetStage :
  DiscreteNeighborhoodCandidate →
  LadderStage
targetStage candidate =
  smoothTargetStage (candidateSmoothTarget candidate)

obligationStage :
  DiscreteNeighborhoodCandidate →
  LadderStage
obligationStage candidate =
  missingObligationsStage (candidateObligations candidate)

promotionStage :
  DiscreteNeighborhoodCandidate →
  LadderStage
promotionStage candidate =
  promotionStatusStage (statusForCandidate candidate)

record SurgeryObligationLadderRow : Set where
  field
    sourceShellClass :
      ShellNeighborhoodClass

    sourceObstruction :
      SurgeryCanonicalNeighborhoodObstruction

    sourceObstructionIsCanonical :
      sourceObstruction ≡ obstructionFromShellClass sourceShellClass

    candidate :
      DiscreteNeighborhoodCandidate

    candidateIsClassMapping :
      candidate ≡ candidateFromShellNeighborhoodClass sourceShellClass

    candidateStageToken :
      LadderStage

    candidateStageTokenIsCandidate :
      candidateStageToken ≡ candidateStage candidate

    smoothTarget :
      SmoothCanonicalNeighborhoodKind

    smoothTargetIsCandidateTarget :
      smoothTarget ≡ candidateSmoothTarget candidate

    smoothTargetStageToken :
      LadderStage

    smoothTargetStageTokenIsTarget :
      smoothTargetStageToken ≡ smoothTargetStage smoothTarget

    missingObligations :
      List SurgeryObligation

    missingObligationsAreCandidateObligations :
      missingObligations ≡ candidateObligations candidate

    missingObligationsStageToken :
      LadderStage

    missingObligationsStageTokenIsObligations :
      missingObligationsStageToken ≡ missingObligationsStage missingObligations

    promotionStatus :
      LadderPromotionStatus

    promotionStatusIsCandidateStatus :
      promotionStatus ≡ statusForCandidate candidate

    promotionStatusStageToken :
      LadderStage

    promotionStatusStageTokenIsStatus :
      promotionStatusStageToken ≡ promotionStatusStage promotionStatus

    smoothPromotionAvailable :
      Bool

    smoothPromotionAvailableIsFalse :
      smoothPromotionAvailable ≡ false

    surgeryContinuationAvailable :
      Bool

    surgeryContinuationAvailableIsFalse :
      surgeryContinuationAvailable ≡ false

    rowStatement :
      String

open SurgeryObligationLadderRow public

ladderRowFromShellClass :
  ShellNeighborhoodClass →
  SurgeryObligationLadderRow
ladderRowFromShellClass shellClass =
  let candidateFromClass =
        candidateFromShellNeighborhoodClass shellClass
  in
  record
    { sourceShellClass =
        shellClass
    ; sourceObstruction =
        obstructionFromShellClass shellClass
    ; sourceObstructionIsCanonical =
        refl
    ; candidate =
        candidateFromClass
    ; candidateIsClassMapping =
        refl
    ; candidateStageToken =
        candidateStage candidateFromClass
    ; candidateStageTokenIsCandidate =
        refl
    ; smoothTarget =
        candidateSmoothTarget candidateFromClass
    ; smoothTargetIsCandidateTarget =
        refl
    ; smoothTargetStageToken =
        smoothTargetStage (candidateSmoothTarget candidateFromClass)
    ; smoothTargetStageTokenIsTarget =
        refl
    ; missingObligations =
        candidateObligations candidateFromClass
    ; missingObligationsAreCandidateObligations =
        refl
    ; missingObligationsStageToken =
        missingObligationsStage (candidateObligations candidateFromClass)
    ; missingObligationsStageTokenIsObligations =
        refl
    ; promotionStatus =
        statusForCandidate candidateFromClass
    ; promotionStatusIsCandidateStatus =
        refl
    ; promotionStatusStageToken =
        promotionStatusStage (statusForCandidate candidateFromClass)
    ; promotionStatusStageTokenIsStatus =
        refl
    ; smoothPromotionAvailable =
        false
    ; smoothPromotionAvailableIsFalse =
        refl
    ; surgeryContinuationAvailable =
        false
    ; surgeryContinuationAvailableIsFalse =
        refl
    ; rowStatement =
        "Discrete shell candidate is routed to a smooth surgery target only as an obligation ladder; no row discharges the smooth neighborhood or continuation obligations."
    }

definiteCanonicalRow :
  SurgeryObligationLadderRow
definiteCanonicalRow =
  ladderRowFromShellClass definiteShellNeighborhood

oneMinusCanonicalRow :
  SurgeryObligationLadderRow
oneMinusCanonicalRow =
  ladderRowFromShellClass oneMinusShellNeighborhood

mixed21CanonicalRow :
  SurgeryObligationLadderRow
mixed21CanonicalRow =
  ladderRowFromShellClass mixed21ShellNeighborhood

split22CanonicalRow :
  SurgeryObligationLadderRow
split22CanonicalRow =
  ladderRowFromShellClass split22ShellNeighborhood

unknownCanonicalRow :
  SurgeryObligationLadderRow
unknownCanonicalRow =
  ladderRowFromShellClass unknownShellNeighborhood

canonicalSurgeryObligationLadder :
  List SurgeryObligationLadderRow
canonicalSurgeryObligationLadder =
  definiteCanonicalRow
  ∷ oneMinusCanonicalRow
  ∷ mixed21CanonicalRow
  ∷ split22CanonicalRow
  ∷ unknownCanonicalRow
  ∷ []

------------------------------------------------------------------------
-- Checked canonical row witnesses.

definiteCandidateMappingWitness :
  candidate definiteCanonicalRow ≡ discreteCompactPositiveCandidate
definiteCandidateMappingWitness =
  refl

definiteSmoothTargetWitness :
  smoothTarget definiteCanonicalRow ≡ smoothCompactPositive
definiteSmoothTargetWitness =
  refl

definiteObligationsWitness :
  missingObligations definiteCanonicalRow
  ≡
  requireCompactPositiveCanonicalNeighborhoodTheorem
  ∷ requireSurgeryContinuationLaw
  ∷ retainDiscreteShellOnlyStatus
  ∷ []
definiteObligationsWitness =
  refl

definitePromotionStatusWitness :
  promotionStatus definiteCanonicalRow ≡ smoothTargetNamedButBlocked
definitePromotionStatusWitness =
  refl

oneMinusCandidateMappingWitness :
  candidate oneMinusCanonicalRow ≡ discreteEpsilonNeckCandidate
oneMinusCandidateMappingWitness =
  refl

oneMinusSmoothTargetWitness :
  smoothTarget oneMinusCanonicalRow ≡ smoothEpsilonNeck
oneMinusSmoothTargetWitness =
  refl

oneMinusObligationsWitness :
  missingObligations oneMinusCanonicalRow
  ≡
  requireSmoothEpsilonNeckModel
  ∷ requireSurgeryContinuationLaw
  ∷ retainDiscreteShellOnlyStatus
  ∷ []
oneMinusObligationsWitness =
  refl

oneMinusPromotionStatusWitness :
  promotionStatus oneMinusCanonicalRow ≡ smoothTargetNamedButBlocked
oneMinusPromotionStatusWitness =
  refl

mixed21CandidateMappingWitness :
  candidate mixed21CanonicalRow ≡ discreteCapCandidate
mixed21CandidateMappingWitness =
  refl

mixed21SmoothTargetWitness :
  smoothTarget mixed21CanonicalRow ≡ smoothCap
mixed21SmoothTargetWitness =
  refl

mixed21ObligationsWitness :
  missingObligations mixed21CanonicalRow
  ≡
  requireSmoothCapModel
  ∷ requireSurgeryContinuationLaw
  ∷ retainDiscreteShellOnlyStatus
  ∷ []
mixed21ObligationsWitness =
  refl

mixed21PromotionStatusWitness :
  promotionStatus mixed21CanonicalRow ≡ smoothTargetNamedButBlocked
mixed21PromotionStatusWitness =
  refl

split22CandidateMappingWitness :
  candidate split22CanonicalRow ≡ discreteSplitCandidate
split22CandidateMappingWitness =
  refl

split22SmoothTargetWitness :
  smoothTarget split22CanonicalRow ≡ smoothEpsilonNeck
split22SmoothTargetWitness =
  refl

split22ObligationsWitness :
  missingObligations split22CanonicalRow
  ≡
  requireSmoothEpsilonNeckModel
  ∷ requireSmoothCapModel
  ∷ requireSurgeryContinuationLaw
  ∷ retainDiscreteShellOnlyStatus
  ∷ []
split22ObligationsWitness =
  refl

split22PromotionStatusWitness :
  promotionStatus split22CanonicalRow ≡ smoothTargetNamedButBlocked
split22PromotionStatusWitness =
  refl

unknownCandidateMappingWitness :
  candidate unknownCanonicalRow ≡ discreteUnknownCandidate
unknownCandidateMappingWitness =
  refl

unknownSmoothTargetWitness :
  smoothTarget unknownCanonicalRow ≡ smoothEpsilonNeck
unknownSmoothTargetWitness =
  refl

unknownObligationsWitness :
  missingObligations unknownCanonicalRow
  ≡
  retainDiscreteShellOnlyStatus
  ∷ requireSurgeryContinuationLaw
  ∷ []
unknownObligationsWitness =
  refl

unknownPromotionStatusWitness :
  promotionStatus unknownCanonicalRow ≡ discreteCandidateOnly
unknownPromotionStatusWitness =
  refl

------------------------------------------------------------------------
-- BT-neck analogue row.

record BTNeckSurgeryObligationRow : Set where
  field
    analogue :
      BTCanonicalNeckAnalogue

    finiteCrossSectionCardinality :
      Nat

    finiteCrossSectionCardinalityIsAnalogueCardinality :
      finiteCrossSectionCardinality ≡ crossSectionCardinality analogue

    finiteCrossSectionCardinalityIsPPlusOne :
      crossSectionCardinality analogue
      ≡
      crossSectionCardinalityForLane (primeLane analogue)

    pathCylinderEvidenceConstructed :
      Bool

    pathCylinderEvidenceConstructedIsTrue :
      pathCylinderEvidenceConstructed ≡ true

    smoothS2CrossSectionDischarged :
      Bool

    smoothS2CrossSectionDischargedIsFalse :
      smoothS2CrossSectionDischarged ≡ false

    smoothEpsilonNeckDischarged :
      Bool

    smoothEpsilonNeckDischargedIsFalse :
      smoothEpsilonNeckDischarged ≡ false

    btSmoothTarget :
      SmoothCanonicalNeighborhoodKind

    btSmoothTargetIsEpsilonNeck :
      btSmoothTarget ≡ smoothEpsilonNeck

    btMissingObligations :
      List SurgeryObligation

    btMissingObligationsWitness :
      btMissingObligations
      ≡
      requireSmoothEpsilonNeckModel
      ∷ requireSurgeryContinuationLaw
      ∷ retainDiscreteShellOnlyStatus
      ∷ []

    btPromotionStatus :
      LadderPromotionStatus

    btPromotionStatusWitness :
      btPromotionStatus ≡ finiteAnalogueConstructedSmoothTargetBlocked

    btBoundaryStatement :
      String

open BTNeckSurgeryObligationRow public

canonicalBTNeckSurgeryObligationRow :
  BTNeckSurgeryObligationRow
canonicalBTNeckSurgeryObligationRow =
  record
    { analogue =
        canonicalP2BTNeckAnalogue
    ; finiteCrossSectionCardinality =
        crossSectionCardinality canonicalP2BTNeckAnalogue
    ; finiteCrossSectionCardinalityIsAnalogueCardinality =
        refl
    ; finiteCrossSectionCardinalityIsPPlusOne =
        crossSectionCardinalityIsPPlusOne canonicalP2BTNeckAnalogue
    ; pathCylinderEvidenceConstructed =
        pathCylinderAnalogueConstructed canonicalP2BTNeckAnalogue
    ; pathCylinderEvidenceConstructedIsTrue =
        refl
    ; smoothS2CrossSectionDischarged =
        smoothS2CrossSectionPromoted canonicalP2BTNeckAnalogue
    ; smoothS2CrossSectionDischargedIsFalse =
        refl
    ; smoothEpsilonNeckDischarged =
        epsilonNeckTheoremPromoted canonicalP2BTNeckAnalogue
    ; smoothEpsilonNeckDischargedIsFalse =
        refl
    ; btSmoothTarget =
        smoothEpsilonNeck
    ; btSmoothTargetIsEpsilonNeck =
        refl
    ; btMissingObligations =
        requireSmoothEpsilonNeckModel
        ∷ requireSurgeryContinuationLaw
        ∷ retainDiscreteShellOnlyStatus
        ∷ []
    ; btMissingObligationsWitness =
        refl
    ; btPromotionStatus =
        finiteAnalogueConstructedSmoothTargetBlocked
    ; btPromotionStatusWitness =
        refl
    ; btBoundaryStatement =
        "The BT row has finite neighbor-sphere and path-cylinder evidence, but that evidence is not a smooth S2 cross-section, smooth epsilon-neck chart, or surgery-continuation theorem."
    }

btFiniteEvidenceConstructedWitness :
  pathCylinderEvidenceConstructed canonicalBTNeckSurgeryObligationRow ≡ true
btFiniteEvidenceConstructedWitness =
  refl

btFiniteCrossSectionCardinalityWitness :
  finiteCrossSectionCardinality canonicalBTNeckSurgeryObligationRow ≡ 3
btFiniteCrossSectionCardinalityWitness =
  refl

btSmoothS2StillMissingWitness :
  smoothS2CrossSectionDischarged canonicalBTNeckSurgeryObligationRow ≡ false
btSmoothS2StillMissingWitness =
  refl

btSmoothEpsilonNeckStillMissingWitness :
  smoothEpsilonNeckDischarged canonicalBTNeckSurgeryObligationRow ≡ false
btSmoothEpsilonNeckStillMissingWitness =
  refl

btObligationsStillMissingWitness :
  btMissingObligations canonicalBTNeckSurgeryObligationRow
  ≡
  requireSmoothEpsilonNeckModel
  ∷ requireSurgeryContinuationLaw
  ∷ retainDiscreteShellOnlyStatus
  ∷ []
btObligationsStillMissingWitness =
  refl
