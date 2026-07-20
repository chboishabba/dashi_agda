module DASHI.Philosophy.InterpretationStrata where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Four distinct claim strata.
--
-- Mathematical inhabitation, structural interpretation, philosophical
-- argument, and empirical/political promotion are not interchangeable.

data ClaimStratum : Set where
  mathematicalTheorem :
    ClaimStratum

  structuralInterpretation :
    ClaimStratum

  philosophicalThesis :
    ClaimStratum

  empiricalPoliticalClaim :
    ClaimStratum

record StratumBoundary : Set where
  constructor mkStratumBoundary
  field
    stratum :
      ClaimStratum

    boundaryLabel :
      String

    machineProofCanCloseThisStratum :
      Bool

    metaphorOrModelAssignment :
      Bool

    philosophicalArgumentRequired :
      Bool

    externalEvidenceRequired :
      Bool

    directCrossStratumPromotionAllowed :
      Bool

open StratumBoundary public

mathematicalTheoremBoundary :
  StratumBoundary
mathematicalTheoremBoundary =
  mkStratumBoundary
    mathematicalTheorem
    "machine-checkable mathematical theorem"
    true
    false
    false
    false
    false

structuralInterpretationBoundary :
  StratumBoundary
structuralInterpretationBoundary =
  mkStratumBoundary
    structuralInterpretation
    "explicit structural interpretation; not a theorem about society"
    false
    true
    false
    false
    false

philosophicalThesisBoundary :
  StratumBoundary
philosophicalThesisBoundary =
  mkStratumBoundary
    philosophicalThesis
    "arguable philosophical thesis; no automatic mathematical promotion"
    false
    false
    true
    false
    false

empiricalPoliticalClaimBoundary :
  StratumBoundary
empiricalPoliticalClaimBoundary =
  mkStratumBoundary
    empiricalPoliticalClaim
    "empirical or political claim requiring evidence and authority"
    false
    false
    true
    true
    false

canonicalStratumBoundaries :
  List StratumBoundary
canonicalStratumBoundaries =
  mathematicalTheoremBoundary
  ∷ structuralInterpretationBoundary
  ∷ philosophicalThesisBoundary
  ∷ empiricalPoliticalClaimBoundary
  ∷ []

noDirectPromotionFromInterpretation :
  directCrossStratumPromotionAllowed structuralInterpretationBoundary
  ≡
  false
noDirectPromotionFromInterpretation =
  refl

empiricalClaimsNeedExternalEvidence :
  externalEvidenceRequired empiricalPoliticalClaimBoundary
  ≡
  true
empiricalClaimsNeedExternalEvidence =
  refl
