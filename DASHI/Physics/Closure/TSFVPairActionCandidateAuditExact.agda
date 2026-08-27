module DASHI.Physics.Closure.TSFVPairActionCandidateAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.HistoryLocalActionAccumulationExact as Action
import DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCouplingRequirement as CrossBand
import DASHI.Physics.Closure.TSFVLocalActionCandidateAuditExact as V3Candidate
import DASHI.Physics.Closure.W4StrictPhysicalNextObligation as Next
import DASHI.Physics.Closure.W4SurrogateScaleSettingBoundary as Surrogate

------------------------------------------------------------------------
-- Second TSFV action-candidate audit: pair-sensitive local contribution.
--
-- The existing Candidate256 cross-band law already supplies a Nat-valued
-- observable I× on ordered pairs of quotient classes.  Unlike the first v3
-- candidate, this local contribution sees both step endpoints.  The generic
-- action accumulator therefore turns it into an additive finite-history
-- functional without inventing a new pair geometry.
------------------------------------------------------------------------

pairLocalActionSystem : Action.LocalActionSystem
pairLocalActionSystem =
  record
    { State = Surrogate.Candidate256QuotientClass
    ; localAction = λ left right →
        CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.I×
          Next.canonicalCandidate256QuotientLaw
          (left , right)
    ; actionReading =
        "Structural pair-action candidate: reuse the existing Candidate256 cross-band observable I×(q1,q2) as a two-endpoint local contribution, then accumulate it additively over finite traces."
    }

candidateLeft : Surrogate.Candidate256QuotientClass
candidateLeft = Surrogate.candidate256LeftQuotientClass

candidateRight : Surrogate.Candidate256QuotientClass
candidateRight = Surrogate.candidate256RightQuotientClass

pairCandidateSymmetricAtWitness :
  Action.localAction pairLocalActionSystem candidateLeft candidateRight
  ≡
  Action.localAction pairLocalActionSystem candidateRight candidateLeft
pairCandidateSymmetricAtWitness =
  CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.I×SymmetricAtWitness
    Next.canonicalCandidate256QuotientLaw

pairCandidateDiagonalSeparates :
  Action.localAction pairLocalActionSystem candidateLeft candidateLeft
  ≡
  Action.localAction pairLocalActionSystem candidateRight candidateRight
  → ⊥
pairCandidateDiagonalSeparates =
  CrossBand.ChemistryRightLimitsQuotientCrossBandLaw.I×BandSensitivityWitness
    Next.canonicalCandidate256QuotientLaw

pairCandidateTrace : List (Action.Step pairLocalActionSystem)
pairCandidateTrace =
  (candidateLeft , candidateRight)
  ∷ (candidateRight , candidateLeft)
  ∷ []

pairCandidateAction : Nat
pairCandidateAction =
  Action.historyAction pairLocalActionSystem pairCandidateTrace

------------------------------------------------------------------------
-- Exact comparison with the first v3 candidate.
------------------------------------------------------------------------

v3CandidateIsDestinationOnly :
  (sourceLeft sourceRight destination : Surrogate.Candidate256QuotientClass) →
  Action.localAction V3Candidate.tsfvLocalActionSystem sourceLeft destination
  ≡
  Action.localAction V3Candidate.tsfvLocalActionSystem sourceRight destination
v3CandidateIsDestinationOnly sourceLeft sourceRight destination = refl

data ActionCandidateAxis : Set where
  finiteTraceAdditivityAxis : ActionCandidateAxis
  tInvarianceAxis : ActionCandidateAxis
  twoEndpointSensitivityAxis : ActionCandidateAxis
  witnessSymmetryAxis : ActionCandidateAxis
  nontrivialSeparationAxis : ActionCandidateAxis
  physicalCalibrationAxis : ActionCandidateAxis

data CandidateAssessment : Set where
  provedHere : CandidateAssessment
  provedElsewhere : CandidateAssessment
  missing : CandidateAssessment
  notApplicable : CandidateAssessment

record CandidateComparison : Set where
  field
    v3Additivity : CandidateAssessment
    v3TInvariance : CandidateAssessment
    v3TwoEndpointSensitivity : CandidateAssessment

    pairAdditivity : CandidateAssessment
    pairWitnessSymmetry : CandidateAssessment
    pairNontrivialSeparation : CandidateAssessment
    pairTInvariance : CandidateAssessment

    physicalCalibration : CandidateAssessment
    comparisonReading : String

open CandidateComparison public

canonicalCandidateComparison : CandidateComparison
canonicalCandidateComparison =
  record
    { v3Additivity = provedElsewhere
    ; v3TInvariance = provedElsewhere
    ; v3TwoEndpointSensitivity = missing
    ; pairAdditivity = provedHere
    ; pairWitnessSymmetry = provedHere
    ; pairNontrivialSeparation = provedHere
    ; pairTInvariance = missing
    ; physicalCalibration = missing
    ; comparisonReading =
        "The v3 candidate has exact T-invariance but is destination-only.  The cross-band candidate is genuinely pair-valued, additive over finite traces, symmetric at the canonical mixed witness, and nontrivial on canonical diagonal witnesses, but a Candidate256 T-invariance theorem and physical action calibration are not yet supplied."
    }

pairTraceAdditivityAvailable :
  (left right : List (Action.Step pairLocalActionSystem)) →
  Action.historyAction pairLocalActionSystem (left Data.List.++ right)
  ≡
  Action.historyAction pairLocalActionSystem left
  + Action.historyAction pairLocalActionSystem right
pairTraceAdditivityAvailable = Action.historyActionAppend pairLocalActionSystem

record PairActionCandidateBoundary : Set where
  constructor pairActionCandidateBoundary
  field
    pairObservableAlreadyPhysicalAction : Bool
    pairObservableAlreadyPhysicalActionIsFalse :
      pairObservableAlreadyPhysicalAction ≡ false

    witnessSymmetryProvesGlobalTimeReversalInvariance : Bool
    witnessSymmetryProvesGlobalTimeReversalInvarianceIsFalse :
      witnessSymmetryProvesGlobalTimeReversalInvariance ≡ false

    diagonalBandSensitivityIsEmpiricalActionCalibration : Bool
    diagonalBandSensitivityIsEmpiricalActionCalibrationIsFalse :
      diagonalBandSensitivityIsEmpiricalActionCalibration ≡ false

canonicalPairActionCandidateBoundary : PairActionCandidateBoundary
canonicalPairActionCandidateBoundary =
  pairActionCandidateBoundary
    false refl
    false refl
    false refl
