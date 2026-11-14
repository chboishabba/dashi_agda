module DASHI.Education.DigitalESDEfSCanonicalReuseAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDEvidenceBraidTensionExact as Braid
import DASHI.Education.DigitalESDEfSIndependentChallengeExact as EfS
import DASHI.Education.DigitalESDEfSIndependentDerivationExact as Derivation
import DASHI.Biology.AliceBrownCorpusLoom as Alice
import DASHI.Core.RelationalEpistemicProcessSourceBridgeExact as Relational
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Education.EducationSituatedInvestmentTrajectoryExact as Trajectory
import DASHI.Education.DigitalESDDBNativeAcademicWorldExecutionExact as World

-- Reuses existing typed epistemic-braid vocabulary rather than adding a new
-- conflict ontology. An outcome classification is an authored inference,
-- not an automatic verdict about the underlying source.
relationFor : EfS.ComparisonOutcome → Braid.BraidRelation
relationFor EfS.candidateConvergence = Braid.convergence
relationFor EfS.candidateTension = Braid.productiveTension
relationFor EfS.unmatchedEfSRequirement = Braid.scopeDifference
relationFor EfS.openEmpiricalComparison = Braid.unresolvedConflict

record EfSReuseReceipt : Set where
  constructor reuse-receipt
  field
    challenge : EfS.ComparisonReceipt
    braid : Braid.TensionReceipt
    braidMatchesChallenge : Braid.TensionReceipt.relation braid ≡
      relationFor (EfS.ComparisonReceipt.outcome challenge)
    sourceFibresRemainIndependent : Bool
    sourceFibresRemainIndependentIsTrue : sourceFibresRemainIndependent ≡ true
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

open EfSReuseReceipt public

reuse : (r : EfS.ComparisonReceipt) → EfSReuseReceipt
reuse r = reuse-receipt r
  (Braid.tension-receipt
    (Derivation.IndependentThemeReceipt.sourceReference
      (EfS.ComparisonReceipt.independentEfS r))
    "DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact"
    (Derivation.IndependentThemeReceipt.sourceReference
      (EfS.ComparisonReceipt.independentEfS r))
    "DASHI.Biology.EducationCorpusSourceRegistry"
    (relationFor (EfS.ComparisonReceipt.outcome r))
    (EfS.ComparisonReceipt.challengeToDigitalFramework r))
  refl true refl true refl

canonicalReuse : List EfSReuseReceipt
canonicalReuse =
  reuse EfS.systemsComparison ∷
  reuse EfS.valuesComparison ∷
  reuse EfS.futuresComparison ∷
  reuse EfS.collectiveComparison ∷
  reuse EfS.ecologicalComparison ∷
  reuse EfS.enactmentComparison ∷ []

existingCorpus : Alice.AliceBrownCorpusLoom
existingCorpus = Alice.canonicalAliceBrownCorpusLoom

existingTwoEyedBoundary : TwoEyed.KimmererTwoEyedSeeingBoundary
existingTwoEyedBoundary = TwoEyed.canonicalKimmererTwoEyedSeeingBoundary

existingRelationalBoundary : Relational.RelationalEpistemicProcessBoundary
existingRelationalBoundary = Relational.canonicalRelationalEpistemicProcessBoundary

-- The 19+ coordinate learning/evidence trajectory and the DB-native
-- manuscript extraction are explicitly reused as owners, NOT flattened into
-- the 6 EfS themes or 7 digital principles.
educationTrajectoryCoordinates : List Trajectory.TrajectoryCoordinate
educationTrajectoryCoordinates = Trajectory.trajectoryCoordinates

dbNativeCoordinateCount : Nat
dbNativeCoordinateCount = World.extractionCoordinateCount

data SourcePairingIsEmpiricalEffect : Set where
data InterpretiveBridgeOverridesCommunityAuthority : Set where
data ParserNominationPaysEfSClaim : Set where

sourcePairingDoesNotProveEffect : SourcePairingIsEmpiricalEffect → ⊥
sourcePairingDoesNotProveEffect ()
interpretationDoesNotOverrideAuthority : InterpretiveBridgeOverridesCommunityAuthority → ⊥
interpretationDoesNotOverrideAuthority ()
parserNominationCannotPayClaim : ParserNominationPaysEfSClaim → ⊥
parserNominationCannotPayClaim ()
