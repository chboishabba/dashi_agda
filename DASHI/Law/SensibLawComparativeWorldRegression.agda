module DASHI.Law.SensibLawComparativeWorldRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawComparativeWorldIRExact as C
import DASHI.Law.SensibLawPabaiComparativeWorldExact as P

worldDifferenceStillDoesNotImplyAnswerDifference :
  C.worldsMayDifferWithoutAnswerDiffering
    C.canonicalComparativeWorldBoundary
  ≡ true
worldDifferenceStillDoesNotImplyAnswerDifference = refl

queryIndexStillRequired :
  C.queryIndexRequired
    C.canonicalComparativeWorldBoundary
  ≡ true
queryIndexStillRequired = refl

proofOutcomeStillNotOwnCause :
  C.proofOutcomeIsNotOwnCause
    C.canonicalComparativeWorldBoundary
  ≡ true
proofOutcomeStillNotOwnCause = refl

comparisonStillDoesNotCreateAuthority :
  C.comparisonCreatesAuthority
    C.canonicalComparativeWorldBoundary
  ≡ false
comparisonStillDoesNotCreateAuthority = refl

comparisonStillDoesNotCreateTruth :
  C.comparisonCreatesTruth
    C.canonicalComparativeWorldBoundary
  ≡ false
comparisonStillDoesNotCreateTruth = refl

pabaiW0StillReachable :
  P.w0Reachable
    P.canonicalPabaiComparativeBoundary
  ≡ true
pabaiW0StillReachable = refl

pabaiW1StillDefeated :
  P.w1Defeated
    P.canonicalPabaiComparativeBoundary
  ≡ true
pabaiW1StillDefeated = refl

pabaiW2StillReopenedCandidate :
  P.w2ReopenedCandidate
    P.canonicalPabaiComparativeBoundary
  ≡ true
pabaiW2StillReopenedCandidate = refl

pabaiRepairStillNotCurrentLaw :
  P.candidateRepairPromotedToCurrentLaw
    P.canonicalPabaiComparativeBoundary
  ≡ false
pabaiRepairStillNotCurrentLaw = refl

flatWorldDifferenceStillCannotDetermineAnswer :
  C.Query.AdequateFor C.flatDifferenceOnly C.demoSemantics C.dutyRouteQuery → ⊥
flatWorldDifferenceStillCannotDetermineAnswer =
  C.flatWorldDifferenceDoesNotDetermineAnswer
