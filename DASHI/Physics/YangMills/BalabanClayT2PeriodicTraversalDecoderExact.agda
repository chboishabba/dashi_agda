module DASHI.Physics.YangMills.BalabanClayT2PeriodicTraversalDecoderExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (length; _++_)

open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact using (SignedAxis4)
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (Product; pair; first; second)
import DASHI.Physics.YangMills.BalabanClayT2PeriodicAdjacencyBFSExact as Periodic
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Carrier
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Concrete root-plus-word replay.  BFS and child ordering still choose the
-- word; decoding is no longer an arbitrary field supplied by an instance.
------------------------------------------------------------------------

reverseOrientation : Bool → Bool
reverseOrientation false = true
reverseOrientation true = false

reverseDirection : SignedAxis4 → SignedAxis4
reverseDirection d = pair (first d) (reverseOrientation (second d))

replayTerminal :
  ∀ {n} → Carrier.PeriodicBlock n → List SignedAxis4 → Carrier.PeriodicBlock n
replayTerminal block [] = block
replayTerminal block (direction ∷ rest) =
  replayTerminal (Periodic.signedStep block direction) rest

replayVisited :
  ∀ {n} → Carrier.PeriodicBlock n → List SignedAxis4 → Carrier.PeriodicPolymer n
replayVisited block [] = block ∷ []
replayVisited block (direction ∷ rest) =
  block ∷ replayVisited (Periodic.signedStep block direction) rest

tailVisited :
  ∀ {n} → Carrier.PeriodicBlock n → List SignedAxis4 → Carrier.PeriodicPolymer n
tailVisited root [] = []
tailVisited root (direction ∷ rest) =
  replayVisited (Periodic.signedStep root direction) rest

replayStartsAtRoot :
  ∀ {n} (root : Carrier.PeriodicBlock n) word →
  replayVisited root word ≡ root ∷ tailVisited root word
replayStartsAtRoot root [] = refl
replayStartsAtRoot root (direction ∷ rest) = refl

replayLengthExact :
  ∀ {n} (root : Carrier.PeriodicBlock n) word →
  length (replayVisited root word) ≡ suc (length word)
replayLengthExact root [] = refl
replayLengthExact root (direction ∷ rest)
  rewrite replayLengthExact (Periodic.signedStep root direction) rest = refl

replayAppendTerminal :
  ∀ {n} (root : Carrier.PeriodicBlock n) left right →
  replayTerminal root (left ++ right)
  ≡ replayTerminal (replayTerminal root left) right
replayAppendTerminal root [] right = refl
replayAppendTerminal root (direction ∷ left) right =
  replayAppendTerminal (Periodic.signedStep root direction) left right

record DirectionInverseLaw (n : Nat) : Set₁ where
  field
    forwardThenReverse : ∀ (block : Carrier.PeriodicBlock n) (direction : SignedAxis4) →
      Periodic.signedStep
        (Periodic.signedStep block direction)
        (reverseDirection direction)
      ≡ block

open DirectionInverseLaw public

singleEdgeReturns :
  ∀ {n} (inverseLaw : DirectionInverseLaw n) block direction →
  replayTerminal block (direction ∷ reverseDirection direction ∷ []) ≡ block
singleEdgeReturns inverseLaw block direction =
  forwardThenReverse inverseLaw block direction

record CanonicalDepthFirstWord {n}
    (polymer : Periodic.ConnectedPeriodicPolymer n)
    (bfs : Periodic.CertifiedPeriodicBreadthFirstData n polymer) : Set₁ where
  field
    word : List SignedAxis4
    generatedFromParentTree : Set
    childrenFollowFixedSignedAxisOrder : Set
    everyParentEdgeForwardAndBackward : Set
    wordLengthTwiceTreeEdges : Set

open CanonicalDepthFirstWord public

record CanonicalDecoderCoverage {n}
    (polymer : Periodic.ConnectedPeriodicPolymer n)
    (bfs : Periodic.CertifiedPeriodicBreadthFirstData n polymer)
    (dfs : CanonicalDepthFirstWord polymer bfs) : Set₁ where
  field
    duplicateElimination : Carrier.PeriodicPolymer n → Carrier.PeriodicPolymer n
    duplicateEliminationPreservesMembership : Set
    duplicateEliminationIsDuplicateFree : Set

    coverageExact :
      duplicateElimination
        (replayVisited (Periodic.root bfs) (word dfs))
      ≡ Periodic.blocks polymer

open CanonicalDecoderCoverage public

decodePeriodicPolymer :
  ∀ {n polymer bfs}
    (dfs : CanonicalDepthFirstWord {n} polymer bfs)
    (coverage : CanonicalDecoderCoverage polymer bfs dfs) →
  Carrier.PeriodicBlock n → List SignedAxis4 → Carrier.PeriodicPolymer n
decodePeriodicPolymer dfs coverage root word =
  duplicateElimination coverage (replayVisited root word)

decodeCanonicalTrace :
  ∀ {n polymer bfs}
    (dfs : CanonicalDepthFirstWord {n} polymer bfs)
    (coverage : CanonicalDecoderCoverage polymer bfs dfs) →
  decodePeriodicPolymer dfs coverage (Periodic.root bfs) (word dfs)
  ≡ Periodic.blocks polymer
decodeCanonicalTrace dfs coverage = coverageExact coverage

record ParentDistanceTermination {n}
    (polymer : Periodic.ConnectedPeriodicPolymer n)
    (bfs : Periodic.CertifiedPeriodicBreadthFirstData n polymer) : Set₁ where
  field
    parentChain : Carrier.PeriodicBlock n → List (Carrier.PeriodicBlock n)
    chainBeginsAtBlock : ∀ (block : Carrier.PeriodicBlock n) → Set
    everySuccessorIsParent : ∀ (block : Carrier.PeriodicBlock n) → Set
    distanceStrictlyDecreasesAtEveryStep : ∀ (block : Carrier.PeriodicBlock n) → Set
    chainEndsAtRoot : ∀ (block : Carrier.PeriodicBlock n) → Set
    noRepeatedNonRootBlock : ∀ (block : Carrier.PeriodicBlock n) → Set

open ParentDistanceTermination public

periodicReplayDecoderLevel : ProofLevel
periodicReplayDecoderLevel = machineChecked

periodicDirectionInverseInputsLevel : ProofLevel
periodicDirectionInverseInputsLevel = conditional

periodicBFSParentTerminationInputsLevel : ProofLevel
periodicBFSParentTerminationInputsLevel = conditional

periodicDFSCoverageInputsLevel : ProofLevel
periodicDFSCoverageInputsLevel = conditional
