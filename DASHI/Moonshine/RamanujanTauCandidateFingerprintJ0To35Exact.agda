module DASHI.Moonshine.RamanujanTauCandidateFingerprintJ0To35Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "A Course in Arithmetic", Graduate Texts in Mathematics 7,
-- Springer, 1973.
-- DOI: 10.1007/978-1-4684-9884-4.
--
-- Toshitsune Miyake,
-- "Modular Forms", Springer Monographs in Mathematics,
-- Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
--
-- DASHI CONTRIBUTION
--
-- Give every level in the unbiased representation scan an independent
-- arithmetic fingerprint from Ramanujan's normalized weight-12 cusp-form
-- coefficients.  The scan consists of level 2 plus all odd levels
-- 1,3,...,71.  Ogg membership is not consulted when defining the table.
--
-- The existing small Hecke checksum module is reused at levels 2,3,9,27.
-- This file records finite exact coefficients only; it does not construct the
-- analytic modular form Delta, a global Hecke algebra, or an Ogg selector.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])

import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Moonshine.CandidateLevelRepresentationHeckeSquareExact as Candidate
import DASHI.Moonshine.RamanujanTauHecke23Exact as Small

tauAtCandidateLevel : Candidate.CandidateLevel → ℤ
tauAtCandidateLevel Candidate.spinorLevel2 = -[1+ 23 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j0) = + 1
tauAtCandidateLevel (Candidate.spatialLevel Spin.j1) = + 252
tauAtCandidateLevel (Candidate.spatialLevel Spin.j2) = + 4830
tauAtCandidateLevel (Candidate.spatialLevel Spin.j3) = -[1+ 16743 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j4) = -[1+ 113642 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j5) = + 534612
tauAtCandidateLevel (Candidate.spatialLevel Spin.j6) = -[1+ 577737 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j7) = + 1217160
tauAtCandidateLevel (Candidate.spatialLevel Spin.j8) = -[1+ 6905933 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j9) = + 10661420
tauAtCandidateLevel (Candidate.spatialLevel Spin.j10) = -[1+ 4219487 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j11) = + 18643272
tauAtCandidateLevel (Candidate.spatialLevel Spin.j12) = -[1+ 25499224 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j13) = -[1+ 73279079 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j14) = + 128406630
tauAtCandidateLevel (Candidate.spatialLevel Spin.j15) = -[1+ 52843167 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j16) = + 134722224
tauAtCandidateLevel (Candidate.spatialLevel Spin.j17) = -[1+ 80873519 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j18) = -[1+ 182213313 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j19) = -[1+ 145589975 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j20) = + 308120442
tauAtCandidateLevel (Candidate.spatialLevel Spin.j21) = -[1+ 17125707 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j22) = -[1+ 548895689 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j23) = + 2687348496
tauAtCandidateLevel (Candidate.spatialLevel Spin.j24) = -[1+ 1696965206 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j25) = -[1+ 1740295367 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j26) = -[1+ 1596055697 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j27) = + 2582175960
tauAtCandidateLevel (Candidate.spatialLevel Spin.j28) = + 2686677840
tauAtCandidateLevel (Candidate.spatialLevel Spin.j29) = -[1+ 5189203739 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j30) = + 6956478662
tauAtCandidateLevel (Candidate.spatialLevel Spin.j31) = + 1902838392
tauAtCandidateLevel (Candidate.spatialLevel Spin.j32) = -[1+ 2790474539 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j33) = -[1+ 15481826883 ]
tauAtCandidateLevel (Candidate.spatialLevel Spin.j34) = + 4698104544
tauAtCandidateLevel (Candidate.spatialLevel Spin.j35) = + 9791485272

record CandidateTauFingerprint : Set where
  constructor candidate-tau-fingerprint
  field
    candidate : Candidate.CandidateLevel
    level : Nat
    levelIsCandidate : level ≡ Candidate.candidateLevelNat candidate
    tauValue : ℤ
    tauValueIsCanonical : tauValue ≡ tauAtCandidateLevel candidate

open CandidateTauFingerprint public

canonicalTauFingerprint :
  (candidate : Candidate.CandidateLevel) → CandidateTauFingerprint
canonicalTauFingerprint candidate =
  candidate-tau-fingerprint
    candidate
    (Candidate.candidateLevelNat candidate)
    refl
    (tauAtCandidateLevel candidate)
    refl

------------------------------------------------------------------------
-- Reuse the already-checked small Hecke coefficient lane as exact anchors.
------------------------------------------------------------------------

tauAt2MatchesExisting :
  tauAtCandidateLevel Candidate.spinorLevel2 ≡ Small.tau2
tauAt2MatchesExisting = refl

tauAt3MatchesExisting :
  tauAtCandidateLevel (Candidate.spatialLevel Spin.j1) ≡ Small.tau3
tauAt3MatchesExisting = refl

tauAt9MatchesExisting :
  tauAtCandidateLevel (Candidate.spatialLevel Spin.j4) ≡ Small.tau9
tauAt9MatchesExisting = refl

tauAt27MatchesExisting :
  tauAtCandidateLevel (Candidate.spatialLevel Spin.j13) ≡ Small.tau27
tauAt27MatchesExisting = refl

------------------------------------------------------------------------
-- Representative Ogg and non-Ogg rows are both first-class fingerprints.
------------------------------------------------------------------------

tauAt7 :
  tauAtCandidateLevel (Candidate.spatialLevel Spin.j3) ≡ -[1+ 16743 ]
tauAt7 = refl

tauAt15 :
  tauAtCandidateLevel (Candidate.spatialLevel Spin.j7) ≡ + 1217160
tauAt15 = refl

tauAt29 :
  tauAtCandidateLevel (Candidate.spatialLevel Spin.j14) ≡ + 128406630
tauAt29 = refl

tauAt35 :
  tauAtCandidateLevel (Candidate.spatialLevel Spin.j17) ≡ -[1+ 80873519 ]
tauAt35 = refl

tauAt43 :
  tauAtCandidateLevel (Candidate.spatialLevel Spin.j21) ≡ -[1+ 17125707 ]
tauAt43 = refl

tauAt53 :
  tauAtCandidateLevel (Candidate.spatialLevel Spin.j26) ≡ -[1+ 1596055697 ]
tauAt53 = refl

tauAt67 :
  tauAtCandidateLevel (Candidate.spatialLevel Spin.j33) ≡ -[1+ 15481826883 ]
tauAt67 = refl

tauAt71 :
  tauAtCandidateLevel (Candidate.spatialLevel Spin.j35) ≡ + 9791485272
tauAt71 = refl

record RamanujanTauCandidateBoundary : Set where
  field
    completeCandidateFingerprintThrough71 : Bool
    completeCandidateFingerprintThrough71IsTrue :
      completeCandidateFingerprintThrough71 ≡ true

    OggLabelsUsedToDefineTauTable : Bool
    OggLabelsUsedToDefineTauTableIsFalse :
      OggLabelsUsedToDefineTauTable ≡ false

    analyticDeltaConstructedHere : Bool
    analyticDeltaConstructedHereIsFalse :
      analyticDeltaConstructedHere ≡ false

    tauFingerprintClaimedToCharacterizeOgg : Bool
    tauFingerprintClaimedToCharacterizeOggIsFalse :
      tauFingerprintClaimedToCharacterizeOgg ≡ false

canonicalRamanujanTauCandidateBoundary : RamanujanTauCandidateBoundary
canonicalRamanujanTauCandidateBoundary =
  record
    { completeCandidateFingerprintThrough71 = true
    ; completeCandidateFingerprintThrough71IsTrue = refl
    ; OggLabelsUsedToDefineTauTable = false
    ; OggLabelsUsedToDefineTauTableIsFalse = refl
    ; analyticDeltaConstructedHere = false
    ; analyticDeltaConstructedHereIsFalse = refl
    ; tauFingerprintClaimedToCharacterizeOgg = false
    ; tauFingerprintClaimedToCharacterizeOggIsFalse = refl
    }
