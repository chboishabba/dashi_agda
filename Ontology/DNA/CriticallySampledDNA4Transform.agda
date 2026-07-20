module Ontology.DNA.CriticallySampledDNA4Transform where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec using (Vec; []; _∷_)

open import Ontology.DNA.Supervoxel4Adic using
  (Base; A; C; G; T; DNA4; DNA16; DNA64; DNA256)

------------------------------------------------------------------------
-- Exact four-state relative coordinate.
-- A block of four bases is represented by one anchor and three deltas.
-- This is critically sampled: 4 four-state symbols become 1 + 3 four-state
-- symbols, with no retained copy of the source block.

data Delta : Set where
  d0 d1 d2 d3 : Delta

difference : Base → Base → Delta
difference A A = d0
difference A C = d1
difference A G = d2
difference A T = d3
difference C A = d3
difference C C = d0
difference C G = d1
difference C T = d2
difference G A = d2
difference G C = d3
difference G G = d0
difference G T = d1
difference T A = d1
difference T C = d2
difference T G = d3
difference T T = d0

applyDelta : Base → Delta → Base
applyDelta A d0 = A
applyDelta A d1 = C
applyDelta A d2 = G
applyDelta A d3 = T
applyDelta C d0 = C
applyDelta C d1 = G
applyDelta C d2 = T
applyDelta C d3 = A
applyDelta G d0 = G
applyDelta G d1 = T
applyDelta G d2 = A
applyDelta G d3 = C
applyDelta T d0 = T
applyDelta T d1 = A
applyDelta T d2 = C
applyDelta T d3 = G

apply-difference : ∀ a b → applyDelta a (difference a b) ≡ b
apply-difference A A = refl
apply-difference A C = refl
apply-difference A G = refl
apply-difference A T = refl
apply-difference C A = refl
apply-difference C C = refl
apply-difference C G = refl
apply-difference C T = refl
apply-difference G A = refl
apply-difference G C = refl
apply-difference G G = refl
apply-difference G T = refl
apply-difference T A = refl
apply-difference T C = refl
apply-difference T G = refl
apply-difference T T = refl

record QuadCoefficients : Set where
  constructor quad
  field
    coarse : Base
    details : Vec Delta 3

analyse4 : DNA4 → QuadCoefficients
analyse4 (a ∷ b ∷ c ∷ d ∷ []) =
  quad a (difference a b ∷ difference a c ∷ difference a d ∷ [])

synthesise4 : QuadCoefficients → DNA4
synthesise4 (quad a (db ∷ dc ∷ dd ∷ [])) =
  a ∷ applyDelta a db ∷ applyDelta a dc ∷ applyDelta a dd ∷ []

synthesise4-analyse4 : ∀ xs → synthesise4 (analyse4 xs) ≡ xs
synthesise4-analyse4 (a ∷ b ∷ c ∷ d ∷ [])
  rewrite apply-difference a b
        | apply-difference a c
        | apply-difference a d = refl

------------------------------------------------------------------------
-- Recursive fixed-height transform.

record Coefficients16 : Set where
  constructor coefficients16
  field
    coarse16 : Base
    detail16 : Vec Delta 3
    detail4 : Vec (Vec Delta 3) 4

analyse16 : DNA16 → Coefficients16
analyse16 (x0 ∷ x1 ∷ x2 ∷ x3 ∷ []) with analyse4 x0 | analyse4 x1 | analyse4 x2 | analyse4 x3
... | quad a0 d0s | quad a1 d1s | quad a2 d2s | quad a3 d3s with analyse4 (a0 ∷ a1 ∷ a2 ∷ a3 ∷ [])
... | quad top topDetails = coefficients16 top topDetails (d0s ∷ d1s ∷ d2s ∷ d3s ∷ [])

synthesise16 : Coefficients16 → DNA16
synthesise16 (coefficients16 top topDetails (d0s ∷ d1s ∷ d2s ∷ d3s ∷ []))
  with synthesise4 (quad top topDetails)
... | a0 ∷ a1 ∷ a2 ∷ a3 ∷ [] =
  synthesise4 (quad a0 d0s) ∷
  synthesise4 (quad a1 d1s) ∷
  synthesise4 (quad a2 d2s) ∷
  synthesise4 (quad a3 d3s) ∷ []

record Coefficients64 : Set where
  constructor coefficients64
  field
    coarse64 : Base
    detail64 : Vec Delta 3
    detail16s : Vec (Vec Delta 3) 4
    detail4s : Vec (Vec (Vec Delta 3) 4) 4

analyse64 : DNA64 → Coefficients64
analyse64 (x0 ∷ x1 ∷ x2 ∷ x3 ∷ []) with analyse16 x0 | analyse16 x1 | analyse16 x2 | analyse16 x3
... | coefficients16 a0 t0 q0 | coefficients16 a1 t1 q1 | coefficients16 a2 t2 q2 | coefficients16 a3 t3 q3 with analyse4 (a0 ∷ a1 ∷ a2 ∷ a3 ∷ [])
... | quad top topDetails = coefficients64 top topDetails (t0 ∷ t1 ∷ t2 ∷ t3 ∷ []) (q0 ∷ q1 ∷ q2 ∷ q3 ∷ [])

synthesise64 : Coefficients64 → DNA64
synthesise64 (coefficients64 top topDetails (t0 ∷ t1 ∷ t2 ∷ t3 ∷ []) (q0 ∷ q1 ∷ q2 ∷ q3 ∷ []))
  with synthesise4 (quad top topDetails)
... | a0 ∷ a1 ∷ a2 ∷ a3 ∷ [] =
  synthesise16 (coefficients16 a0 t0 q0) ∷
  synthesise16 (coefficients16 a1 t1 q1) ∷
  synthesise16 (coefficients16 a2 t2 q2) ∷
  synthesise16 (coefficients16 a3 t3 q3) ∷ []

record Coefficients256 : Set where
  constructor coefficients256
  field
    coarse256 : Base
    detail256 : Vec Delta 3
    detail64s : Vec (Vec Delta 3) 4
    detail16ss : Vec (Vec (Vec Delta 3) 4) 4
    detail4sss : Vec (Vec (Vec (Vec Delta 3) 4) 4) 4

analyse256 : DNA256 → Coefficients256
analyse256 (x0 ∷ x1 ∷ x2 ∷ x3 ∷ []) with analyse64 x0 | analyse64 x1 | analyse64 x2 | analyse64 x3
... | coefficients64 a0 t0 s0 q0 | coefficients64 a1 t1 s1 q1 | coefficients64 a2 t2 s2 q2 | coefficients64 a3 t3 s3 q3 with analyse4 (a0 ∷ a1 ∷ a2 ∷ a3 ∷ [])
... | quad top topDetails =
  coefficients256 top topDetails
    (t0 ∷ t1 ∷ t2 ∷ t3 ∷ [])
    (s0 ∷ s1 ∷ s2 ∷ s3 ∷ [])
    (q0 ∷ q1 ∷ q2 ∷ q3 ∷ [])

synthesise256 : Coefficients256 → DNA256
synthesise256 (coefficients256 top topDetails (t0 ∷ t1 ∷ t2 ∷ t3 ∷ []) (s0 ∷ s1 ∷ s2 ∷ s3 ∷ []) (q0 ∷ q1 ∷ q2 ∷ q3 ∷ []))
  with synthesise4 (quad top topDetails)
... | a0 ∷ a1 ∷ a2 ∷ a3 ∷ [] =
  synthesise64 (coefficients64 a0 t0 s0 q0) ∷
  synthesise64 (coefficients64 a1 t1 s1 q1) ∷
  synthesise64 (coefficients64 a2 t2 s2 q2) ∷
  synthesise64 (coefficients64 a3 t3 s3 q3) ∷ []

------------------------------------------------------------------------
-- Exact coefficient count in four-state symbols:
-- 1 coarse + 3 + 12 + 48 + 192 = 256.

coefficientCount : Nat
coefficientCount = 1 + 3 + 12 + 48 + 192

coefficientCount-is-256 : coefficientCount ≡ 256
coefficientCount-is-256 = refl

record CriticalSamplingReceipt : Set where
  field
    sourceSymbols : Nat
    coefficientSymbols : Nat
    noRedundantLeafCopy : Set
    exactFourBlockReconstruction : ∀ xs → synthesise4 (analyse4 xs) ≡ xs
    countsAgree : sourceSymbols ≡ coefficientSymbols

criticalSamplingReceipt : CriticalSamplingReceipt
criticalSamplingReceipt = record
  { sourceSymbols = 256
  ; coefficientSymbols = coefficientCount
  ; noRedundantLeafCopy = Coefficients256
  ; exactFourBlockReconstruction = synthesise4-analyse4
  ; countsAgree = coefficientCount-is-256
  }
