module DASHI.Computation.SSSPFindPivotsCoverageCompressionExact where

-- Structural certificate extracted from Duan-Mao-Mao-Shu-Yin (2025),
-- Lemma 3.2 (Finding Pivots).
--
-- The exact graph algorithm is not reimplemented here.  This owner isolates
-- the theorem obligations needed downstream: every relevant vertex is either
-- completed in W or its shortest path visits a complete pivot in P, and the
-- pivot set is compressed relative to W.  No total ordering of S, W, P or the
-- relevant vertices is part of the certificate.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

------------------------------------------------------------------------
-- 1. Exact coverage shape of Lemma 3.2.
------------------------------------------------------------------------

record FindPivotsCoverage : Set₁ where
  constructor findPivotsCoverage
  field
    RelevantVertex : Set
    InWAndComplete : RelevantVertex → Set
    VisitsCompletePivot : RelevantVertex → Set
    coverage :
      (x : RelevantVertex) →
      InWAndComplete x ⊎ VisitsCompletePivot x

open FindPivotsCoverage public

------------------------------------------------------------------------
-- 2. Cardinal compression in denominator-free form.
--
-- The paper states |P| <= |W|/k.  A convenient natural-number certificate is
-- k*|P| <= |W|.  This owner records that denominator-free form as an input
-- witness; a later arithmetic bridge may relate it to floor division.
------------------------------------------------------------------------

record FindPivotsCompression : Set where
  constructor findPivotsCompression
  field
    k sourceCount workCount pivotCount : Nat
    workLinearBound : Set
    pivotCompression : k * pivotCount ≤ workCount

open FindPivotsCompression public

------------------------------------------------------------------------
-- 3. Combined consumer-facing receipt.
------------------------------------------------------------------------

record FindPivotsCertificate : Set₁ where
  constructor findPivotsCertificate
  field
    coverageReceipt : FindPivotsCoverage
    compressionReceipt : FindPivotsCompression
    totalOrderOfRelevantVerticesRequired : Bool
    totalOrderOfRelevantVerticesRequiredIsFalse :
      totalOrderOfRelevantVerticesRequired ≡ false
    totalOrderOfPivotsRequired : Bool
    totalOrderOfPivotsRequiredIsFalse :
      totalOrderOfPivotsRequired ≡ false

open FindPivotsCertificate public

------------------------------------------------------------------------
-- 4. Small exact regression: k=2, one pivot, two work vertices.
------------------------------------------------------------------------

data Relevant2 : Set where
  completedVertex pivotCoveredVertex : Relevant2

data CompletedInW2 : Relevant2 → Set where
  completedWitness : CompletedInW2 completedVertex

data VisitsPivot2 : Relevant2 → Set where
  pivotVisitWitness : VisitsPivot2 pivotCoveredVertex

coverage2 :
  (x : Relevant2) → CompletedInW2 x ⊎ VisitsPivot2 x
coverage2 completedVertex = inj₁ completedWitness
coverage2 pivotCoveredVertex = inj₂ pivotVisitWitness

finiteCoverage2 : FindPivotsCoverage
finiteCoverage2 =
  findPivotsCoverage Relevant2 CompletedInW2 VisitsPivot2 coverage2

-- 2 * 1 <= 2
compression2 : FindPivotsCompression
compression2 =
  findPivotsCompression 2 1 2 1 ⊤ (s≤s (s≤s z≤n))

canonicalFindPivotsCertificate : FindPivotsCertificate
canonicalFindPivotsCertificate =
  findPivotsCertificate
    finiteCoverage2
    compression2
    false refl
    false refl

------------------------------------------------------------------------
-- 5. BIDI consequence.
--
-- Forward execution may choose a compressed pivot carrier.  Backward demand
-- for correctness reopens only the coverage obligations above; it does not
-- reopen a demand for a total distance sort.
------------------------------------------------------------------------

record FindPivotsBidiBoundary : Set where
  constructor findPivotsBidiBoundary
  field
    coverageIsRequired : Bool
    coverageIsRequiredIsTrue : coverageIsRequired ≡ true
    pivotCompressionIsRequired : Bool
    pivotCompressionIsRequiredIsTrue : pivotCompressionIsRequired ≡ true
    fullFrontierSortIsRequired : Bool
    fullFrontierSortIsRequiredIsFalse : fullFrontierSortIsRequired ≡ false

canonicalFindPivotsBidiBoundary : FindPivotsBidiBoundary
canonicalFindPivotsBidiBoundary =
  findPivotsBidiBoundary true refl true refl false refl
