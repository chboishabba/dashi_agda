module DASHI.Physics.Closure.NSTriadKNSignedCrossShellAlmostOrthogonalityRound29Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- State the reusable pre-TT* theorem at the cross-shell level. Every signed
-- shell-pairing keeps its sign and receives one local envelope. Finite
-- aggregation proves that a cutoff-independent decay-mass bound controls the
-- complete signed pairing. The actual operator-valued Cotlar--Stein estimate
-- remains a separate physical theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst; sym)

record SignedCrossShellCell : Set where
  constructor signed-cross-shell-cell
  field
    leftShell rightShell : Nat
    signedPairing : ℚ
    localEnvelope : ℚ
    signedPairingBound : ∣ signedPairing ∣ ≤ localEnvelope

open SignedCrossShellCell public

sumSignedPairings : List SignedCrossShellCell → ℚ
sumSignedPairings [] = 0ℚ
sumSignedPairings (cell ∷ rest) =
  signedPairing cell + sumSignedPairings rest

sumLocalEnvelopes : List SignedCrossShellCell → ℚ
sumLocalEnvelopes [] = 0ℚ
sumLocalEnvelopes (cell ∷ rest) =
  localEnvelope cell + sumLocalEnvelopes rest

crossShellSignedAggregation :
  (cells : List SignedCrossShellCell) →
  ∣ sumSignedPairings cells ∣ ≤ sumLocalEnvelopes cells
crossShellSignedAggregation [] =
  subst
    (λ value → value ≤ 0ℚ)
    (sym (ℚₚ.0≤p⇒∣p∣≡p ℚₚ.≤-refl))
    ℚₚ.≤-refl
crossShellSignedAggregation (cell ∷ rest) =
  ℚₚ.≤-trans
    (ℚₚ.∣p+q∣≤∣p∣+∣q∣
      (signedPairing cell)
      (sumSignedPairings rest))
    (ℚₚ.+-mono-≤
      (signedPairingBound cell)
      (crossShellSignedAggregation rest))

record CrossShellDecayCertificate
    (cells : List SignedCrossShellCell) : Set where
  constructor cross-shell-decay-certificate
  field
    commonConstant : ℚ
    decayMass : ℚ
    envelopeMassBound :
      sumLocalEnvelopes cells ≤ commonConstant * decayMass

open CrossShellDecayCertificate public

finiteAlmostOrthogonalityBound :
  (cells : List SignedCrossShellCell) →
  (certificate : CrossShellDecayCertificate cells) →
  ∣ sumSignedPairings cells ∣
  ≤ commonConstant certificate * decayMass certificate
finiteAlmostOrthogonalityBound cells certificate =
  ℚₚ.≤-trans
    (crossShellSignedAggregation cells)
    (envelopeMassBound certificate)

record NearFarCrossShellSplit : Set where
  constructor near-far-cross-shell-split
  field
    nearCells farCells : List SignedCrossShellCell
    nearBound farBound : ℚ
    nearCertificate :
      ∣ sumSignedPairings nearCells ∣ ≤ nearBound
    farCertificate :
      ∣ sumSignedPairings farCells ∣ ≤ farBound

open NearFarCrossShellSplit public

nearFarSignedBound :
  (split : NearFarCrossShellSplit) →
  ∣ sumSignedPairings (nearCells split)
    + sumSignedPairings (farCells split) ∣
  ≤ nearBound split + farBound split
nearFarSignedBound split =
  ℚₚ.≤-trans
    (ℚₚ.∣p+q∣≤∣p∣+∣q∣
      (sumSignedPairings (nearCells split))
      (sumSignedPairings (farCells split)))
    (ℚₚ.+-mono-≤
      (nearCertificate split)
      (farCertificate split))

crossShellAlmostOrthogonalityScalarCoreClosed : Bool
crossShellAlmostOrthogonalityScalarCoreClosed = true

cutoffUniformOperatorCotlarSteinClosed : Bool
cutoffUniformOperatorCotlarSteinClosed = false

crossShellAlmostOrthogonalityScalarCoreClosedIsTrue :
  crossShellAlmostOrthogonalityScalarCoreClosed ≡ true
crossShellAlmostOrthogonalityScalarCoreClosedIsTrue = refl

cutoffUniformOperatorCotlarSteinClosedIsFalse :
  cutoffUniformOperatorCotlarSteinClosed ≡ false
cutoffUniformOperatorCotlarSteinClosedIsFalse = refl
