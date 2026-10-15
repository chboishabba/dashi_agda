module DASHI.Biology.IITCubeTwoFaceQ9SelfIndexingWeldExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

import Base369 as Base
import DASHI.Biology.JFinePhaseQuotientFieldExact as Fine
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase

------------------------------------------------------------------------
-- Exact target carrier for the numerical 3x3x3 ternary-cube image weld.
--
-- Existing repo owner:
--   PhaseQuotient9 = TriTruth × TriTruth.
--
-- One ternary 3x3 face is already represented as
--   PhaseFineField = PhaseQuotient9 → TriTruth.
--
-- Therefore two such faces are pointwise equivalent to a nine-site field of
-- nine-state values:
--
--   (Q9 → F3) × (Q9 → F3)  <->  (Q9 → Q9).
--
-- This is the structured 9^9 target suggested by the local rank experiment.
-- The actual cube-image -> two-face restriction is deliberately a separate
-- recognition obligation; numerical rank 18 does not become an Agda theorem
-- merely by being reported here.
------------------------------------------------------------------------

TwoFineFaces : Set
TwoFineFaces = Fine.PhaseFineField × Fine.PhaseFineField

Q9Field9 : Set
Q9Field9 = Phase.PhaseQuotient9 → Phase.PhaseQuotient9

facesToQ9Field : TwoFineFaces → Q9Field9
facesToQ9Field (left , right) q = left q , right q

q9FieldToFaces : Q9Field9 → TwoFineFaces
q9FieldToFaces field =
  ( (λ q → proj₁ (field q))
  , (λ q → proj₂ (field q))
  )

facesAfterQ9FieldPointwiseLeft :
  (faces : TwoFineFaces) →
  (q : Phase.PhaseQuotient9) →
  proj₁ (q9FieldToFaces (facesToQ9Field faces)) q ≡ proj₁ faces q
facesAfterQ9FieldPointwiseLeft (left , right) q = refl

facesAfterQ9FieldPointwiseRight :
  (faces : TwoFineFaces) →
  (q : Phase.PhaseQuotient9) →
  proj₂ (q9FieldToFaces (facesToQ9Field faces)) q ≡ proj₂ faces q
facesAfterQ9FieldPointwiseRight (left , right) q = refl

q9FieldAfterFacesPointwise :
  (field : Q9Field9) →
  (q : Phase.PhaseQuotient9) →
  facesToQ9Field (q9FieldToFaces field) q ≡ field q
q9FieldAfterFacesPointwise field q with field q
... | (a , b) = refl

record CubeTwoFaceRecognition (CubeImage : Set) : Set₁ where
  field
    restrictToTwoFaces : CubeImage → TwoFineFaces
    reconstructFromTwoFaces : TwoFineFaces → CubeImage
    reconstructAfterRestrict :
      (x : CubeImage) → reconstructFromTwoFaces (restrictToTwoFaces x) ≡ x
    restrictAfterReconstruct :
      (faces : TwoFineFaces) →
      restrictToTwoFaces (reconstructFromTwoFaces faces) ≡ faces

record CubeQ9WeldBoundary : Set where
  field
    twoFacesExactlyWeldToQ9Field : Bool
    numericalRank18ProvesCubeRecognitionInAgda : Bool
    equalCardinalityAloneCreatesSameObject : Bool
    selfIndexedTetrationIsAutomaticallyCubeDynamics : Bool

canonicalCubeQ9WeldBoundary : CubeQ9WeldBoundary
canonicalCubeQ9WeldBoundary = record
  { twoFacesExactlyWeldToQ9Field = true
  ; numericalRank18ProvesCubeRecognitionInAgda = false
  ; equalCardinalityAloneCreatesSameObject = false
  ; selfIndexedTetrationIsAutomaticallyCubeDynamics = false
  }
