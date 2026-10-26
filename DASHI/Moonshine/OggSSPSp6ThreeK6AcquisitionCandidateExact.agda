module DASHI.Moonshine.OggSSPSp6ThreeK6AcquisitionCandidateExact where

------------------------------------------------------------------------
-- SOURCE-BOUNDED Sp6(3) CANDIDATE FOR THE K6 FIELD-SELECTOR ACQUISITION
--
-- External source facts used only to schedule acquisition:
--
-- * ATLAS of Group Representations: Sp6(3) has a standard 6-dimensional
--   matrix representation over GF(3) and a permutation representation on
--   728 points.
-- * standard symplectic Singer-cycle literature gives irreducible cyclic
--   elements in Sp(2n,q) of order q^n+1; for n=3,q=3 this order is 28.
--
-- These facts are structurally close to the existing K6 = F3^6 carrier but do
-- NOT identify the ATLAS module with DASHI.X6, do not select the branch's
-- chosen GF(729) multiplication, and do not manufacture a field-selector
-- operator.  The exact matrix, same-carrier chart, minimal polynomial and
-- swap-breaking witness remain explicit acquisition gates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

k6PuncturedCardinality : Nat
k6PuncturedCardinality = 728

threeToSixCardinalityCheck : 729 ≡ k6PuncturedCardinality + 1
threeToSixCardinalityCheck = refl

sp6ThreeSingerOrder : Nat
sp6ThreeSingerOrder = 28

sp6ThreeSingerOrderCheck : 3 * 3 * 3 + 1 ≡ sp6ThreeSingerOrder
sp6ThreeSingerOrderCheck = refl

atlasSp6ThreeURL : String
atlasSp6ThreeURL = "https://brauer.maths.qmul.ac.uk/Atlas/v3/clas/S63/"

barracloughWilsonMonster3BDOI : String
barracloughWilsonMonster3BDOI = "10.1112/S1461157000001352"

record Sp6ThreeK6CandidateBoundary : Set where
  constructor sp6-three-k6-candidate-boundary
  field
    sourceSixDimensionalGF3RepresentationLocated : Bool
    source728PointActionLocated : Bool
    sourceIrreducibleSingerFamilyLocated : Bool
    sameObjectAtlasModuleToX6Paid : Bool
    exactSelectedSingerMatrixAcquired : Bool
    minimalPolynomialDegreeSixChecked : Bool
    swap01BreakingWitnessPaid : Bool
    chosenGF729ActionIntertwinerPaid : Bool
    fieldSelectorPromotionPaid : Bool

open Sp6ThreeK6CandidateBoundary public

canonicalSp6ThreeK6CandidateBoundary : Sp6ThreeK6CandidateBoundary
canonicalSp6ThreeK6CandidateBoundary =
  sp6-three-k6-candidate-boundary
    true true true
    false false false false false false

-- The 728-point match is deliberately only an acquisition hint.
data PuncturedCardinalityImpliesSameObject : Set where

data SixDimensionalGF3ImpliesChosenFieldProduct : Set where

puncturedCardinalityDoesNotIdentifyCarrier :
  PuncturedCardinalityImpliesSameObject -> ⊥
puncturedCardinalityDoesNotIdentifyCarrier ()

sixDimensionalRepresentationDoesNotSelectField :
  SixDimensionalGF3ImpliesChosenFieldProduct -> ⊥
sixDimensionalRepresentationDoesNotSelectField ()
