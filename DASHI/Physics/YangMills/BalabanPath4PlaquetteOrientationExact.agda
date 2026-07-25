module DASHI.Physics.YangMills.BalabanPath4PlaquetteOrientationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanFiniteEnumerationDistinctExact using
  (DuplicateFree; []-duplicateFree; _∷-duplicateFree_)

------------------------------------------------------------------------
-- Literal positive orientation convention for four dimensions.
--
-- Exactly six unordered coordinate planes are enumerated.  Reverse
-- orientation is a derived operation, not an additional plaquette slot.
------------------------------------------------------------------------

data PositivePlaquettePlane4 : Set where
  plane01 plane02 plane03 plane12 plane13 plane23 : PositivePlaquettePlane4

positivePlaquettePlanes4 : List PositivePlaquettePlane4
positivePlaquettePlanes4 =
  plane01 ∷ plane02 ∷ plane03 ∷ plane12 ∷ plane13 ∷ plane23 ∷ []

positivePlaneFirst : PositivePlaquettePlane4 → Axis4
positivePlaneFirst plane01 = zeroᵢ
positivePlaneFirst plane02 = zeroᵢ
positivePlaneFirst plane03 = zeroᵢ
positivePlaneFirst plane12 = sucᵢ zeroᵢ
positivePlaneFirst plane13 = sucᵢ zeroᵢ
positivePlaneFirst plane23 = sucᵢ (sucᵢ zeroᵢ)

positivePlaneSecond : PositivePlaquettePlane4 → Axis4
positivePlaneSecond plane01 = sucᵢ zeroᵢ
positivePlaneSecond plane02 = sucᵢ (sucᵢ zeroᵢ)
positivePlaneSecond plane03 = sucᵢ (sucᵢ (sucᵢ zeroᵢ))
positivePlaneSecond plane12 = sucᵢ (sucᵢ zeroᵢ)
positivePlaneSecond plane13 = sucᵢ (sucᵢ (sucᵢ zeroᵢ))
positivePlaneSecond plane23 = sucᵢ (sucᵢ (sucᵢ zeroᵢ))

positivePlaquettePlanes4Complete : ∀ plane → plane ∈ positivePlaquettePlanes4
positivePlaquettePlanes4Complete plane01 = here
positivePlaquettePlanes4Complete plane02 = there here
positivePlaquettePlanes4Complete plane03 = there (there here)
positivePlaquettePlanes4Complete plane12 = there (there (there here))
positivePlaquettePlanes4Complete plane13 = there (there (there (there here)))
positivePlaquettePlanes4Complete plane23 =
  there (there (there (there (there here))))

------------------------------------------------------------------------
-- A direct duplicate-free proof is kept local rather than relying on a
-- cardinality claim.  The constructor distinctions discharge all exclusions.
------------------------------------------------------------------------

plane01NotInTail :
  Not (plane01 ∈ (plane02 ∷ plane03 ∷ plane12 ∷ plane13 ∷ plane23 ∷ []))
plane01NotInTail ()

plane02NotInTail :
  Not (plane02 ∈ (plane03 ∷ plane12 ∷ plane13 ∷ plane23 ∷ []))
plane02NotInTail ()

plane03NotInTail :
  Not (plane03 ∈ (plane12 ∷ plane13 ∷ plane23 ∷ []))
plane03NotInTail ()

plane12NotInTail : Not (plane12 ∈ (plane13 ∷ plane23 ∷ []))
plane12NotInTail ()

plane13NotInTail : Not (plane13 ∈ (plane23 ∷ []))
plane13NotInTail ()

plane23NotInTail : Not (plane23 ∈ [])
plane23NotInTail ()

positivePlaquettePlanes4DuplicateFree :
  DuplicateFree positivePlaquettePlanes4
positivePlaquettePlanes4DuplicateFree =
  plane01NotInTail ∷-duplicateFree
  (plane02NotInTail ∷-duplicateFree
  (plane03NotInTail ∷-duplicateFree
  (plane12NotInTail ∷-duplicateFree
  (plane13NotInTail ∷-duplicateFree
  (plane23NotInTail ∷-duplicateFree []-duplicateFree)))))

wilsonPlaquetteEnumerationMatchesPositivePairs :
  positivePlaquettePlanes4 ≡
    plane01 ∷ plane02 ∷ plane03 ∷ plane12 ∷ plane13 ∷ plane23 ∷ []
wilsonPlaquetteEnumerationMatchesPositivePairs = refl

------------------------------------------------------------------------
-- Reverse orientation changes the sign of the linearised curvature and hence
-- leaves its square unchanged.  Thus an ordered-pair Wilson convention would
-- have multiplicity two, whereas the configured convention uses the six
-- positive planes exactly once.
------------------------------------------------------------------------

square : ℚ → ℚ
square value = value * value

reversePlaquetteCurlSqExact : ∀ forward reverse →
  reverse ≡ (0ℚ - forward) → square reverse ≡ square forward
reversePlaquetteCurlSqExact forward .(0ℚ - forward) refl =
  ℚRing.solve-∀ forward

positivePlaquetteMultiplicity : ℚ
positivePlaquetteMultiplicity = 1ℚ

orderedPlaquetteMultiplicity : ℚ
orderedPlaquetteMultiplicity = 2ℚ

wilsonOrientationMultiplicityExact :
  orderedPlaquetteMultiplicity ≡
  positivePlaquetteMultiplicity + positivePlaquetteMultiplicity
wilsonOrientationMultiplicityExact = refl

path4PlaquetteOrientationLevel : ProofLevel
path4PlaquetteOrientationLevel = machineChecked
