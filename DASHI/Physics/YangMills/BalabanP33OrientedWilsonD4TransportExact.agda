module DASHI.Physics.YangMills.BalabanP33OrientedWilsonD4TransportExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- John H. Conway and Derek A. Smith,
-- "On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry",
-- A K Peters, 2003.
-- DOI: 10.1201/9781439864180.
--
-- DASHI CONTRIBUTION
--
-- Package the D4 transport of a plaquette variation frame without conflating
-- additive jet negation, group inversion, quaternion conjugation, reversal of
-- multiplication order, geometric reflection or common-frame transport.
-- Slot-indexed data are pulled back by the inverse permutation; orientation
-- reversal acts by quaternion conjugation.  Composition is proved pointwise,
-- and the Wilson scalar is exactly invariant under every named D4 symmetry.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanWilsonD4SubsetCharacterExact as D4
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33QuaternionFourFactorTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanP33PlaquetteOrientationReversalExact as Reversal

xor : Bool → Bool → Bool
xor false value = value
xor true false = true
xor true true = false

xorAssociative : ∀ first second third →
  xor first (xor second third)
  ≡ xor (xor first second) third
xorAssociative false false false = refl
xorAssociative false false true = refl
xorAssociative false true false = refl
xorAssociative false true true = refl
xorAssociative true false false = refl
xorAssociative true false true = refl
xorAssociative true true false = refl
xorAssociative true true true = refl

record OrientedPlaquetteSymmetry : Set where
  constructor orientedSymmetry
  field
    slotPermutation : D4.SlotPermutation4
    reversesOrientation : Bool

open OrientedPlaquetteSymmetry public

composeOrientedSymmetry :
  OrientedPlaquetteSymmetry →
  OrientedPlaquetteSymmetry →
  OrientedPlaquetteSymmetry
composeOrientedSymmetry left right = orientedSymmetry
  (D4.composePermutation4
    (slotPermutation left) (slotPermutation right))
  (xor (reversesOrientation left) (reversesOrientation right))

namedOrientationReverses : D4.NamedD4 → Bool
namedOrientationReverses D4.identity = false
namedOrientationReverses D4.rotation90 = false
namedOrientationReverses D4.rotation180 = false
namedOrientationReverses D4.rotation270 = false
namedOrientationReverses D4.reflectionAxis = true
namedOrientationReverses D4.reflectionEdge = true
namedOrientationReverses D4.reflectionOppositeAxis = true
namedOrientationReverses D4.reflectionOppositeEdge = true

namedOrientedSymmetry : D4.NamedD4 → OrientedPlaquetteSymmetry
namedOrientedSymmetry symmetry = orientedSymmetry
  (D4.namedPermutation symmetry)
  (namedOrientationReverses symmetry)

data JetSign : Set where
  positiveJet negativeJet : JetSign

data GroupInversionFlag : Set where
  directGroupElement inverseGroupElement : GroupInversionFlag

record PlaquetteVariationFrame : Set where
  constructor variationFrame
  field
    activeBond : Cube.BondSlot4 → Bool
    geometricOrientation : Bool
    transportPrefix : Cube.BondSlot4 → Q.RationalQuaternion
    jetSign : Cube.BondSlot4 → JetSign
    groupInversion : Cube.BondSlot4 → GroupInversionFlag
    gaugeRepair : Cube.BondSlot4 → ℚ
    constraintRepair : Cube.BondSlot4 → ℚ
    orderedAtom : Q.RationalQuaternion

open PlaquetteVariationFrame public

transportAtom : Bool → Q.RationalQuaternion → Q.RationalQuaternion
transportAtom false atom = atom
transportAtom true atom = Reversal.reverseQuaternion atom

transportAtomComposeExact : ∀ first second atom →
  transportAtom first (transportAtom second atom)
  ≡ transportAtom (xor first second) atom
transportAtomComposeExact false false atom = refl
transportAtomComposeExact false true atom = refl
transportAtomComposeExact true false atom = refl
transportAtomComposeExact true true atom =
  Reversal.reverseQuaternionInvolutive atom

transportFrame :
  OrientedPlaquetteSymmetry →
  PlaquetteVariationFrame →
  PlaquetteVariationFrame
transportFrame symmetry frame = variationFrame
  (λ slot → activeBond frame
    (D4.backward (slotPermutation symmetry) slot))
  (xor (reversesOrientation symmetry)
    (geometricOrientation frame))
  (λ slot → transportPrefix frame
    (D4.backward (slotPermutation symmetry) slot))
  (λ slot → jetSign frame
    (D4.backward (slotPermutation symmetry) slot))
  (λ slot → groupInversion frame
    (D4.backward (slotPermutation symmetry) slot))
  (λ slot → gaugeRepair frame
    (D4.backward (slotPermutation symmetry) slot))
  (λ slot → constraintRepair frame
    (D4.backward (slotPermutation symmetry) slot))
  (transportAtom (reversesOrientation symmetry)
    (orderedAtom frame))

record FramePointwiseEquality
    (left right : PlaquetteVariationFrame) : Set where
  field
    activeBondEqual : ∀ slot →
      activeBond left slot ≡ activeBond right slot
    orientationEqual :
      geometricOrientation left ≡ geometricOrientation right
    transportPrefixEqual : ∀ slot →
      transportPrefix left slot ≡ transportPrefix right slot
    jetSignEqual : ∀ slot → jetSign left slot ≡ jetSign right slot
    groupInversionEqual : ∀ slot →
      groupInversion left slot ≡ groupInversion right slot
    gaugeRepairEqual : ∀ slot →
      gaugeRepair left slot ≡ gaugeRepair right slot
    constraintRepairEqual : ∀ slot →
      constraintRepair left slot ≡ constraintRepair right slot
    orderedAtomEqual : orderedAtom left ≡ orderedAtom right

open FramePointwiseEquality public

transportFrameCompositionExact :
  ∀ first second frame →
  FramePointwiseEquality
    (transportFrame first (transportFrame second frame))
    (transportFrame (composeOrientedSymmetry first second) frame)
transportFrameCompositionExact first second frame = record
  { activeBondEqual = λ slot → refl
  ; orientationEqual =
      xorAssociative
        (reversesOrientation first)
        (reversesOrientation second)
        (geometricOrientation frame)
  ; transportPrefixEqual = λ slot → refl
  ; jetSignEqual = λ slot → refl
  ; groupInversionEqual = λ slot → refl
  ; gaugeRepairEqual = λ slot → refl
  ; constraintRepairEqual = λ slot → refl
  ; orderedAtomEqual =
      transportAtomComposeExact
        (reversesOrientation first)
        (reversesOrientation second)
        (orderedAtom frame)
  }

namedFrameTransport :
  D4.NamedD4 → PlaquetteVariationFrame → PlaquetteVariationFrame
namedFrameTransport symmetry =
  transportFrame (namedOrientedSymmetry symmetry)

namedFrameWilsonScalarInvariant :
  ∀ symmetry frame →
  Telescope.wilsonScalar
    (orderedAtom (namedFrameTransport symmetry frame))
  ≡ Telescope.wilsonScalar (orderedAtom frame)
namedFrameWilsonScalarInvariant D4.identity frame = refl
namedFrameWilsonScalarInvariant D4.rotation90 frame = refl
namedFrameWilsonScalarInvariant D4.rotation180 frame = refl
namedFrameWilsonScalarInvariant D4.rotation270 frame = refl
namedFrameWilsonScalarInvariant D4.reflectionAxis frame =
  Reversal.reverseWilsonScalarInvariant (orderedAtom frame)
namedFrameWilsonScalarInvariant D4.reflectionEdge frame =
  Reversal.reverseWilsonScalarInvariant (orderedAtom frame)
namedFrameWilsonScalarInvariant D4.reflectionOppositeAxis frame =
  Reversal.reverseWilsonScalarInvariant (orderedAtom frame)
namedFrameWilsonScalarInvariant D4.reflectionOppositeEdge frame =
  Reversal.reverseWilsonScalarInvariant (orderedAtom frame)

reflectedOrderedAtomExact : ∀ a0 a1 a2 a3 →
  transportAtom true (Telescope.orderedProduct4 a0 a1 a2 a3)
  ≡ Reversal.reverseOrderedProduct4 a0 a1 a2 a3
reflectedOrderedAtomExact = Reversal.reverseSubsetAtomExact

data FrameOperation : Set where
  additiveJetNegation groupElementInversion quaternionConjugation
    multiplicationOrderReversal geometricPlaquetteReflection
    commonFrameTransport : FrameOperation

jetNegationIsNotGroupInversion :
  additiveJetNegation ≡ groupElementInversion → ⊥
jetNegationIsNotGroupInversion ()

groupInversionIsNotQuaternionConjugation :
  groupElementInversion ≡ quaternionConjugation → ⊥
groupInversionIsNotQuaternionConjugation ()

conjugationIsNotGeometricReflection :
  quaternionConjugation ≡ geometricPlaquetteReflection → ⊥
conjugationIsNotGeometricReflection ()

orderReversalIsNotCommonFrameTransport :
  multiplicationOrderReversal ≡ commonFrameTransport → ⊥
orderReversalIsNotCommonFrameTransport ()

orientedD4FrameActionLevel : ProofLevel
orientedD4FrameActionLevel = machineChecked

orientedWilsonScalarTransportLevel : ProofLevel
orientedWilsonScalarTransportLevel = machineChecked

frameOperationNonconfusionLevel : ProofLevel
frameOperationNonconfusionLevel = machineChecked
