module DASHI.Mathematics.Topology.AlexanderHornedC3CompactCommutatorRepresentationExact where

------------------------------------------------------------------------
-- POSITIVE CROSS-PR CONSUMER: EVERY CHOSEN SU(3) ROOT CAN BE THE
-- IMAGE OF A HATCHER HORN MERIDIAN IN AN ABSTRACT GROUP ACTION.
--
-- ORIGINAL CLASSICAL ROOTS / DATED ATTRIBUTION
-- Hatcher, Algebraic Topology, Example 2B.2, commutator free-group
-- tower, injective stage maps and colimit exterior group.
-- Morikuni Goto, "A Theorem on compact semi-simple groups,"
-- J Math Soc Japan 1(3), 270-272 (1949).
-- DOI 10.2969/jmsj/00130270: EVERY element of connected compact
-- semisimple SU(3) is a commutator.
-- Alexander (1924), original horned sphere.
--
-- ORIGINAL REPOSITORY OWNERS
-- DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact:
-- the actual binary word expansion and three-sector C3 rotation.
-- PR #1247 NeutrinoExistingCPSectorLeptonBridgeExact defines the
-- complex CP-nonzero leptonic U and chosen TS1 target (separate
-- branch, NOT imported without merge).
--
-- NEW THEOREM:
-- Given a specified group with a single-commutator section, an
-- order-three commutator-preserving automorphism and chosen root,
-- construct *all* binary horn address images, prove each horn
-- refinement and all-word compatibility, and show rotation
-- equivariance, without adding an SU(3) axiom to the free-word
-- source or inventing a finite A5 quotient.
--
-- Applying the STANDARD direct-limit universal property to these
-- finite-stage maps yields a genuine abstract representation
-- G_A * G_A * G_A -> SU(3), equivariant under the threefold
-- conjugation of its rotation generator T.
-- NOTE: direct-limit object, Gotô's analytic theorem and the
-- actual SU(3) matrix operations are not instantiated/kernellized
-- in this file. Agda source-written until exact-head typechecked.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; sym; trans)
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Mathematics.Topology.AlexanderHornedC3FiniteStageExact as Horn

record CommutatorSectionGroup : Set₁ where
  field
    Carrier : Set
    identity : Carrier
    multiply : Carrier → Carrier → Carrier
    inverse : Carrier → Carrier

  commutator : Carrier → Carrier → Carrier
  commutator a b =
    multiply (multiply (multiply a b) (inverse a)) (inverse b)

  field
    root : Carrier
    chooseLeft chooseRight : Carrier → Carrier
    chosenCommutator :
      (g : Carrier) →
      commutator (chooseLeft g) (chooseRight g) ≡ g

    -- The following laws are ordinary group and C3-action data.
    -- For SU(3), 'twist' is conjugation by the selected T.
    twist : Carrier → Carrier
    twistUnit : twist identity ≡ identity
    twistProduct : (a b : Carrier) →
      twist (multiply a b) ≡ multiply (twist a) (twist b)
    twistInverse : (a : Carrier) →
      twist (inverse a) ≡ inverse (twist a)
    twistCubed : (a : Carrier) →
      twist (twist (twist a)) ≡ a

    -- Exposed separately so this module does not need to reinvent
    -- the selected group-action/conjugation proof infrastructure.
    twistCommutator : (a b : Carrier) →
      twist (commutator a b) ≡
      commutator (twist a) (twist b)

open CommutatorSectionGroup public

rootValue : (G : CommutatorSectionGroup) →
  List Horn.Bit → Carrier G
rootValue G [] = root G
rootValue G (Horn.left ∷ xs) = chooseLeft G (rootValue G xs)
rootValue G (Horn.right ∷ xs) = chooseRight G (rootValue G xs)

rootValueRefinesAsCommutator :
  (G : CommutatorSectionGroup) (xs : List Horn.Bit) →
  rootValue G xs ≡
    commutator G
      (rootValue G (Horn.left ∷ xs))
      (rootValue G (Horn.right ∷ xs))
rootValueRefinesAsCommutator G xs =
  sym (chosenCommutator G (rootValue G xs))

liftC3 : (G : CommutatorSectionGroup) →
  C3.C3 → Carrier G → Carrier G
liftC3 G C3.c0 x = x
liftC3 G C3.c1 x = twist G x
liftC3 G C3.c2 x = twist G (twist G x)

liftC3Commutator :
  (G : CommutatorSectionGroup) (c : C3.C3)
  (a b : Carrier G) →
  liftC3 G c (commutator G a b)
    ≡ commutator G (liftC3 G c a) (liftC3 G c b)
liftC3Commutator G C3.c0 a b = refl
liftC3Commutator G C3.c1 a b = twistCommutator G a b
liftC3Commutator G C3.c2 a b =
  trans
    (cong (twist G) (twistCommutator G a b))
    (twistCommutator G (twist G a) (twist G b))

liftC3UnderRotation :
  (G : CommutatorSectionGroup) (c : C3.C3)
  (x : Carrier G) →
  liftC3 G (Horn.rotateSector c) x ≡ twist G (liftC3 G c x)
liftC3UnderRotation G C3.c0 x = refl
liftC3UnderRotation G C3.c1 x = refl
liftC3UnderRotation G C3.c2 x = sym (twistCubed G x)

addressValue : (G : CommutatorSectionGroup) →
  Horn.HornAddress → Carrier G
addressValue G (Horn.address c xs) =
  liftC3 G c (rootValue G xs)

addressRefinesAsCommutator :
  (G : CommutatorSectionGroup) (addr : Horn.HornAddress) →
  addressValue G addr ≡
    commutator G
      (addressValue G (Horn.leftChild addr))
      (addressValue G (Horn.rightChild addr))
addressRefinesAsCommutator G (Horn.address c xs) =
  trans
    (cong (liftC3 G c) (rootValueRefinesAsCommutator G xs))
    (liftC3Commutator G c
      (rootValue G (Horn.left ∷ xs))
      (rootValue G (Horn.right ∷ xs)))

addressRotationEquivariant :
  (G : CommutatorSectionGroup) (addr : Horn.HornAddress) →
  addressValue G (Horn.rotateAddress addr)
    ≡ twist G (addressValue G addr)
addressRotationEquivariant G (Horn.address c xs) =
  liftC3UnderRotation G c (rootValue G xs)

valueWord : (G : CommutatorSectionGroup) →
  Horn.Word → Carrier G
valueWord G Horn.unit = identity G
valueWord G (Horn.generator addr) = addressValue G addr
valueWord G (Horn.inverseWord w) = inverse G (valueWord G w)
valueWord G (Horn.combine a b) =
  multiply G (valueWord G a) (valueWord G b)

valueCommutator :
  (G : CommutatorSectionGroup) (a b : Horn.Word) →
  valueWord G (Horn.commutator a b)
    ≡ commutator G (valueWord G a) (valueWord G b)
valueCommutator G a b = refl

everyHornExpansionPreservesValue :
  (G : CommutatorSectionGroup) (w : Horn.Word) →
  valueWord G (Horn.expandWord w) ≡ valueWord G w
everyHornExpansionPreservesValue G Horn.unit = refl
everyHornExpansionPreservesValue G (Horn.generator addr) =
  trans
    (valueCommutator G
      (Horn.generator (Horn.leftChild addr))
      (Horn.generator (Horn.rightChild addr)))
    (sym (addressRefinesAsCommutator G addr))
everyHornExpansionPreservesValue G (Horn.inverseWord w) =
  cong (inverse G) (everyHornExpansionPreservesValue G w)
everyHornExpansionPreservesValue G (Horn.combine a b) =
  cong₂ (multiply G)
    (everyHornExpansionPreservesValue G a)
    (everyHornExpansionPreservesValue G b)

twiceTwistUnit :
  (G : CommutatorSectionGroup) →
  twist G (twist G (identity G)) ≡ identity G
twiceTwistUnit G =
  trans (cong (twist G) (twistUnit G)) (twistUnit G)

liftC3Product :
  (G : CommutatorSectionGroup) (c : C3.C3) →
  (a b : Carrier G) →
  liftC3 G c (multiply G a b)
    ≡ multiply G (liftC3 G c a) (liftC3 G c b)
liftC3Product G C3.c0 a b = refl
liftC3Product G C3.c1 a b = twistProduct G a b
liftC3Product G C3.c2 a b =
  trans
    (cong (twist G) (twistProduct G a b))
    (twistProduct G (twist G a) (twist G b))

liftC3Inverse :
  (G : CommutatorSectionGroup) (c : C3.C3) →
  (a : Carrier G) →
  liftC3 G c (inverse G a) ≡ inverse G (liftC3 G c a)
liftC3Inverse G C3.c0 a = refl
liftC3Inverse G C3.c1 a = twistInverse G a
liftC3Inverse G C3.c2 a =
  trans (cong (twist G) (twistInverse G a))
    (twistInverse G (twist G a))

wordRotationEquivariant :
  (G : CommutatorSectionGroup) (w : Horn.Word) →
  valueWord G (Horn.rotateWord w) ≡ twist G (valueWord G w)
wordRotationEquivariant G Horn.unit = sym (twistUnit G)
wordRotationEquivariant G (Horn.generator addr) =
  addressRotationEquivariant G addr
wordRotationEquivariant G (Horn.inverseWord w) =
  trans (cong (inverse G) (wordRotationEquivariant G w))
    (sym (twistInverse G (valueWord G w)))
wordRotationEquivariant G (Horn.combine a b) =
  trans
    (cong₂ (multiply G)
      (wordRotationEquivariant G a)
      (wordRotationEquivariant G b))
    (sym (twistProduct G (valueWord G a) (valueWord G b)))

------------------------------------------------------------------------
-- GOTO/CONSTRUCTION BOUNDARY
--
-- The source has no postulates; section+automorphism are explicit
-- parameters. Gotô's original theorem DISCHARGES a chosen section
-- for SU(3) in ordinary mathematics. A concrete SU(3) action must
-- additionally supply matrix group laws and 'twist' by conjugation
-- T^3=I. We do NOT claim that construction has been Agda checked.
--
-- A direct-limit / free-product universal property, when supplied,
-- transports these compatible finite-stage word homomorphisms.
-- The selected q:G→A5^3 quotient is NOT used; its fifth-power no-go
-- does not constrain these infinite-image representations.
------------------------------------------------------------------------
