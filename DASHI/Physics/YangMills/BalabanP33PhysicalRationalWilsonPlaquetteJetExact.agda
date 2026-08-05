module DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact where

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
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Construct the actual rational right-exponential link jets used by the Wilson
-- Hessian on the literal side-four periodic lattice.  For a positive link
--
--   U_b(t)=U_b exp(t X_b),
--
-- its two-jet at zero is
--
--   (U_b, U_b X_b, U_b X_b^2).
--
-- For an inverse plaquette occurrence,
--
--   U_b(t)^-1=exp(-t X_b) U_b^-1,
--
-- the jet is
--
--   (U_b^-1, -X_b U_b^-1, X_b^2 U_b^-1).
--
-- The module constructs the six oriented axis-pair plaquettes at every one of
-- the 4^4 sites, feeds their four literal factor jets to the rational
-- quaternion product rule, and proves that the Wilson second variation is
-- exactly the finite sum of the four diagonal and twelve ordered cross atoms.
--
-- At the identity background the same concrete jet reduces to the previously
-- proved plaquette curl square for the same physical perturbation h.  Thus the
-- nonzero-background Wilson defect is now a literal difference between two
-- computed finite expressions, rather than an abstract atom-family premise.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map; length)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Product; pair; PositiveBond; cartesian; physicalBlockSites; four)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Wilson
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge4
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatWilsonCurlIdentificationExact as Flat
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini

------------------------------------------------------------------------
-- Rational SU(2) unit quaternions.
------------------------------------------------------------------------

quaternionConjugate : Wilson.RationalQuaternion → Wilson.RationalQuaternion
quaternionConjugate (Wilson.quat a0 a1 a2 a3) =
  Wilson.quat a0 (- a1) (- a2) (- a3)

quaternionNormSq : Wilson.RationalQuaternion → ℚ
quaternionNormSq (Wilson.quat a0 a1 a2 a3) =
  a0 * a0 + a1 * a1 + a2 * a2 + a3 * a3

multiplyConjugateExact : ∀ value →
  value Wilson.*q quaternionConjugate value
  ≡ Wilson.quat (quaternionNormSq value) 0ℚ 0ℚ 0ℚ
multiplyConjugateExact (Wilson.quat a0 a1 a2 a3) =
  Wilson.quaternionExt
    (ℚRing.solve-∀ a0 a1 a2 a3)
    (ℚRing.solve-∀ a0 a1 a2 a3)
    (ℚRing.solve-∀ a0 a1 a2 a3)
    (ℚRing.solve-∀ a0 a1 a2 a3)

conjugateMultiplyExact : ∀ value →
  quaternionConjugate value Wilson.*q value
  ≡ Wilson.quat (quaternionNormSq value) 0ℚ 0ℚ 0ℚ
conjugateMultiplyExact (Wilson.quat a0 a1 a2 a3) =
  Wilson.quaternionExt
    (ℚRing.solve-∀ a0 a1 a2 a3)
    (ℚRing.solve-∀ a0 a1 a2 a3)
    (ℚRing.solve-∀ a0 a1 a2 a3)
    (ℚRing.solve-∀ a0 a1 a2 a3)

record RationalSU2Background4 : Set where
  field
    link : PositiveBond Path4.side4 → Wilson.RationalQuaternion
    unitNorm : ∀ bond → quaternionNormSq (link bond) ≡ 1ℚ

open RationalSU2Background4 public

inverseLink :
  RationalSU2Background4 → PositiveBond Path4.side4 →
  Wilson.RationalQuaternion
inverseLink background bond = quaternionConjugate (link background bond)

linkInverseRightExact : ∀ background bond →
  link background bond Wilson.*q inverseLink background bond ≡ Wilson.oneQ
linkInverseRightExact background bond =
  trans
    (multiplyConjugateExact (link background bond))
    (cong (λ selected → Wilson.quat selected 0ℚ 0ℚ 0ℚ)
      (unitNorm background bond))

linkInverseLeftExact : ∀ background bond →
  inverseLink background bond Wilson.*q link background bond ≡ Wilson.oneQ
linkInverseLeftExact background bond =
  trans
    (conjugateMultiplyExact (link background bond))
    (cong (λ selected → Wilson.quat selected 0ℚ 0ℚ 0ℚ)
      (unitNorm background bond))

identityBackground : RationalSU2Background4
identityBackground = record
  { link = λ _ → Wilson.oneQ
  ; unitNorm = λ _ → ℚRing.solve []
  }

------------------------------------------------------------------------
-- Physical right-exponential link two-jets.
------------------------------------------------------------------------

insertionAt :
  Physical.PhysicalSU2BondField4 →
  Hodge4.Axis4 → Hodge4.Site4 → Wilson.RationalVector3
insertionAt = Flat.insertionAt

positiveLinkJet :
  RationalSU2Background4 → Physical.PhysicalSU2BondField4 →
  Hodge4.Site4 → Hodge4.Axis4 → Wilson.QuaternionFactorJet
positiveLinkJet background field site axis =
  let
    backgroundValue = link background (pair site axis)
    insertion = Wilson.pureQuaternion (insertionAt field axis site)
  in
  Wilson.factorJet
    backgroundValue
    (backgroundValue Wilson.*q insertion)
    (backgroundValue Wilson.*q (insertion Wilson.*q insertion))

inverseLinkJet :
  RationalSU2Background4 → Physical.PhysicalSU2BondField4 →
  Hodge4.Site4 → Hodge4.Axis4 → Wilson.QuaternionFactorJet
inverseLinkJet background field site axis =
  let
    backgroundInverse = inverseLink background (pair site axis)
    insertion = Wilson.pureQuaternion (insertionAt field axis site)
  in
  Wilson.factorJet
    backgroundInverse
    (Wilson.negQ insertion Wilson.*q backgroundInverse)
    ((insertion Wilson.*q insertion) Wilson.*q backgroundInverse)

------------------------------------------------------------------------
-- Six literal plaquette orientations.
------------------------------------------------------------------------

data AxisPair6 : Set where
  pair01 pair02 pair03 pair12 pair13 pair23 : AxisPair6

axisPairs6 : List AxisPair6
axisPairs6 = pair01 ∷ pair02 ∷ pair03 ∷ pair12 ∷ pair13 ∷ pair23 ∷ []

pairLeft : AxisPair6 → Hodge4.Axis4
pairLeft pair01 = Hodge4.axis0
pairLeft pair02 = Hodge4.axis0
pairLeft pair03 = Hodge4.axis0
pairLeft pair12 = Hodge4.axis1
pairLeft pair13 = Hodge4.axis1
pairLeft pair23 = Hodge4.axis2

pairRight : AxisPair6 → Hodge4.Axis4
pairRight pair01 = Hodge4.axis1
pairRight pair02 = Hodge4.axis2
pairRight pair03 = Hodge4.axis3
pairRight pair12 = Hodge4.axis2
pairRight pair13 = Hodge4.axis3
pairRight pair23 = Hodge4.axis3

Plaquette4 : Set
Plaquette4 = Product Hodge4.Site4 AxisPair6

plaquettes4 : List Plaquette4
plaquettes4 = cartesian (Block.physicalBlockSites Path4.side4) axisPairs6

plaquetteFactorJets :
  RationalSU2Background4 → Physical.PhysicalSU2BondField4 →
  Plaquette4 → List Wilson.QuaternionFactorJet
plaquetteFactorJets background field (pair site axes) =
  let
    left = pairLeft axes
    right = pairRight axes
  in
  Wilson.fourFactorJets
    (positiveLinkJet background field site left)
    (positiveLinkJet background field
      (Hodge4.shiftForward left site) right)
    (inverseLinkJet background field
      (Hodge4.shiftForward right site) left)
    (inverseLinkJet background field site right)

plaquetteJetData :
  RationalSU2Background4 → Physical.PhysicalSU2BondField4 →
  Plaquette4 → Jets.PlaquetteSecondJet
plaquetteJetData background field plaquette
  with plaquetteFactorJets background field plaquette
... | first ∷ second ∷ third ∷ fourth ∷ [] =
  Jets.plaquetteJet first second third fourth

plaquetteWilsonSecondVariation :
  RationalSU2Background4 → Physical.PhysicalSU2BondField4 →
  Plaquette4 → ℚ
plaquetteWilsonSecondVariation background field plaquette =
  Jets.plaquetteWilsonSecondVariation
    (plaquetteJetData background field plaquette)

plaquetteWilsonAtomSum :
  RationalSU2Background4 → Physical.PhysicalSU2BondField4 →
  Plaquette4 → ℚ
plaquetteWilsonAtomSum background field plaquette =
  Wilson.wilsonSecondVariationAtomSum
    (plaquetteFactorJets background field plaquette)

plaquetteWilsonIsSixteenAtoms : ∀ background field plaquette →
  plaquetteWilsonSecondVariation background field plaquette
  ≡ plaquetteWilsonAtomSum background field plaquette
plaquetteWilsonIsSixteenAtoms background field plaquette =
  Jets.plaquetteWilsonIsSixteenAtomSum
    (plaquetteJetData background field plaquette)

physicalWilsonSecondVariation :
  RationalSU2Background4 → Physical.PhysicalSU2BondField4 → ℚ
physicalWilsonSecondVariation background field =
  Sums.sumRational plaquettes4
    (plaquetteWilsonSecondVariation background field)

physicalWilsonAtomSum :
  RationalSU2Background4 → Physical.PhysicalSU2BondField4 → ℚ
physicalWilsonAtomSum background field =
  Sums.sumRational plaquettes4
    (plaquetteWilsonAtomSum background field)

physicalWilsonSecondVariationIsSixteenAtomSum : ∀ background field →
  physicalWilsonSecondVariation background field
  ≡ physicalWilsonAtomSum background field
physicalWilsonSecondVariationIsSixteenAtomSum background field =
  Sums.sumRationalCong
    plaquettes4
    (plaquetteWilsonSecondVariation background field)
    (plaquetteWilsonAtomSum background field)
    (plaquetteWilsonIsSixteenAtoms background field)

------------------------------------------------------------------------
-- Identity-background specialization to the concrete flat curl energy.
------------------------------------------------------------------------

identityPositiveJetIsFlat : ∀ field site axis →
  positiveLinkJet identityBackground field site axis
  ≡ Wilson.flatExponentialJet (insertionAt field axis site)
identityPositiveJetIsFlat field site axis = refl

identityInverseJetIsFlatNegative : ∀ field site axis →
  inverseLinkJet identityBackground field site axis
  ≡ Wilson.flatExponentialJet (Wilson.negV (insertionAt field axis site))
identityInverseJetIsFlatNegative field site axis = refl

identityPlaquetteSecondVariationIsCurlSquare : ∀ field site axes →
  plaquetteWilsonSecondVariation
    identityBackground field (pair site axes)
  ≡ Wilson.vectorNormSq
      (Wilson.plaquetteCurlVector
        (insertionAt field (pairLeft axes) site)
        (insertionAt field (pairRight axes)
          (Hodge4.shiftForward (pairLeft axes) site))
        (insertionAt field (pairLeft axes)
          (Hodge4.shiftForward (pairRight axes) site))
        (insertionAt field (pairRight axes) site))
identityPlaquetteSecondVariationIsCurlSquare field site axes =
  Wilson.flatPlaquetteWilsonIsCurlSquare
    (insertionAt field (pairLeft axes) site)
    (insertionAt field (pairRight axes)
      (Hodge4.shiftForward (pairLeft axes) site))
    (insertionAt field (pairLeft axes)
      (Hodge4.shiftForward (pairRight axes) site))
    (insertionAt field (pairRight axes) site)

physicalWilsonDefect :
  RationalSU2Background4 → Physical.PhysicalSU2BondField4 → ℚ
physicalWilsonDefect background field =
  physicalWilsonSecondVariation background field
  - physicalWilsonSecondVariation identityBackground field

physicalWilsonDefectIsAtomDifference : ∀ background field →
  physicalWilsonDefect background field
  ≡ physicalWilsonAtomSum background field
    - physicalWilsonAtomSum identityBackground field
physicalWilsonDefectIsAtomDifference background field =
  cong₂ _-_
    (physicalWilsonSecondVariationIsSixteenAtomSum background field)
    (physicalWilsonSecondVariationIsSixteenAtomSum identityBackground field)

rationalSU2InverseLevel : ProofLevel
rationalSU2InverseLevel = machineChecked

physicalRightExponentialLinkJetLevel : ProofLevel
physicalRightExponentialLinkJetLevel = machineChecked

physicalWilsonPlaquetteEnumerationLevel : ProofLevel
physicalWilsonPlaquetteEnumerationLevel = machineChecked

physicalWilsonSixteenAtomIdentificationLevel : ProofLevel
physicalWilsonSixteenAtomIdentificationLevel = machineChecked

physicalWilsonDefectAtomDifferenceLevel : ProofLevel
physicalWilsonDefectAtomDifferenceLevel = machineChecked
