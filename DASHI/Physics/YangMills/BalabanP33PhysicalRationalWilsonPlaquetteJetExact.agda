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
-- its two-jet at zero is `(U_b,U_b X_b,U_b X_b^2)`.  For an inverse occurrence
--
--   U_b(t)^-1=exp(-t X_b)U_b^-1,
--
-- the jet is `(U_b^-1,-X_b U_b^-1,X_b^2 U_b^-1)`.
--
-- The six oriented axis-pair plaquettes at every one of the 4^4 sites are fed
-- directly to the rational four-factor product rule.  The resulting physical
-- Wilson Hessian is exactly the finite sum of four diagonal and twelve ordered
-- cross atoms per plaquette.  A separate finite Fubini calculation proves that
-- the identity-background value of this same construction is the concrete
-- physical periodic curl energy.  The nonzero-background Wilson defect is
-- therefore a literal difference of computed sixteen-atom sums.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Product; pair; PositiveBond; cartesian; Axis4)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Wilson
import DASHI.Physics.YangMills.BalabanP33LiteralGaugeConstraintSecondVariationExact as Jets
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge4
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatWilsonCurlIdentificationExact as Flat
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanPhysicalAxisPartitionExact as Partition

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
  Axis4 → Hodge4.Site4 → Wilson.RationalVector3
insertionAt = Flat.insertionAt

positiveLinkJet :
  RationalSU2Background4 → Physical.PhysicalSU2BondField4 →
  Hodge4.Site4 → Axis4 → Wilson.QuaternionFactorJet
positiveLinkJet background bondField site axis =
  let
    backgroundValue = link background (pair site axis)
    insertion = Wilson.pureQuaternion (insertionAt bondField axis site)
  in
  Wilson.factorJet
    backgroundValue
    (backgroundValue Wilson.*q insertion)
    (backgroundValue Wilson.*q (insertion Wilson.*q insertion))

inverseLinkJet :
  RationalSU2Background4 → Physical.PhysicalSU2BondField4 →
  Hodge4.Site4 → Axis4 → Wilson.QuaternionFactorJet
inverseLinkJet background bondField site axis =
  let
    backgroundInverse = inverseLink background (pair site axis)
    insertion = Wilson.pureQuaternion (insertionAt bondField axis site)
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

pairLeft : AxisPair6 → Axis4
pairLeft pair01 = Hodge4.axis0
pairLeft pair02 = Hodge4.axis0
pairLeft pair03 = Hodge4.axis0
pairLeft pair12 = Hodge4.axis1
pairLeft pair13 = Hodge4.axis1
pairLeft pair23 = Hodge4.axis2

pairRight : AxisPair6 → Axis4
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

plaquetteJetData :
  RationalSU2Background4 → Physical.PhysicalSU2BondField4 →
  Plaquette4 → Jets.PlaquetteSecondJet
plaquetteJetData background bondField (pair site axes) =
  let
    left = pairLeft axes
    right = pairRight axes
  in
  Jets.plaquetteJet
    (positiveLinkJet background bondField site left)
    (positiveLinkJet background bondField
      (Hodge4.shiftForward left site) right)
    (inverseLinkJet background bondField
      (Hodge4.shiftForward right site) left)
    (inverseLinkJet background bondField site right)

plaquetteFactorJets :
  RationalSU2Background4 → Physical.PhysicalSU2BondField4 →
  Plaquette4 → List Wilson.QuaternionFactorJet
plaquetteFactorJets background bondField plaquette =
  let dataSet = plaquetteJetData background bondField plaquette
  in Wilson.fourFactorJets
      (Jets.link0 dataSet) (Jets.link1 dataSet)
      (Jets.link2 dataSet) (Jets.link3 dataSet)

plaquetteWilsonSecondVariation :
  RationalSU2Background4 → Physical.PhysicalSU2BondField4 →
  Plaquette4 → ℚ
plaquetteWilsonSecondVariation background bondField plaquette =
  Jets.plaquetteWilsonSecondVariation
    (plaquetteJetData background bondField plaquette)

plaquetteWilsonAtomSum :
  RationalSU2Background4 → Physical.PhysicalSU2BondField4 →
  Plaquette4 → ℚ
plaquetteWilsonAtomSum background bondField plaquette =
  Wilson.wilsonSecondVariationAtomSum
    (plaquetteFactorJets background bondField plaquette)

plaquetteWilsonIsSixteenAtoms : ∀ background bondField plaquette →
  plaquetteWilsonSecondVariation background bondField plaquette
  ≡ plaquetteWilsonAtomSum background bondField plaquette
plaquetteWilsonIsSixteenAtoms background bondField plaquette =
  Jets.plaquetteWilsonIsSixteenAtomSum
    (plaquetteJetData background bondField plaquette)

physicalWilsonSecondVariation :
  RationalSU2Background4 → Physical.PhysicalSU2BondField4 → ℚ
physicalWilsonSecondVariation background bondField =
  Sums.sumRational plaquettes4
    (plaquetteWilsonSecondVariation background bondField)

physicalWilsonAtomSum :
  RationalSU2Background4 → Physical.PhysicalSU2BondField4 → ℚ
physicalWilsonAtomSum background bondField =
  Sums.sumRational plaquettes4
    (plaquetteWilsonAtomSum background bondField)

physicalWilsonSecondVariationIsSixteenAtomSum : ∀ background bondField →
  physicalWilsonSecondVariation background bondField
  ≡ physicalWilsonAtomSum background bondField
physicalWilsonSecondVariationIsSixteenAtomSum background bondField =
  Sums.sumRationalCong
    plaquettes4
    (plaquetteWilsonSecondVariation background bondField)
    (plaquetteWilsonAtomSum background bondField)
    (plaquetteWilsonIsSixteenAtoms background bondField)

------------------------------------------------------------------------
-- Identity-background specialization to the concrete flat curl energy.
------------------------------------------------------------------------

identityPlaquetteSecondVariationIsCurlSquare : ∀ bondField site axes →
  plaquetteWilsonSecondVariation
    identityBackground bondField (pair site axes)
  ≡ Wilson.vectorNormSq
      (Wilson.plaquetteCurlVector
        (insertionAt bondField (pairLeft axes) site)
        (insertionAt bondField (pairRight axes)
          (Hodge4.shiftForward (pairLeft axes) site))
        (insertionAt bondField (pairLeft axes)
          (Hodge4.shiftForward (pairRight axes) site))
        (insertionAt bondField (pairRight axes) site))
identityPlaquetteSecondVariationIsCurlSquare
    bondField site axes =
  ℚRing.solve-∀
    (bondField Physical.coordinateX (pair site (pairLeft axes)))
    (bondField Physical.coordinateY (pair site (pairLeft axes)))
    (bondField Physical.coordinateZ (pair site (pairLeft axes)))
    (bondField Physical.coordinateX
      (pair (Hodge4.shiftForward (pairLeft axes) site) (pairRight axes)))
    (bondField Physical.coordinateY
      (pair (Hodge4.shiftForward (pairLeft axes) site) (pairRight axes)))
    (bondField Physical.coordinateZ
      (pair (Hodge4.shiftForward (pairLeft axes) site) (pairRight axes)))
    (bondField Physical.coordinateX
      (pair (Hodge4.shiftForward (pairRight axes) site) (pairLeft axes)))
    (bondField Physical.coordinateY
      (pair (Hodge4.shiftForward (pairRight axes) site) (pairLeft axes)))
    (bondField Physical.coordinateZ
      (pair (Hodge4.shiftForward (pairRight axes) site) (pairLeft axes)))
    (bondField Physical.coordinateX (pair site (pairRight axes)))
    (bondField Physical.coordinateY (pair site (pairRight axes)))
    (bondField Physical.coordinateZ (pair site (pairRight axes)))

identityPairEnergy :
  Physical.PhysicalSU2BondField4 → AxisPair6 → ℚ
identityPairEnergy bondField axes =
  Sums.sumRational (Block.physicalBlockSites Path4.side4)
    (λ site →
      plaquetteWilsonSecondVariation
        identityBackground bondField (pair site axes))

identityPairEnergyIsFlatPair : ∀ bondField axes →
  identityPairEnergy bondField axes
  ≡ Flat.flatPlaquettePairEnergy bondField (pairLeft axes) (pairRight axes)
identityPairEnergyIsFlatPair bondField axes =
  trans
    (Sums.sumRationalCong
      (Block.physicalBlockSites Path4.side4)
      (λ site →
        plaquetteWilsonSecondVariation
          identityBackground bondField (pair site axes))
      (λ site →
        Flat.flatPlaquetteSecondVariation
          bondField (pairLeft axes) (pairRight axes) site)
      (λ site →
        trans
          (identityPlaquetteSecondVariationIsCurlSquare bondField site axes)
          (sym
            (Wilson.flatPlaquetteWilsonIsCurlSquare
              (Flat.insertionAt bondField (pairLeft axes) site)
              (Flat.insertionAt bondField (pairRight axes)
                (Hodge4.shiftForward (pairLeft axes) site))
              (Flat.insertionAt bondField (pairLeft axes)
                (Hodge4.shiftForward (pairRight axes) site))
              (Flat.insertionAt bondField (pairRight axes) site)))))
    (trans
      (Partition.globalSiteSumMatchesCoordinateSum4
        (Flat.flatPlaquetteSecondVariation
          bondField (pairLeft axes) (pairRight axes)))
      refl)

identityPhysicalWilsonIsFlatCurl : ∀ bondField →
  physicalWilsonSecondVariation identityBackground bondField
  ≡ Flat.flatWilsonEnergy bondField
identityPhysicalWilsonIsFlatCurl bondField =
  trans
    (Fubini.sumCartesian
      (Block.physicalBlockSites Path4.side4) axisPairs6
      (plaquetteWilsonSecondVariation identityBackground bondField))
    (trans
      (Sums.sumRationalCong
        (Block.physicalBlockSites Path4.side4)
        (λ site →
          Sums.sumRational axisPairs6
            (λ axes →
              plaquetteWilsonSecondVariation
                identityBackground bondField (pair site axes)))
        (λ site →
          Sums.sumRational axisPairs6
            (λ axes →
              plaquetteWilsonSecondVariation
                identityBackground bondField (pair site axes)))
        (λ _ → refl))
      (trans
        (Fubini.sumSwap
          (Block.physicalBlockSites Path4.side4) axisPairs6
          (λ site axes →
            plaquetteWilsonSecondVariation
              identityBackground bondField (pair site axes)))
        (trans
          (Sums.sumRationalCong
            axisPairs6
            (identityPairEnergy bondField)
            (λ axes →
              Flat.flatPlaquettePairEnergy bondField
                (pairLeft axes) (pairRight axes))
            (identityPairEnergyIsFlatPair bondField))
          (ℚRing.solve-∀
            (Flat.flatPlaquettePairEnergy bondField Hodge4.axis0 Hodge4.axis1)
            (Flat.flatPlaquettePairEnergy bondField Hodge4.axis0 Hodge4.axis2)
            (Flat.flatPlaquettePairEnergy bondField Hodge4.axis0 Hodge4.axis3)
            (Flat.flatPlaquettePairEnergy bondField Hodge4.axis1 Hodge4.axis2)
            (Flat.flatPlaquettePairEnergy bondField Hodge4.axis1 Hodge4.axis3)
            (Flat.flatPlaquettePairEnergy bondField Hodge4.axis2 Hodge4.axis3)))))

physicalWilsonDefect :
  RationalSU2Background4 → Physical.PhysicalSU2BondField4 → ℚ
physicalWilsonDefect background bondField =
  physicalWilsonSecondVariation background bondField
  - physicalWilsonSecondVariation identityBackground bondField

physicalWilsonDefectIsAtomDifference : ∀ background bondField →
  physicalWilsonDefect background bondField
  ≡ physicalWilsonAtomSum background bondField
    - physicalWilsonAtomSum identityBackground bondField
physicalWilsonDefectIsAtomDifference background bondField =
  cong₂ _-_
    (physicalWilsonSecondVariationIsSixteenAtomSum background bondField)
    (physicalWilsonSecondVariationIsSixteenAtomSum identityBackground bondField)

physicalWilsonDefectIsBackgroundMinusFlatCurl : ∀ background bondField →
  physicalWilsonDefect background bondField
  ≡ physicalWilsonSecondVariation background bondField
    - Flat.flatWilsonEnergy bondField
physicalWilsonDefectIsBackgroundMinusFlatCurl background bondField =
  cong
    (physicalWilsonSecondVariation background bondField -_)
    (identityPhysicalWilsonIsFlatCurl bondField)

rationalSU2InverseLevel : ProofLevel
rationalSU2InverseLevel = machineChecked

physicalRightExponentialLinkJetLevel : ProofLevel
physicalRightExponentialLinkJetLevel = machineChecked

physicalWilsonPlaquetteEnumerationLevel : ProofLevel
physicalWilsonPlaquetteEnumerationLevel = machineChecked

physicalWilsonSixteenAtomIdentificationLevel : ProofLevel
physicalWilsonSixteenAtomIdentificationLevel = machineChecked

physicalIdentityWilsonCurlLevel : ProofLevel
physicalIdentityWilsonCurlLevel = machineChecked

physicalWilsonDefectAtomDifferenceLevel : ProofLevel
physicalWilsonDefectAtomDifferenceLevel = machineChecked
