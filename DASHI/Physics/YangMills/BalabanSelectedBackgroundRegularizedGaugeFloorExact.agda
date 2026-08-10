module DASHI.Physics.YangMills.BalabanSelectedBackgroundRegularizedGaugeFloorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics. DOI: 10.1007/978-3-642-66282-9.
--
-- DASHI CONTRIBUTION
--
-- Close the fixed-carrier coercivity problem for the selected background by
-- regularizing only with the *flat* constant projector.  For every multiplier
--
--   lambda = lambda_0 + c,
--
-- the preceding mean-decomposition theorem gives lambda_0 mean zero and an
-- exact orthogonal norm split.  The physical selected-background theorem gives
--
--   29/1024 ||lambda_0||^2 <= ||L_A^* lambda_0||^2,
--
-- while L_0^* c = 0 and the already proved selected-radius transpose defect
-- gives
--
--   ||L_A^* c||^2 <= 3/1024 ||c||^2.
--
-- Combining these with the exact finite perturbation inequality yields the
-- new all-multiplier theorem
--
--   29/2048 ||lambda||^2
--     <= ||L_A^* lambda||^2 + ||P_const lambda||^2.
--
-- This is a genuine positive floor on the full fixed 768-coordinate carrier.
-- It does NOT identify P_const with the moving physical stabilizer; it is a
-- fixed regularizer anchored at the flat operator, exactly as required before
-- constructing a background Green inverse by perturbation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact as GaugeMatrix
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as FlatAdjoint
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeReducedFloorExact as FlatFloor
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeAdjointDefectExact as Defect
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeReducedFloorExact as BackgroundFloor
import DASHI.Physics.YangMills.BalabanFiniteReducedFloorPerturbationExact as Perturb
import DASHI.Physics.YangMills.BalabanSelectedGaugeMeanDecompositionExact as Mean
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed

GaugeMultiplier : Set
GaugeMultiplier = FlatFloor.GaugeMultiplier

oneHalf : ℚ
oneHalf = Perturb.oneHalf

regularizedGaugeFloor : ℚ
regularizedGaugeFloor = + 29 / 2048

constantDefectCoefficient : ℚ
constantDefectCoefficient = Defect.selectedAdjointDefectCoefficient

constantFlatAdjointZero : ∀ multiplier selected →
  FlatAdjoint.actualFlatGaugeAdjoint
    (Mean.constantProjection multiplier) selected
  ≡ 0ℚ
constantFlatAdjointZero multiplier (pair coordinate (pair axis site)) =
  trans
    (FlatAdjoint.actualFlatGaugeAdjointPointwiseExact
      (Mean.constantProjection multiplier)
      (pair coordinate (pair axis site)))
    (ℚRing.solve-∀
      (Mean.scalarMean (FlatFloor.gaugeMultiplierField multiplier coordinate)))

backgroundConstantAdjointIsDefect : ∀ background multiplier selected →
  BackgroundFloor.backgroundGaugeAdjoint
    background (Mean.constantProjection multiplier) selected
  ≡ Defect.gaugeAdjointDefectApply
      background (Mean.constantProjection multiplier) selected
backgroundConstantAdjointIsDefect background multiplier selected =
  trans
    (BackgroundFloor.backgroundGaugeAdjointSplits
      background (Mean.constantProjection multiplier) selected)
    (trans
      (cong
        (_+ Defect.gaugeAdjointDefectApply
          background (Mean.constantProjection multiplier) selected)
        (constantFlatAdjointZero multiplier selected))
      (ℚRing.solve-∀
        (Defect.gaugeAdjointDefectApply
          background (Mean.constantProjection multiplier) selected)))

backgroundConstantAdjointNormExact : ∀ background multiplier →
  KKT.stateNormSq
    (BackgroundFloor.backgroundGaugeAdjoint
      background (Mean.constantProjection multiplier))
  ≡ Defect.gaugeAdjointDefectNormSq
      background (Mean.constantProjection multiplier)
backgroundConstantAdjointNormExact background multiplier =
  Sums.sumRationalCong Coordinates.physicalSU2Coordinates4 _ _
    (λ selected →
      cong₂ _*_
        (backgroundConstantAdjointIsDefect background multiplier selected)
        (backgroundConstantAdjointIsDefect background multiplier selected))

backgroundConstantAdjointUpper :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ multiplier →
  KKT.stateNormSq
    (BackgroundFloor.backgroundGaugeAdjoint
      background (Mean.constantProjection multiplier))
  ≤ constantDefectCoefficient
      * FlatFloor.gaugeMultiplierNormSq (Mean.constantProjection multiplier)
backgroundConstantAdjointUpper background radius multiplier =
  let
    constant = Mean.constantProjection multiplier
    raw = Defect.gaugeAdjointDefectSelectedRadiusBound
      background radius constant
    rowNormExact = BackgroundFloor.gaugeMultiplierRowNormSqExact constant
  in
  subst
    (λ left →
      left ≤ constantDefectCoefficient * FlatFloor.gaugeMultiplierNormSq constant)
    (sym (backgroundConstantAdjointNormExact background multiplier))
    (subst
      (λ norm →
        Defect.gaugeAdjointDefectNormSq background constant
        ≤ constantDefectCoefficient * norm)
      rowNormExact raw)

backgroundAdjointMeanSplit : ∀ background multiplier selected →
  BackgroundFloor.backgroundGaugeAdjoint background multiplier selected
  ≡ BackgroundFloor.backgroundGaugeAdjoint
      background (Mean.centeredMultiplier multiplier) selected
    + BackgroundFloor.backgroundGaugeAdjoint
      background (Mean.constantProjection multiplier) selected
backgroundAdjointMeanSplit background multiplier selected =
  let
    rows = Defect.gaugeRows

    pointwise : ∀ row →
      GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background row selected
        * multiplier row
      ≡ GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background row selected
        * Mean.centeredMultiplier multiplier row
        + GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background row selected
        * Mean.constantProjection multiplier row
    pointwise (pair coordinate site)
      rewrite Mean.multiplierSplitsPointwise multiplier coordinate site =
      ℚRing.solve-∀
        (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix
          background (pair coordinate site) selected)
        (Mean.centeredMultiplier multiplier (pair coordinate site))
        (Mean.constantProjection multiplier (pair coordinate site))
  in
  trans
    (Sums.sumRationalCong rows _ _ pointwise)
    (BackgroundFloor.sumRationalAddExact rows
      (λ row →
        GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background row selected
        * Mean.centeredMultiplier multiplier row)
      (λ row →
        GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background row selected
        * Mean.constantProjection multiplier row))

backgroundAdjointMeanNormExact : ∀ background multiplier →
  KKT.stateNormSq
    (KKT.stateVectorAdd
      (BackgroundFloor.backgroundGaugeAdjoint
        background (Mean.centeredMultiplier multiplier))
      (BackgroundFloor.backgroundGaugeAdjoint
        background (Mean.constantProjection multiplier)))
  ≡ KKT.stateNormSq
      (BackgroundFloor.backgroundGaugeAdjoint background multiplier)
backgroundAdjointMeanNormExact background multiplier =
  Sums.sumRationalCong Coordinates.physicalSU2Coordinates4 _ _
    (λ selected →
      let split = backgroundAdjointMeanSplit background multiplier selected
      in cong₂ _*_ (sym split) (sym split))

centeredSelected : GaugeMultiplier → BackgroundFloor.ReducedGaugeMultiplier
centeredSelected multiplier = record
  { BackgroundFloor.ReducedGaugeMultiplier.multiplier =
      Mean.centeredMultiplier multiplier
  ; BackgroundFloor.ReducedGaugeMultiplier.reduced =
      Mean.centeredMultiplierReduced multiplier
  }

centeredBackgroundAdjointLower :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ multiplier →
  BackgroundFloor.selectedBackgroundGaugeReducedFloor
    * FlatFloor.gaugeMultiplierNormSq (Mean.centeredMultiplier multiplier)
  ≤ KKT.stateNormSq
      (BackgroundFloor.backgroundGaugeAdjoint
        background (Mean.centeredMultiplier multiplier))
centeredBackgroundAdjointLower background radius multiplier =
  BackgroundFloor.selectedBackgroundGaugeAdjointReducedFloor
    background radius (centeredSelected multiplier)

fieldNormNonnegative : ∀ field →
  0ℚ ≤ Sums.sumRational (Block.physicalBlockSites Block.side4)
    (λ site → field site * field site)
fieldNormNonnegative field =
  Schur.sumNonnegative
    (Block.physicalBlockSites Block.side4)
    (λ site → field site * field site)
    (λ site → FiniteL2.squareNonnegative (field site))

gaugeMultiplierNormNonnegative : ∀ multiplier →
  0ℚ ≤ FlatFloor.gaugeMultiplierNormSq multiplier
gaugeMultiplierNormNonnegative multiplier =
  let
    x = FlatFloor.gaugeMultiplierField multiplier Coordinates.coordinateX
    y = FlatFloor.gaugeMultiplierField multiplier Coordinates.coordinateY
    z = FlatFloor.gaugeMultiplierField multiplier Coordinates.coordinateZ
  in
  FiniteL2.addNonnegative
    (FiniteL2.addNonnegative (fieldNormNonnegative x) (fieldNormNonnegative y))
    (fieldNormNonnegative z)

backgroundAdjointNormFromMeanPerturbation :
  ∀ background multiplier →
  oneHalf * KKT.stateNormSq
      (BackgroundFloor.backgroundGaugeAdjoint
        background (Mean.centeredMultiplier multiplier))
    - KKT.stateNormSq
      (BackgroundFloor.backgroundGaugeAdjoint
        background (Mean.constantProjection multiplier))
  ≤ KKT.stateNormSq
      (BackgroundFloor.backgroundGaugeAdjoint background multiplier)
backgroundAdjointNormFromMeanPerturbation background multiplier =
  let
    centeredAdjoint =
      BackgroundFloor.backgroundGaugeAdjoint
        background (Mean.centeredMultiplier multiplier)
    constantAdjoint =
      BackgroundFloor.backgroundGaugeAdjoint
        background (Mean.constantProjection multiplier)
    raw = Perturb.finiteVectorHalfMinusDefectLower
      KKT.physicalStateCarrier centeredAdjoint constantAdjoint
  in
  ℚP.≤-trans raw
    (subst
      (λ upper →
        KKT.stateNormSq (KKT.stateVectorAdd centeredAdjoint constantAdjoint)
        ≤ upper)
      (sym (backgroundAdjointMeanNormExact background multiplier))
      ℚP.≤-refl)

centeredHalfLower :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ multiplier →
  oneHalf
    * (BackgroundFloor.selectedBackgroundGaugeReducedFloor
      * FlatFloor.gaugeMultiplierNormSq (Mean.centeredMultiplier multiplier))
  ≤ oneHalf * KKT.stateNormSq
      (BackgroundFloor.backgroundGaugeAdjoint
        background (Mean.centeredMultiplier multiplier))
centeredHalfLower background radius multiplier =
  Norm.scaleNonnegative oneHalf
    (ℚP.nonNegative⁻¹ oneHalf)
    (centeredBackgroundAdjointLower background radius multiplier)

preRegularizedLower :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ multiplier →
  regularizedGaugeFloor
      * FlatFloor.gaugeMultiplierNormSq (Mean.centeredMultiplier multiplier)
    - constantDefectCoefficient
      * FlatFloor.gaugeMultiplierNormSq (Mean.constantProjection multiplier)
  ≤ KKT.stateNormSq
      (BackgroundFloor.backgroundGaugeAdjoint background multiplier)
preRegularizedLower background radius multiplier =
  let
    rNorm = FlatFloor.gaugeMultiplierNormSq (Mean.centeredMultiplier multiplier)
    cNorm = FlatFloor.gaugeMultiplierNormSq (Mean.constantProjection multiplier)
    rEnergy = KKT.stateNormSq
      (BackgroundFloor.backgroundGaugeAdjoint
        background (Mean.centeredMultiplier multiplier))
    cEnergy = KKT.stateNormSq
      (BackgroundFloor.backgroundGaugeAdjoint
        background (Mean.constantProjection multiplier))

    combined :
      oneHalf
          * (BackgroundFloor.selectedBackgroundGaugeReducedFloor * rNorm)
        - constantDefectCoefficient * cNorm
      ≤ oneHalf * rEnergy - cEnergy
    combined =
      ℚP.+-mono-≤
        (centeredHalfLower background radius multiplier)
        (ℚP.neg-antimono-≤
          (backgroundConstantAdjointUpper background radius multiplier))

    lowerExact :
      regularizedGaugeFloor * rNorm
        - constantDefectCoefficient * cNorm
      ≡ oneHalf
          * (BackgroundFloor.selectedBackgroundGaugeReducedFloor * rNorm)
        - constantDefectCoefficient * cNorm
    lowerExact = ℚRing.solve-∀ rNorm cNorm
  in
  subst
    (λ lower →
      lower ≤ KKT.stateNormSq
        (BackgroundFloor.backgroundGaugeAdjoint background multiplier))
    (sym lowerExact)
    (ℚP.≤-trans combined
      (backgroundAdjointNormFromMeanPerturbation background multiplier))

constantCoefficientUpper : ℚ
constantCoefficientUpper = (+ 1 / 1) - constantDefectCoefficient

regularizedBelowConstantCoefficient :
  regularizedGaugeFloor ≤ constantCoefficientUpper
regularizedBelowConstantCoefficient =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ difference → 0ℚ ≤ difference)
      (sym (ℚRing.solve []))
      (ℚP.nonNegative⁻¹ (+ 2013 / 2048)))

regularizedConstantPartComparison : ∀ multiplier →
  regularizedGaugeFloor
    * FlatFloor.gaugeMultiplierNormSq (Mean.constantProjection multiplier)
  ≤ constantCoefficientUpper
    * FlatFloor.gaugeMultiplierNormSq (Mean.constantProjection multiplier)
regularizedConstantPartComparison multiplier =
  let
    cNorm = FlatFloor.gaugeMultiplierNormSq (Mean.constantProjection multiplier)
    scaled = Norm.scaleNonnegative cNorm
      (gaugeMultiplierNormNonnegative (Mean.constantProjection multiplier))
      regularizedBelowConstantCoefficient
  in
  subst
    (λ lower →
      lower ≤ constantCoefficientUpper * cNorm)
    (ℚRing.solve-∀ cNorm)
    (subst
      (λ upper → cNorm * regularizedGaugeFloor ≤ upper)
      (ℚRing.solve-∀ cNorm)
      scaled)

regularizedGaugeEnergy :
  Physical.RationalSU2Background4 → GaugeMultiplier → ℚ
regularizedGaugeEnergy background multiplier =
  KKT.stateNormSq
    (BackgroundFloor.backgroundGaugeAdjoint background multiplier)
  + FlatFloor.gaugeMultiplierNormSq (Mean.constantProjection multiplier)
  where
  import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical

selectedBackgroundRegularizedGaugeFloor :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ multiplier →
  regularizedGaugeFloor * FlatFloor.gaugeMultiplierNormSq multiplier
  ≤ KKT.stateNormSq
      (BackgroundFloor.backgroundGaugeAdjoint background multiplier)
    + FlatFloor.gaugeMultiplierNormSq (Mean.constantProjection multiplier)
selectedBackgroundRegularizedGaugeFloor background radius multiplier =
  let
    rNorm = FlatFloor.gaugeMultiplierNormSq (Mean.centeredMultiplier multiplier)
    cNorm = FlatFloor.gaugeMultiplierNormSq (Mean.constantProjection multiplier)
    fullEnergy = KKT.stateNormSq
      (BackgroundFloor.backgroundGaugeAdjoint background multiplier)

    addRegularizer :
      (regularizedGaugeFloor * rNorm
        - constantDefectCoefficient * cNorm) + cNorm
      ≤ fullEnergy + cNorm
    addRegularizer =
      ℚP.+-monoʳ-≤ cNorm
        (preRegularizedLower background radius multiplier)

    normalizedAdd :
      regularizedGaugeFloor * rNorm
        + constantCoefficientUpper * cNorm
      ≤ fullEnergy + cNorm
    normalizedAdd =
      subst
        (λ lower → lower ≤ fullEnergy + cNorm)
        (ℚRing.solve-∀ rNorm cNorm)
        addRegularizer

    coefficientCompare :
      regularizedGaugeFloor * rNorm
        + regularizedGaugeFloor * cNorm
      ≤ regularizedGaugeFloor * rNorm
        + constantCoefficientUpper * cNorm
    coefficientCompare =
      ℚP.+-monoˡ-≤
        (regularizedGaugeFloor * rNorm)
        (regularizedConstantPartComparison multiplier)

    splitLower :
      regularizedGaugeFloor
        * FlatFloor.gaugeMultiplierNormSq multiplier
      ≡ regularizedGaugeFloor * rNorm
        + regularizedGaugeFloor * cNorm
    splitLower =
      trans
        (cong (regularizedGaugeFloor *_)
          (Mean.multiplierMeanPythagoras multiplier))
        (ℚRing.solve-∀ rNorm cNorm)
  in
  subst
    (λ lower → lower ≤ fullEnergy + cNorm)
    (sym splitLower)
    (ℚP.≤-trans coefficientCompare normalizedAdd)

selectedBackgroundRegularizedGaugeFloorLevel : ProofLevel
selectedBackgroundRegularizedGaugeFloorLevel = machineChecked

selectedBackgroundFullGaugeCarrierCoercivityLevel : ProofLevel
selectedBackgroundFullGaugeCarrierCoercivityLevel = machineChecked
