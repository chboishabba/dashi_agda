module DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeRelativeFormExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", Springer Classics in
-- Mathematics. DOI: 10.1007/978-3-642-66282-9.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Verify the relative-form estimate suggested by the selected-background
-- constants already proved in Round 42.  Let
--
--   r = L_0^* lambda,
--   d = (L_A^* - L_0^*) lambda,
--   Q_0(lambda) = ||r||^2 + ||P_const lambda||^2.
--
-- The literal flat mean-zero floor and exact Pythagorean decomposition give
--
--   (1/16) ||lambda||^2 <= Q_0(lambda),
--
-- while the selected physical transpose defect gives
--
--   ||d||^2 <= (3/1024) ||lambda||^2
--             <= (3/64) Q_0(lambda).
--
-- The exact finite quarter-five inequality then yields
--
--   | ||r+d||^2 - ||r||^2 | <= (31/64) Q_0(lambda)
--
-- in two-sided ordered form, without introducing absolute-value or square-root
-- infrastructure.  Since the same P_const regularizer occurs at A and 0, this
-- is exactly the relative quadratic-form comparison
--
--   (33/64) Q_0 <= Q_A <= (95/64) Q_0.
--
-- Consequently the complete fixed 768-coordinate carrier has the stronger
-- selected-background floor
--
--   (33/1024) ||lambda||^2 <= Q_A(lambda).
--
-- This improves the earlier conservative 29/2048 bound.  It still treats
-- P_const only as a flat reference regularizer and makes no claim that flat
-- constant modes are the physical stabilizer at a noncentral background.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanPath4GeneratedLDLCertificate as LDL
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Periodic
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeReducedFloorExact as FlatFloor
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeAdjointGramFloorExact as FlatAdjoint
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeAdjointDefectExact as Defect
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeReducedFloorExact as BackgroundFloor
import DASHI.Physics.YangMills.BalabanSelectedGaugeMeanDecompositionExact as Mean
import DASHI.Physics.YangMills.BalabanSelectedBackgroundRegularizedGaugeFloorExact as PreviousFloor
import DASHI.Physics.YangMills.BalabanFiniteRelativeFormPerturbationExact as Relative

GaugeMultiplier : Set
GaugeMultiplier = FlatFloor.GaugeMultiplier

oneQuarter five sixteen : ℚ
oneQuarter = Relative.oneQuarter
five = Relative.five
sixteen = + 16 / 1

relativeDefectCoefficient relativePerturbationCoefficient : ℚ
relativeDefectCoefficient = + 3 / 64
relativePerturbationCoefficient = + 31 / 64

relativeLowerCoefficient relativeUpperCoefficient : ℚ
relativeLowerCoefficient = + 33 / 64
relativeUpperCoefficient = + 95 / 64

strongRegularizedGaugeFloor : ℚ
strongRegularizedGaugeFloor = + 33 / 1024

flatRegularizedGaugeEnergy : GaugeMultiplier → ℚ
flatRegularizedGaugeEnergy multiplier =
  KKT.stateNormSq (FlatAdjoint.actualFlatGaugeAdjoint multiplier)
  + FlatFloor.gaugeMultiplierNormSq (Mean.constantProjection multiplier)

backgroundRegularizedGaugeEnergy :
  Physical.RationalSU2Background4 → GaugeMultiplier → ℚ
backgroundRegularizedGaugeEnergy = PreviousFloor.regularizedGaugeEnergy

gaugePerturbationQuadratic :
  Physical.RationalSU2Background4 → GaugeMultiplier → ℚ
gaugePerturbationQuadratic background multiplier =
  backgroundRegularizedGaugeEnergy background multiplier
  - flatRegularizedGaugeEnergy multiplier

centeredForwardDifferenceExact :
  ∀ multiplier coordinate axis site →
  Periodic.forwardDifference axis
    (FlatAdjoint.multiplierField (Mean.centeredMultiplier multiplier) coordinate)
    site
  ≡ Periodic.forwardDifference axis
    (FlatAdjoint.multiplierField multiplier coordinate) site
centeredForwardDifferenceExact multiplier coordinate axis site =
  ℚRing.solve-∀
    (multiplier
      (pair coordinate (Periodic.shiftForward axis site)))
    (multiplier (pair coordinate site))
    (Mean.scalarMean (FlatFloor.gaugeMultiplierField multiplier coordinate))

flatAdjointIgnoresConstantProjectionPointwise :
  ∀ multiplier selected →
  FlatAdjoint.actualFlatGaugeAdjoint multiplier selected
  ≡ FlatAdjoint.actualFlatGaugeAdjoint
      (Mean.centeredMultiplier multiplier) selected
flatAdjointIgnoresConstantProjectionPointwise multiplier
    (pair coordinate (pair axis site)) =
  trans
    (FlatAdjoint.actualFlatGaugeAdjointPointwiseExact
      multiplier (pair coordinate (pair axis site)))
    (trans
      (cong -_
        (sym (centeredForwardDifferenceExact multiplier coordinate axis site)))
      (sym
        (FlatAdjoint.actualFlatGaugeAdjointPointwiseExact
          (Mean.centeredMultiplier multiplier)
          (pair coordinate (pair axis site)))))

flatAdjointIgnoresConstantProjectionNormExact : ∀ multiplier →
  KKT.stateNormSq (FlatAdjoint.actualFlatGaugeAdjoint multiplier)
  ≡ KKT.stateNormSq
      (FlatAdjoint.actualFlatGaugeAdjoint (Mean.centeredMultiplier multiplier))
flatAdjointIgnoresConstantProjectionNormExact multiplier =
  Sums.sumRationalCong Coordinates.physicalSU2Coordinates4 _ _
    (λ selected →
      cong₂ _*_
        (flatAdjointIgnoresConstantProjectionPointwise multiplier selected)
        (flatAdjointIgnoresConstantProjectionPointwise multiplier selected))

flatRegularizedMeanExact : ∀ multiplier →
  flatRegularizedGaugeEnergy multiplier
  ≡ KKT.stateNormSq
      (FlatAdjoint.actualFlatGaugeAdjoint (Mean.centeredMultiplier multiplier))
    + FlatFloor.gaugeMultiplierNormSq (Mean.constantProjection multiplier)
flatRegularizedMeanExact multiplier =
  cong
    (_+ FlatFloor.gaugeMultiplierNormSq (Mean.constantProjection multiplier))
    (flatAdjointIgnoresConstantProjectionNormExact multiplier)

oneSixteenthBelowOne : LDL.oneSixteenth ≤ 1ℚ
oneSixteenthBelowOne =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ difference → 0ℚ ≤ difference)
      (sym (ℚRing.solve [] : 1ℚ - LDL.oneSixteenth ≡ + 15 / 16))
      (ℚP.nonNegative⁻¹ (+ 15 / 16)))

flatRegularizedGaugeFloorOneSixteenth : ∀ multiplier →
  LDL.oneSixteenth * FlatFloor.gaugeMultiplierNormSq multiplier
  ≤ flatRegularizedGaugeEnergy multiplier
flatRegularizedGaugeFloorOneSixteenth multiplier =
  let
    centered = Mean.centeredMultiplier multiplier
    constant = Mean.constantProjection multiplier
    rNorm = FlatFloor.gaugeMultiplierNormSq centered
    cNorm = FlatFloor.gaugeMultiplierNormSq constant
    rEnergy = KKT.stateNormSq (FlatAdjoint.actualFlatGaugeAdjoint centered)

    rLower : LDL.oneSixteenth * rNorm ≤ rEnergy
    rLower = FlatAdjoint.actualFlatGaugeGramReducedFloor
      centered (Mean.centeredMultiplierReduced multiplier)

    cNonnegative : 0ℚ ≤ cNorm
    cNonnegative = PreviousFloor.gaugeMultiplierNormNonnegative constant

    cScaleRaw : cNorm * LDL.oneSixteenth ≤ cNorm * 1ℚ
    cScaleRaw = Norm.scaleNonnegative cNorm cNonnegative oneSixteenthBelowOne

    cLower : LDL.oneSixteenth * cNorm ≤ cNorm
    cLower =
      subst
        (λ lower → lower ≤ cNorm)
        (sym (ℚRing.solve-∀ cNorm :
          LDL.oneSixteenth * cNorm ≡ cNorm * LDL.oneSixteenth))
        (subst
          (λ upper → cNorm * LDL.oneSixteenth ≤ upper)
          (ℚRing.solve-∀ cNorm : cNorm * 1ℚ ≡ cNorm)
          cScaleRaw)

    combined :
      LDL.oneSixteenth * rNorm + LDL.oneSixteenth * cNorm
      ≤ rEnergy + cNorm
    combined = ℚP.+-mono-≤ rLower cLower

    leftExact :
      LDL.oneSixteenth * FlatFloor.gaugeMultiplierNormSq multiplier
      ≡ LDL.oneSixteenth * rNorm + LDL.oneSixteenth * cNorm
    leftExact =
      trans
        (cong (LDL.oneSixteenth *_)
          (Mean.multiplierMeanPythagoras multiplier))
        (ℚRing.solve-∀ rNorm cNorm)

    rightExact : rEnergy + cNorm ≡ flatRegularizedGaugeEnergy multiplier
    rightExact = sym (flatRegularizedMeanExact multiplier)
  in
  subst
    (λ lower → lower ≤ flatRegularizedGaugeEnergy multiplier)
    leftExact
    (subst
      (λ upper →
        LDL.oneSixteenth * rNorm + LDL.oneSixteenth * cNorm ≤ upper)
      rightExact combined)

flatAdjointEnergyBelowRegularized : ∀ multiplier →
  KKT.stateNormSq (FlatAdjoint.actualFlatGaugeAdjoint multiplier)
  ≤ flatRegularizedGaugeEnergy multiplier
flatAdjointEnergyBelowRegularized multiplier =
  let
    energy = KKT.stateNormSq (FlatAdjoint.actualFlatGaugeAdjoint multiplier)
    cNorm = FlatFloor.gaugeMultiplierNormSq (Mean.constantProjection multiplier)
    cNonnegative =
      PreviousFloor.gaugeMultiplierNormNonnegative
        (Mean.constantProjection multiplier)
    differenceExact :
      flatRegularizedGaugeEnergy multiplier - energy ≡ cNorm
    differenceExact = ℚRing.solve-∀ energy cNorm
  in
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ difference → 0ℚ ≤ difference)
      (sym differenceExact)
      cNonnegative)

multiplierNormControlledByFlatRegularized : ∀ multiplier →
  FlatFloor.gaugeMultiplierNormSq multiplier
  ≤ sixteen * flatRegularizedGaugeEnergy multiplier
multiplierNormControlledByFlatRegularized multiplier =
  let
    norm = FlatFloor.gaugeMultiplierNormSq multiplier
    q0 = flatRegularizedGaugeEnergy multiplier
    scaled = Norm.scaleNonnegative sixteen
      (ℚP.nonNegative⁻¹ sixteen)
      (flatRegularizedGaugeFloorOneSixteenth multiplier)

    leftExact : sixteen * (LDL.oneSixteenth * norm) ≡ norm
    leftExact = ℚRing.solve-∀ norm
  in
  subst
    (λ lower → lower ≤ sixteen * q0)
    leftExact scaled

defectNormRelativeUpper :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ multiplier →
  Defect.gaugeAdjointDefectNormSq background multiplier
  ≤ relativeDefectCoefficient * flatRegularizedGaugeEnergy multiplier
defectNormRelativeUpper background radius multiplier =
  let
    norm = FlatFloor.gaugeMultiplierNormSq multiplier
    q0 = flatRegularizedGaugeEnergy multiplier
    defectNorm = Defect.gaugeAdjointDefectNormSq background multiplier

    raw :
      defectNorm ≤ Defect.selectedAdjointDefectCoefficient * norm
    raw =
      subst
        (λ rowNorm →
          defectNorm ≤ Defect.selectedAdjointDefectCoefficient * rowNorm)
        (BackgroundFloor.gaugeMultiplierRowNormSqExact multiplier)
        (Defect.gaugeAdjointDefectSelectedRadiusBound
          background radius multiplier)

    scale :
      Defect.selectedAdjointDefectCoefficient * norm
      ≤ Defect.selectedAdjointDefectCoefficient * (sixteen * q0)
    scale = Norm.scaleNonnegative Defect.selectedAdjointDefectCoefficient
      (ℚP.nonNegative⁻¹ Defect.selectedAdjointDefectCoefficient)
      (multiplierNormControlledByFlatRegularized multiplier)

    coefficientExact :
      Defect.selectedAdjointDefectCoefficient * (sixteen * q0)
      ≡ relativeDefectCoefficient * q0
    coefficientExact = ℚRing.solve-∀ q0
  in
  ℚP.≤-trans raw
    (subst
      (λ upper →
        Defect.selectedAdjointDefectCoefficient * norm ≤ upper)
      coefficientExact scale)

backgroundAdjointNormSplitExact : ∀ background multiplier →
  KKT.stateNormSq (BackgroundFloor.backgroundGaugeAdjoint background multiplier)
  ≡ KKT.stateNormSq
      (Rect.vectorAdd
        (FlatAdjoint.actualFlatGaugeAdjoint multiplier)
        (Defect.gaugeAdjointDefectApply background multiplier))
backgroundAdjointNormSplitExact background multiplier =
  Sums.sumRationalCong Coordinates.physicalSU2Coordinates4 _ _
    (λ selected →
      cong₂ _*_
        (BackgroundFloor.backgroundGaugeAdjointSplits
          background multiplier selected)
        (BackgroundFloor.backgroundGaugeAdjointSplits
          background multiplier selected))

gaugePerturbationRegularizerCancels : ∀ background multiplier →
  gaugePerturbationQuadratic background multiplier
  ≡ KKT.stateNormSq (BackgroundFloor.backgroundGaugeAdjoint background multiplier)
    - KKT.stateNormSq (FlatAdjoint.actualFlatGaugeAdjoint multiplier)
gaugePerturbationRegularizerCancels background multiplier =
  ℚRing.solve-∀
    (KKT.stateNormSq (BackgroundFloor.backgroundGaugeAdjoint background multiplier))
    (KKT.stateNormSq (FlatAdjoint.actualFlatGaugeAdjoint multiplier))
    (FlatFloor.gaugeMultiplierNormSq (Mean.constantProjection multiplier))

gaugePerturbationFiniteDifferenceExact : ∀ background multiplier →
  gaugePerturbationQuadratic background multiplier
  ≡ KKT.stateNormSq
      (Rect.vectorAdd
        (FlatAdjoint.actualFlatGaugeAdjoint multiplier)
        (Defect.gaugeAdjointDefectApply background multiplier))
    - KKT.stateNormSq (FlatAdjoint.actualFlatGaugeAdjoint multiplier)
gaugePerturbationFiniteDifferenceExact background multiplier =
  trans
    (gaugePerturbationRegularizerCancels background multiplier)
    (cong
      (_- KKT.stateNormSq (FlatAdjoint.actualFlatGaugeAdjoint multiplier))
      (backgroundAdjointNormSplitExact background multiplier))

quarterFiveEnvelopeUpper :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ multiplier →
  oneQuarter * KKT.stateNormSq (FlatAdjoint.actualFlatGaugeAdjoint multiplier)
    + five * Defect.gaugeAdjointDefectNormSq background multiplier
  ≤ relativePerturbationCoefficient * flatRegularizedGaugeEnergy multiplier
quarterFiveEnvelopeUpper background radius multiplier =
  let
    q0 = flatRegularizedGaugeEnergy multiplier
    flatEnergy = KKT.stateNormSq (FlatAdjoint.actualFlatGaugeAdjoint multiplier)
    defectEnergy = Defect.gaugeAdjointDefectNormSq background multiplier

    flatPart : oneQuarter * flatEnergy ≤ oneQuarter * q0
    flatPart = Norm.scaleNonnegative oneQuarter
      (ℚP.nonNegative⁻¹ oneQuarter)
      (flatAdjointEnergyBelowRegularized multiplier)

    defectPart :
      five * defectEnergy ≤ five * (relativeDefectCoefficient * q0)
    defectPart = Norm.scaleNonnegative five
      (ℚP.nonNegative⁻¹ five)
      (defectNormRelativeUpper background radius multiplier)

    combined = ℚP.+-mono-≤ flatPart defectPart

    coefficientExact :
      oneQuarter * q0 + five * (relativeDefectCoefficient * q0)
      ≡ relativePerturbationCoefficient * q0
    coefficientExact = ℚRing.solve-∀ q0
  in
  subst
    (λ upper →
      oneQuarter * flatEnergy + five * defectEnergy ≤ upper)
    coefficientExact combined

selectedBackgroundGaugePerturbationRelativeFormUpper :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ multiplier →
  gaugePerturbationQuadratic background multiplier
  ≤ relativePerturbationCoefficient * flatRegularizedGaugeEnergy multiplier
selectedBackgroundGaugePerturbationRelativeFormUpper background radius multiplier =
  let
    reference = FlatAdjoint.actualFlatGaugeAdjoint multiplier
    defect = Defect.gaugeAdjointDefectApply background multiplier
    envelope =
      oneQuarter * KKT.stateNormSq reference
      + five * Defect.gaugeAdjointDefectNormSq background multiplier

    raw = Relative.finiteVectorQuarterFiveDifferenceUpper
      KKT.physicalStateCarrier reference defect

    identified : gaugePerturbationQuadratic background multiplier ≤ envelope
    identified =
      subst
        (λ lower → lower ≤ envelope)
        (sym (gaugePerturbationFiniteDifferenceExact background multiplier))
        raw
  in
  ℚP.≤-trans identified
    (quarterFiveEnvelopeUpper background radius multiplier)

selectedBackgroundGaugePerturbationRelativeFormLower :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ multiplier →
  - (relativePerturbationCoefficient * flatRegularizedGaugeEnergy multiplier)
  ≤ gaugePerturbationQuadratic background multiplier
selectedBackgroundGaugePerturbationRelativeFormLower background radius multiplier =
  let
    reference = FlatAdjoint.actualFlatGaugeAdjoint multiplier
    defect = Defect.gaugeAdjointDefectApply background multiplier
    envelope =
      oneQuarter * KKT.stateNormSq reference
      + five * Defect.gaugeAdjointDefectNormSq background multiplier

    rawDifference = Relative.finiteVectorQuarterFiveDifferenceLower
      KKT.physicalStateCarrier reference defect

    raw : - envelope ≤ gaugePerturbationQuadratic background multiplier
    raw =
      subst
        (λ upper → - envelope ≤ upper)
        (sym (gaugePerturbationFiniteDifferenceExact background multiplier))
        rawDifference

    envelopeUpper = quarterFiveEnvelopeUpper background radius multiplier
  in
  ℚP.≤-trans
    (ℚP.neg-antimono-≤ envelopeUpper)
    raw

record GaugePerturbationRelativeFormBound
    (background : Physical.RationalSU2Background4)
    (multiplier : GaugeMultiplier) : Set where
  field
    lower :
      - (relativePerturbationCoefficient * flatRegularizedGaugeEnergy multiplier)
      ≤ gaugePerturbationQuadratic background multiplier
    upper :
      gaugePerturbationQuadratic background multiplier
      ≤ relativePerturbationCoefficient * flatRegularizedGaugeEnergy multiplier

open GaugePerturbationRelativeFormBound public

selectedBackgroundGaugePerturbationRelativeFormBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ multiplier → GaugePerturbationRelativeFormBound background multiplier
selectedBackgroundGaugePerturbationRelativeFormBound background radius multiplier = record
  { lower = selectedBackgroundGaugePerturbationRelativeFormLower
      background radius multiplier
  ; upper = selectedBackgroundGaugePerturbationRelativeFormUpper
      background radius multiplier
  }

selectedBackgroundRegularizedGaugeRelativeFloor :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ multiplier →
  relativeLowerCoefficient * flatRegularizedGaugeEnergy multiplier
  ≤ backgroundRegularizedGaugeEnergy background multiplier
selectedBackgroundRegularizedGaugeRelativeFloor background radius multiplier =
  let
    q0 = flatRegularizedGaugeEnergy multiplier
    qA = backgroundRegularizedGaugeEnergy background multiplier
    perturb = gaugePerturbationQuadratic background multiplier
    lower = selectedBackgroundGaugePerturbationRelativeFormLower
      background radius multiplier

    combined : q0 + (- (relativePerturbationCoefficient * q0)) ≤ q0 + perturb
    combined = ℚP.+-monoˡ-≤ q0 lower

    leftExact :
      q0 + (- (relativePerturbationCoefficient * q0))
      ≡ relativeLowerCoefficient * q0
    leftExact = ℚRing.solve-∀ q0

    rightExact : q0 + perturb ≡ qA
    rightExact = ℚRing.solve-∀ q0 qA
  in
  subst
    (λ lowerValue → lowerValue ≤ qA)
    leftExact
    (subst
      (λ upperValue →
        q0 + (- (relativePerturbationCoefficient * q0)) ≤ upperValue)
      rightExact combined)

selectedBackgroundRegularizedGaugeRelativeUpper :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ multiplier →
  backgroundRegularizedGaugeEnergy background multiplier
  ≤ relativeUpperCoefficient * flatRegularizedGaugeEnergy multiplier
selectedBackgroundRegularizedGaugeRelativeUpper background radius multiplier =
  let
    q0 = flatRegularizedGaugeEnergy multiplier
    qA = backgroundRegularizedGaugeEnergy background multiplier
    perturb = gaugePerturbationQuadratic background multiplier
    upper = selectedBackgroundGaugePerturbationRelativeFormUpper
      background radius multiplier

    combined : q0 + perturb ≤ q0 + relativePerturbationCoefficient * q0
    combined = ℚP.+-monoˡ-≤ q0 upper

    leftExact : q0 + perturb ≡ qA
    leftExact = ℚRing.solve-∀ q0 qA

    rightExact :
      q0 + relativePerturbationCoefficient * q0
      ≡ relativeUpperCoefficient * q0
    rightExact = ℚRing.solve-∀ q0
  in
  subst
    (λ lowerValue → lowerValue ≤ relativeUpperCoefficient * q0)
    leftExact
    (subst
      (λ upperValue → q0 + perturb ≤ upperValue)
      rightExact combined)

selectedBackgroundRegularizedGaugeFloorThirtyThreeOver1024 :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ multiplier →
  strongRegularizedGaugeFloor * FlatFloor.gaugeMultiplierNormSq multiplier
  ≤ backgroundRegularizedGaugeEnergy background multiplier
selectedBackgroundRegularizedGaugeFloorThirtyThreeOver1024
    background radius multiplier =
  let
    norm = FlatFloor.gaugeMultiplierNormSq multiplier
    q0 = flatRegularizedGaugeEnergy multiplier

    scaledFlat = Norm.scaleNonnegative relativeLowerCoefficient
      (ℚP.nonNegative⁻¹ relativeLowerCoefficient)
      (flatRegularizedGaugeFloorOneSixteenth multiplier)

    coefficientExact :
      relativeLowerCoefficient * (LDL.oneSixteenth * norm)
      ≡ strongRegularizedGaugeFloor * norm
    coefficientExact = ℚRing.solve-∀ norm

    first : strongRegularizedGaugeFloor * norm ≤ relativeLowerCoefficient * q0
    first =
      subst
        (λ lower → lower ≤ relativeLowerCoefficient * q0)
        coefficientExact scaledFlat
  in
  ℚP.≤-trans first
    (selectedBackgroundRegularizedGaugeRelativeFloor
      background radius multiplier)

selectedBackgroundGaugeRelativeFormLevel : ProofLevel
selectedBackgroundGaugeRelativeFormLevel = machineChecked

selectedBackgroundRegularizedGaugeRelativeComparisonLevel : ProofLevel
selectedBackgroundRegularizedGaugeRelativeComparisonLevel = machineChecked

selectedBackgroundRegularizedGaugeThirtyThreeOver1024Level : ProofLevel
selectedBackgroundRegularizedGaugeThirtyThreeOver1024Level = machineChecked
