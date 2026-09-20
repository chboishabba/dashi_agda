module DASHI.Physics.Closure.NSTriadKNR571UnitNormalizedDisplacementWeldExact where

------------------------------------------------------------------------
-- PERIODIC B / UNIT-NORMALIZED LIVE <-> LATTICE DISPLACEMENT WELD
--
-- The generic rational IntegerEmbedding is intentionally scale-covariant:
--
--   normSquared_I(y) = E(1)^2 * |y|_Z^2.
--
-- R571's physical A1/A2 owners use the live normSquared_I(y), while the
-- discrete G2 owner uses the literal lattice displacement |y|_Z^2.  The repo
-- already has an explicit UnitPreservingIntegerEmbedding witness.  Under that
-- physical normalization E(1)=1, this module proves the two displacement
-- scalars are literally equal and transports the G2 and A1 bounds onto the
-- same object.  No normalization is silently assumed for arbitrary E.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 1ℚ; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalIntegerEmbeddingModeNormScaleExact as Scale
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact as Unit
import DASHI.Physics.Closure.NSTriadKNR571LatticeDisplacementG2Exact as Lattice
import DASHI.Physics.Closure.NSTriadKNR571HermitianScalarizedOppositePairExact as G0
import DASHI.Physics.Closure.NSTriadKNR571HermitianStateAmplitudeEnvelopeExact as G1
import DASHI.Physics.Closure.NSTriadKNR571DiscreteG2FromG1Exact as G2
import DASHI.Physics.Closure.NSTriadKNR571A1SameDisplacementExact as A1
import DASHI.Physics.Closure.NSTriadKNR571A2PhysicalSampleExact as A2
import DASHI.Physics.Closure.NSTriadKNR571A2SameDisplacementCompilerExact as A2Compiler
import DASHI.Physics.Closure.NSTriadKNPhysicalNormalizedAntiParallelComplementRound467Exact as R467
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNR571CenteredShiftTriangleExcessExact as Shift
import DASHI.Physics.Closure.NSTriadKNR571GateAEnvelopeCrosswalkExact as GateA
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicMultiplierTaylorDifferenceExact as Taylor
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311

F : C3.RealField _
F = Scale.F

embeddingUnitIsOne :
  ∀ {E : C3.IntegerEmbedding F} →
  Unit.UnitPreservingIntegerEmbedding F E →
  Scale.embeddingUnit E ≡ 1ℚ
embeddingUnitIsOne unit = Unit.embedPositiveOne unit

unitSquareIsOne :
  ∀ {E : C3.IntegerEmbedding F} →
  Unit.UnitPreservingIntegerEmbedding F E →
  Scale.unitSquare E ≡ 1ℚ
unitSquareIsOne {E = E} unit
  rewrite embeddingUnitIsOne unit =
  ℚP.*-identityˡ 1ℚ

liveSquaredDisplacementIsLattice :
  ∀ {E : C3.IntegerEmbedding F} →
  Unit.UnitPreservingIntegerEmbedding F E →
  (I : C3.ModeInverseSquare F E) →
  (shift : Z3.FourierMode) →
  C3.normSquared I shift
  ≡ Lattice.latticeSquaredDisplacement shift
liveSquaredDisplacementIsLattice {E = E} unit I shift =
  trans
    (Scale.modeNormCommonSquareScale E I shift)
    (trans
      (cong
        (λ scale → scale * Scale.modeNatNormAsRational shift)
        (unitSquareIsOne unit))
      (ℚP.*-identityˡ (Scale.modeNatNormAsRational shift)))

latticeSquaredDisplacementIsLive :
  ∀ {E : C3.IntegerEmbedding F} →
  Unit.UnitPreservingIntegerEmbedding F E →
  (I : C3.ModeInverseSquare F E) →
  (shift : Z3.FourierMode) →
  Lattice.latticeSquaredDisplacement shift
  ≡ C3.normSquared I shift
latticeSquaredDisplacementIsLive unit I shift =
  sym (liveSquaredDisplacementIsLattice unit I shift)

nonzeroLiveSquaredDisplacementAtLeastOne :
  ∀ {E : C3.IntegerEmbedding F} →
  Unit.UnitPreservingIntegerEmbedding F E →
  (I : C3.ModeInverseSquare F E) →
  (shift : Z3.FourierMode) →
  Z3.NonZeroMode shift →
  1ℚ ≤ C3.normSquared I shift
nonzeroLiveSquaredDisplacementAtLeastOne unit I shift nonzero =
  subst
    (1ℚ ≤_)
    (latticeSquaredDisplacementIsLive unit I shift)
    (Lattice.nonzeroLatticeSquaredDisplacementAtLeastOne shift nonzero)

liveHermitianG2 :
  ∀ {E : C3.IntegerEmbedding F} →
  Unit.UnitPreservingIntegerEmbedding F E →
  (I : C3.ModeInverseSquare F E) →
  (shift : Z3.FourierMode) →
  Z3.NonZeroMode shift →
  (XPlus XMinus D : C3.Complex3 F) →
  ∣ G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D ∣
  ≤
  C3.normSquared I shift
    * (G2.two * G1.stateAmplitudeEnvelope XPlus XMinus D)
liveHermitianG2 unit I shift nonzero XPlus XMinus D =
  subst
    (λ displacement →
      ∣ G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D ∣
      ≤ displacement
        * (G2.two * G1.stateAmplitudeEnvelope XPlus XMinus D))
    (latticeSquaredDisplacementIsLive unit I shift)
    (Lattice.latticeHermitianG2 shift nonzero XPlus XMinus D)

unitNormalizedPreferredLinearIncrementMagnitudeBound :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S sign center displacement output} →
  Unit.UnitPreservingIntegerEmbedding F E →
  Z3.NonZeroMode displacement →
  (D : R467.PhysicalNormalizedComplementData E I S
    (Shift.plusMode center displacement) center output) →
  ∣ Taylor.linearIncrement
      (GateA.preferredRadialTaylorPair
        sign S center
        (Shift.plusMode center displacement)
        (Shift.minusMode center displacement)) ∣
  ≤ Lattice.latticeSquaredDisplacement displacement
unitNormalizedPreferredLinearIncrementMagnitudeBound
    {I = I} {S = S} {sign = sign} {center = center}
    {displacement = displacement}
    unit nonzero D =
  subst
    (λ d →
      ∣ Taylor.linearIncrement
          (GateA.preferredRadialTaylorPair
            sign S center
            (Shift.plusMode center displacement)
            (Shift.minusMode center displacement)) ∣
      ≤ d)
    (liveSquaredDisplacementIsLattice unit I displacement)
    (A1.preferredLinearIncrementMagnitudeBound D
      (nonzeroLiveSquaredDisplacementAtLeastOne
        unit I displacement nonzero))

unitNormalizedPhysicalA2CompilerData :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S sign center displacement} →
  Unit.UnitPreservingIntegerEmbedding F E →
  (D : A2.PhysicalA2SampleData E I S sign center displacement) →
  A2Compiler.A2SameDisplacementData
    E I S sign center displacement
    (Lattice.latticeSquaredDisplacement displacement)
unitNormalizedPhysicalA2CompilerData
    {I = I} {displacement = displacement} unit D =
  subst
    (λ d →
      A2Compiler.A2SameDisplacementData
        _ I _ _ _ displacement d)
    (liveSquaredDisplacementIsLattice unit I displacement)
    (A2.physicalA2CompilerData D)

unitNormalizedLiveLatticeDisplacementWeldClosed : Bool
unitNormalizedLiveLatticeDisplacementWeldClosed = true

a1A2G2UseOneDisplacementUnderUnitNormalization : Bool
a1A2G2UseOneDisplacementUnderUnitNormalization = true

arbitraryScaledIntegerEmbeddingCollapsedByFiat : Bool
arbitraryScaledIntegerEmbeddingCollapsedByFiat = false

cutoffUniformG1FamilyEnvelopeClosedHere : Bool
cutoffUniformG1FamilyEnvelopeClosedHere = false

clayPromotion : Bool
clayPromotion = false

unitNormalizedLiveLatticeDisplacementWeldClosedIsTrue :
  unitNormalizedLiveLatticeDisplacementWeldClosed ≡ true
unitNormalizedLiveLatticeDisplacementWeldClosedIsTrue = refl

arbitraryScaledIntegerEmbeddingCollapsedByFiatIsFalse :
  arbitraryScaledIntegerEmbeddingCollapsedByFiat ≡ false
arbitraryScaledIntegerEmbeddingCollapsedByFiatIsFalse = refl
