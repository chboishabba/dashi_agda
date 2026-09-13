module DASHI.Physics.Closure.NSTriadKNSpectatorNestedOuterCellMassThreeOrbitBidiExact where

------------------------------------------------------------------------
-- OUTER SPECTATOR-WEIGHTED POSITIVE CELL MASS -> THREE-ORBIT ENVELOPE
--
-- The selected outer Gram ledger leaves positive cell mass plus signed outer
-- Gram debt.  This owner pays only the positive cell-mass half.
--
-- On one fixed nonzero output fibre the R541 resolvent obeys
--
--   w_beta(alpha)^2 <= C_nu^2,  C_nu = 1/(2 nu).
--
-- For p_alpha != 0 the nested-slot norm is bounded by the exact three-orbit
-- Bony envelope obtained after the consumer-paid LH <-> HL quotient.  For
-- p_alpha = 0, R573's actual nested weighted companion cell is definitionally
-- zero.  Thus no illegal normalized-direction-at-zero premise is introduced.
--
-- The remaining outer obstruction after this file is therefore the SELECTED
-- signed Gram/gluing debt, not the positive cell mass and not a fibre-cardinality
-- multiplier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; Positive; NonNegative; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramLedgerRound180Exact as R180
import DASHI.Physics.Closure.NSTriadKNFibreLocalPositiveR290EnumerationRound396Exact as R396
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNHHAntiParallelQuadraticKernelNormRound174Exact as R174
import DASHI.Physics.Closure.NSTriadKNRationalNormalizedDirectionUnitRound455Exact as R455
import DASHI.Physics.Closure.NSTriadKNNormalizedDoubleMixedCellMassRound452Exact as R452
import DASHI.Physics.Closure.NSTriadKNFourHelicityVectorRecombinationRound576Exact as R576
import DASHI.Physics.Closure.NSTriadKNCanonicalFourierUnitGapRateFloorRound450Exact as R450
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventUnitGapCeilingBidiExact as CeilingOwner
import DASHI.Physics.Closure.NSTriadKNSpectatorWeightedExactClassEnvelopeBidiExact as EnvelopeOwner
import DASHI.Physics.Closure.NSTriadKNSpectatorNestedOuterGramGluingBidiExact as OuterOwner

F : C3.RealField _
F = Rational.rationalRealField

module OuterMass
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode))
    (viscosityPositive : Positive (Field30.viscosity physicalSystem))
    (unitGap : R450.CanonicalFourierUnitGap physicalSystem)
    (output : Z3.FourierMode)
    (outputNonzero : Z3.NonZeroMode output)
    (beta : Physical.PhysicalTriadIncidence)
    (betaOutput : Physical.k beta ≡ output) where

  module Ceiling = CeilingOwner.SameOutputResolventCeiling
    physicalSystem S viscosityPositive unitGap
  module Env = EnvelopeOwner.ExactEnvelope physicalSystem S L H velocityTransverse
  module E = Env.AtSpectator beta
  module Outer = OuterOwner.OuterGluing physicalSystem S L H velocityTransverse
  module O = Outer.AtSpectator beta
  module N = O.N

  c2 : ℚ
  c2 = Ceiling.ceiling * Ceiling.ceiling

  c2Nonnegative : 0ℚ ≤ c2
  c2Nonnegative =
    Rational.productNonnegative Ceiling.ceilingNonnegative Ceiling.ceilingNonnegative

  outerEnvelope : Physical.PhysicalTriadIncidence → ℚ
  outerEnvelope alpha with Output.modeEqual (Physical.p alpha) Z3.zeroMode
  ... | true = 0ℚ
  ... | false = c2 * (R576.four * E.exactThreeOrbitEnvelope alpha)

  pNonzeroFromDecision :
    (alpha : Physical.PhysicalTriadIncidence) →
    Output.modeEqual (Physical.p alpha) Z3.zeroMode ≡ false →
    Z3.NonZeroMode (Physical.p alpha)
  pNonzeroFromDecision alpha pDecision = record
    { Z3.notZero = λ pZero →
        Output.falseNotTrue
          (trans (sym pDecision) (Output.modeEqualComplete pZero))
    }

  iNestedNorm :
    (alpha : Physical.PhysicalTriadIncidence) →
    L2.complex3NormSquared
      (C3.complex3Scale (C3.complexI F) (N.nestedSlotFold alpha))
    ≡ L2.complex3NormSquared (N.nestedSlotFold alpha)
  iNestedNorm alpha = R452.iScalePreservesNorm (N.nestedSlotFold alpha)

  nonzeroOuterCellNormMeaning :
    (alpha : Physical.PhysicalTriadIncidence) →
    Output.modeEqual (Physical.p alpha) Z3.zeroMode ≡ false →
    L2.complex3NormSquared (O.outerCell alpha)
    ≡
    (Ceiling.Pair.pairResolvent alpha beta * Ceiling.Pair.pairResolvent alpha beta)
      * L2.complex3NormSquared (N.nestedSlotFold alpha)
  nonzeroOuterCellNormMeaning alpha pDecision
    with Output.modeEqual (Physical.p alpha) Z3.zeroMode in sameDecision
  ... | true = Output.falseNotTrue (trans (sym pDecision) sameDecision)
  ... | false =
    let
      r = Ceiling.Pair.pairResolvent alpha beta
      weightMeaning = Outer.SN.Spec.spectatorWeightMeaning beta alpha
      scaledI = C3.complex3Scale (C3.complexI F) (N.nestedSlotFold alpha)
      first =
        R174.normScale
          (R294.weight (Outer.SN.Spec.spectatorWeight beta) alpha)
          scaledI
      weightModulus :
        L2.complexModulusSquared
          (R294.weight (Outer.SN.Spec.spectatorWeight beta) alpha)
        ≡ r * r
      weightModulus =
        trans
          (cong L2.complexModulusSquared weightMeaning)
          (R455.realEmbedModulusSquared r)
    in
    trans first (cong₂ _*_ weightModulus (iNestedNorm alpha))

  outerCellMassBelowEnvelope :
    (alpha : Physical.PhysicalTriadIncidence) →
    Physical.k alpha ≡ output →
    L2.complex3NormSquared (O.outerCell alpha) ≤ outerEnvelope alpha
  outerCellMassBelowEnvelope alpha alphaOutput
    with Output.modeEqual (Physical.p alpha) Z3.zeroMode in pDecision
  ... | true =
    subst
      (_≤ 0ℚ)
      (sym R180.zeroCellMass)
      ℚP.≤-refl
  ... | false =
    let
      pNonzero = pNonzeroFromDecision alpha pDecision
      r2Below = Ceiling.pairResolventSquareBelowCeilingSquare
        output outputNonzero alpha beta alphaOutput betaOutput
      slotBound = E.nestedSlotBelowExactThreeOrbitEnvelope alpha pNonzero
      slotNN = Separation.complex3NormSquaredNonnegative (N.nestedSlotFold alpha)
      scaleWeight :
        (Ceiling.Pair.pairResolvent alpha beta * Ceiling.Pair.pairResolvent alpha beta)
          * L2.complex3NormSquared (N.nestedSlotFold alpha)
        ≤ c2 * L2.complex3NormSquared (N.nestedSlotFold alpha)
      scaleWeight =
        let instance slotNNI : NonNegative
              (L2.complex3NormSquared (N.nestedSlotFold alpha)) = nonNegative slotNN
        in ℚP.*-monoʳ-≤-nonNeg
          (L2.complex3NormSquared (N.nestedSlotFold alpha)) r2Below
      scaleSlot :
        c2 * L2.complex3NormSquared (N.nestedSlotFold alpha)
        ≤ c2 * (R576.four * E.exactThreeOrbitEnvelope alpha)
      scaleSlot =
        let instance c2NNI : NonNegative c2 = nonNegative c2Nonnegative
        in ℚP.*-monoˡ-≤-nonNeg c2 slotBound
      core = ℚP.≤-trans scaleWeight scaleSlot
    in
    subst
      (λ lower → lower ≤ c2 * (R576.four * E.exactThreeOrbitEnvelope alpha))
      (sym (nonzeroOuterCellNormMeaning alpha pDecision))
      core

  outerEnvelopeSum : List Physical.PhysicalTriadIncidence → ℚ
  outerEnvelopeSum [] = 0ℚ
  outerEnvelopeSum (alpha ∷ rest) = outerEnvelope alpha + outerEnvelopeSum rest

  outerCellMassSumBelowEnvelopeSum :
    (items : List Physical.PhysicalTriadIncidence) →
    ((alpha : Physical.PhysicalTriadIncidence) →
      alpha R396.OccursIn items → Physical.k alpha ≡ output) →
    R180.cellMassSum (O.outerCells items) ≤ outerEnvelopeSum items
  outerCellMassSumBelowEnvelopeSum [] allOutput = ℚP.≤-refl
  outerCellMassSumBelowEnvelopeSum (alpha ∷ rest) allOutput =
    ℚP.+-mono-≤
      (outerCellMassBelowEnvelope alpha (allOutput alpha R396.here))
      (outerCellMassSumBelowEnvelopeSum rest
        (λ selected member → allOutput selected (R396.there member)))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

outerZeroBranchHandledWithoutNormalizedDirectionPremise : Bool
outerZeroBranchHandledWithoutNormalizedDirectionPremise = true

outerPositiveCellMassPaidByThreeOrbitEnvelope : Bool
outerPositiveCellMassPaidByThreeOrbitEnvelope = true

outerPositiveCellMassIntroducesCardinalityTax : Bool
outerPositiveCellMassIntroducesCardinalityTax = false

outerSelectedSignedGramDebtStillOpen : Bool
outerSelectedSignedGramDebtStillOpen = true

cutoffUniformSpacetimeThreeOrbitEnvelopePaid : Bool
cutoffUniformSpacetimeThreeOrbitEnvelopePaid = false

clayPromotion : Bool
clayPromotion = false
