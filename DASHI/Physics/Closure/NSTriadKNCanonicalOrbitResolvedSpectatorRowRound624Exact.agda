{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNCanonicalOrbitResolvedSpectatorRowRound624Exact where

------------------------------------------------------------------------
-- ROUND624 / CANONICAL ORBIT-RESOLVED EXTERNAL TERM IN THE LITERAL R545 ROW
--
-- R545/R573 already put the literal spectator-resolvent scalar row on
--
--   2 * ( <NestedForce , DoubleCell_beta>
--         + <FourAmplitude , DoubleForcing_beta> ).
--
-- R613 splits NestedForce pointwise into selected-self + external-network.
-- R622 rewrites the complete external fold onto the canonical total
-- fixed/nonfixed orbit-resolved carrier.
--
-- This owner pushes both equalities through the ACTUAL R545 scalar consumer:
--
--   <NestedForce , D_beta>
--     = <SelfForce , D_beta>
--       + <CanonicalExternalForce , D_beta>.
--
-- The independent amplitude half is preserved literally.  No estimate, norm,
-- absolute value, shell bound, time integration, or cutoff-uniform payment is
-- introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventRowFactorizationRound545Exact as R545
import DASHI.Physics.Closure.NSTriadKNSpectatorNestedRowFactorizationBidiExact as NestedRowWeld
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventNestedCommutatorBidiExact as SpectatorWeld
import DASHI.Physics.Closure.NSTriadKNR573SelfExternalNestedCompanionSplitRound613Exact as R613
import DASHI.Physics.Closure.NSTriadKNCanonicalOrbitResolvedExternalNestedFoldRound622Exact as R622

F : C3.RealField _
F = Rational.rationalRealField

module CanonicalSpectatorRow624
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
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  system = Field30.finiteSystem physicalSystem

  module Row = R545.Row physicalSystem S
  module Spec = R541.Spectator physicalSystem S
  module NestedRow =
    NestedRowWeld.NestedRow physicalSystem S L H velocityTransverse
  module Spectator =
    SpectatorWeld.SpectatorNested physicalSystem S L H velocityTransverse

  items : Z3.FourierMode → List Physical.PhysicalTriadIncidence
  items output =
    Output.physicalOutputFiber (Audit.cutoff system) output

  module At
      (beta : Physical.PhysicalTriadIncidence) where

    W = Spec.spectatorWeight beta

    module Nested = Spectator.Nested beta
    module Split =
      R613.NestedNetworkSplit W S L H system velocityTransverse
    module Canonical =
      R622.CanonicalExternalNested W S L H system velocityTransverse

    selfFold : Z3.FourierMode → C3.Complex3 F
    selfFold output =
      R224.foldVector
        Split.selfNestedWeightedCompanionCell
        (items output)

    externalFold : Z3.FourierMode → C3.Complex3 F
    externalFold output =
      R224.foldVector
        Split.externalNestedWeightedCompanionCell
        (items output)

    canonicalExternalFold : Z3.FourierMode → C3.Complex3 F
    canonicalExternalFold =
      Canonical.canonicalExternalNestedFold

    nestedFold : Z3.FourierMode → C3.Complex3 F
    nestedFold output =
      R224.foldVector
        Nested.nestedWeightedCompanionCell
        (items output)

    nestedFoldSplitsSelfExternal :
      (output : Z3.FourierMode) →
      nestedFold output
      ≡ C3.complex3Add (selfFold output) (externalFold output)
    nestedFoldSplitsSelfExternal output =
      trans
        (R230.foldCongruent
          Nested.nestedWeightedCompanionCell
          (λ tau →
            C3.complex3Add
              (Split.selfNestedWeightedCompanionCell tau)
              (Split.externalNestedWeightedCompanionCell tau))
          (Split.nestedWeightedCompanionSplitsSelfExternal)
          (items output))
        (R230.foldAdd
          Split.selfNestedWeightedCompanionCell
          Split.externalNestedWeightedCompanionCell
          (items output))

    nestedFoldSplitsSelfCanonicalExternal :
      (output : Z3.FourierMode) →
      nestedFold output
      ≡
      C3.complex3Add
        (selfFold output)
        (canonicalExternalFold output)
    nestedFoldSplitsSelfCanonicalExternal output =
      trans
        (nestedFoldSplitsSelfExternal output)
        (cong
          (C3.complex3Add (selfFold output))
          (Canonical.fixedOutputExternalNestedFoldIsCanonical output))

    nestedForceScalarSplitsSelfCanonicalExternal :
      (output : Z3.FourierMode) →
      R179.realHermitianCross
        (nestedFold output)
        (Row.doubleCell beta)
      ≡
      R179.realHermitianCross
        (selfFold output)
        (Row.doubleCell beta)
      +
      R179.realHermitianCross
        (canonicalExternalFold output)
        (Row.doubleCell beta)
    nestedForceScalarSplitsSelfCanonicalExternal output =
      trans
        (cong
          (λ force →
            R179.realHermitianCross force (Row.doubleCell beta))
          (nestedFoldSplitsSelfCanonicalExternal output))
        (R291.realCrossAddLeft
          (selfFold output)
          (canonicalExternalFold output)
          (Row.doubleCell beta))

    --------------------------------------------------------------------
    -- Literal R545 row consequence.  The amplitude term remains untouched.
    --------------------------------------------------------------------

    spectatorRowUsesCanonicalExternalScalar :
      (output : Z3.FourierMode) →
      let
        A = R224.foldVector (Row.Weighted.Amp.amplitude beta) (items output)
        fourA = C3.complex3Add
          (C3.complex3Add A A)
          (C3.complex3Add A A)
      in
      Row.spectatorRow beta (items output)
      ≡
      R291.two *
        ( ( R179.realHermitianCross
              (selfFold output)
              (Row.doubleCell beta)
          + R179.realHermitianCross
              (canonicalExternalFold output)
              (Row.doubleCell beta)
          )
        + R179.realHermitianCross
            fourA
            (Row.D.doubleForcing beta)
        )
    spectatorRowUsesCanonicalExternalScalar output =
      let
        A = R224.foldVector (Row.Weighted.Amp.amplitude beta) (items output)
        fourA = C3.complex3Add
          (C3.complex3Add A A)
          (C3.complex3Add A A)
      in
      trans
        (NestedRow.fixedOutputSpectatorRowFactorsThroughNestedForce
          output beta)
        (cong
          (λ forceScalar →
            R291.two *
              (forceScalar
                + R179.realHermitianCross
                    fourA
                    (Row.D.doubleForcing beta)))
          (nestedForceScalarSplitsSelfCanonicalExternal output))

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round624NestedForceFoldSelfCanonicalExternalSplitClosed : Bool
round624NestedForceFoldSelfCanonicalExternalSplitClosed = true

round624LiteralR545ExternalScalarCanonicalized : Bool
round624LiteralR545ExternalScalarCanonicalized = true

round624AmplitudeHalfPreservedLiterally : Bool
round624AmplitudeHalfPreservedLiterally = true

round624RequiresLegacyR112WitnessFamily : Bool
round624RequiresLegacyR112WitnessFamily = false

round624IntroducesNormOrAbsoluteValue : Bool
round624IntroducesNormOrAbsoluteValue = false

round624IntroducesEstimate : Bool
round624IntroducesEstimate = false

round624CanonicalExternalScalarBudgetClosed : Bool
round624CanonicalExternalScalarBudgetClosed = false

round624NestedForceFoldSelfCanonicalExternalSplitClosedIsTrue :
  round624NestedForceFoldSelfCanonicalExternalSplitClosed ≡ true
round624NestedForceFoldSelfCanonicalExternalSplitClosedIsTrue = refl

round624LiteralR545ExternalScalarCanonicalizedIsTrue :
  round624LiteralR545ExternalScalarCanonicalized ≡ true
round624LiteralR545ExternalScalarCanonicalizedIsTrue = refl

round624AmplitudeHalfPreservedLiterallyIsTrue :
  round624AmplitudeHalfPreservedLiterally ≡ true
round624AmplitudeHalfPreservedLiterallyIsTrue = refl

round624RequiresLegacyR112WitnessFamilyIsFalse :
  round624RequiresLegacyR112WitnessFamily ≡ false
round624RequiresLegacyR112WitnessFamilyIsFalse = refl

round624IntroducesNormOrAbsoluteValueIsFalse :
  round624IntroducesNormOrAbsoluteValue ≡ false
round624IntroducesNormOrAbsoluteValueIsFalse = refl

round624IntroducesEstimateIsFalse :
  round624IntroducesEstimate ≡ false
round624IntroducesEstimateIsFalse = refl

round624CanonicalExternalScalarBudgetClosedIsFalse :
  round624CanonicalExternalScalarBudgetClosed ≡ false
round624CanonicalExternalScalarBudgetClosedIsFalse = refl
