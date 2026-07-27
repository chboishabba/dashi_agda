module DASHI.Physics.YangMills.BalabanClayT3ConfiguredFiniteAtomListsExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _≤_; _/_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3LiteralPointwiseHessianEstimatesExact as Pointwise

------------------------------------------------------------------------
-- Concrete atom tags for the configured five-remainder proof.
--
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Relationship: the papers motivate the local background and averaging
-- expansions.  The finite tag lists and their order below are DASHI-owned and
-- remove the previous freedom to hide an unspecified atom family behind each
-- local estimate.
------------------------------------------------------------------------

data CurvatureAtom : Set where
  curvatureBracket01 curvatureBracket02 curvatureBracket03 curvatureBracket12 : CurvatureAtom
  curvatureBracket13 curvatureBracket23 : CurvatureAtom
  curvatureTransport01 curvatureTransport02 curvatureTransport03 curvatureTransport10 : CurvatureAtom
  curvatureTransport12 curvatureTransport13 curvatureTransport20 curvatureTransport21 : CurvatureAtom
  curvatureTransport23 curvatureTransport30 curvatureTransport31 curvatureTransport32 : CurvatureAtom

data TransportAtom : Set where
  transportForward0 transportBackward0 transportForward1 transportBackward1 : TransportAtom
  transportForward2 transportBackward2 transportForward3 transportBackward3 : TransportAtom

data ChartAtom : Set where
  chartAxis chartPerpendicular0 chartPerpendicular1 chartSkew : ChartAtom

data GaugeAtom : Set where
  gaugeIncoming0 gaugeOutgoing0 gaugeIncoming1 gaugeOutgoing1 : GaugeAtom
  gaugeIncoming2 gaugeOutgoing2 gaugeIncoming3 gaugeOutgoing3 : GaugeAtom
  gaugeCross0 gaugeCross1 gaugeCross2 gaugeCross3 : GaugeAtom
  gaugeSquare0 gaugeSquare1 gaugeSquare2 gaugeSquare3 : GaugeAtom

data ConstraintAtom : Set where
  blockPath0Step0 blockPath0Step1 blockPath0Step2 blockPath0Step3 : ConstraintAtom
  blockPath1Step0 blockPath1Step1 blockPath1Step2 blockPath1Step3 : ConstraintAtom
  blockPath2Step0 blockPath2Step1 blockPath2Step2 blockPath2Step3 : ConstraintAtom
  blockPath3Step0 blockPath3Step1 blockPath3Step2 blockPath3Step3 : ConstraintAtom

curvatureAtoms : List CurvatureAtom
curvatureAtoms =
  curvatureBracket01 ∷ curvatureBracket02 ∷ curvatureBracket03 ∷
  curvatureBracket12 ∷ curvatureBracket13 ∷ curvatureBracket23 ∷
  curvatureTransport01 ∷ curvatureTransport02 ∷ curvatureTransport03 ∷
  curvatureTransport10 ∷ curvatureTransport12 ∷ curvatureTransport13 ∷
  curvatureTransport20 ∷ curvatureTransport21 ∷ curvatureTransport23 ∷
  curvatureTransport30 ∷ curvatureTransport31 ∷ curvatureTransport32 ∷ []

transportAtoms : List TransportAtom
transportAtoms =
  transportForward0 ∷ transportBackward0 ∷
  transportForward1 ∷ transportBackward1 ∷
  transportForward2 ∷ transportBackward2 ∷
  transportForward3 ∷ transportBackward3 ∷ []

chartAtoms : List ChartAtom
chartAtoms = chartAxis ∷ chartPerpendicular0 ∷ chartPerpendicular1 ∷ chartSkew ∷ []

gaugeAtoms : List GaugeAtom
gaugeAtoms =
  gaugeIncoming0 ∷ gaugeOutgoing0 ∷ gaugeIncoming1 ∷ gaugeOutgoing1 ∷
  gaugeIncoming2 ∷ gaugeOutgoing2 ∷ gaugeIncoming3 ∷ gaugeOutgoing3 ∷
  gaugeCross0 ∷ gaugeCross1 ∷ gaugeCross2 ∷ gaugeCross3 ∷
  gaugeSquare0 ∷ gaugeSquare1 ∷ gaugeSquare2 ∷ gaugeSquare3 ∷ []

constraintAtoms : List ConstraintAtom
constraintAtoms =
  blockPath0Step0 ∷ blockPath0Step1 ∷ blockPath0Step2 ∷ blockPath0Step3 ∷
  blockPath1Step0 ∷ blockPath1Step1 ∷ blockPath1Step2 ∷ blockPath1Step3 ∷
  blockPath2Step0 ∷ blockPath2Step1 ∷ blockPath2Step2 ∷ blockPath2Step3 ∷
  blockPath3Step0 ∷ blockPath3Step1 ∷ blockPath3Step2 ∷ blockPath3Step3 ∷ []

curvatureCoefficient transportCoefficient chartCoefficient gaugeCoefficient constraintCoefficient : ℚ
curvatureCoefficient = + 32 / 1
transportCoefficient = + 64 / 1
chartCoefficient = + 32 / 1
gaugeCoefficient = + 64 / 1
constraintCoefficient = + 64 / 1

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

record FixedAtomExpansionInput
    (Background State Cell Atom : Set)
    (fixedAtoms : List Atom)
    (fixedCoefficient : ℚ) : Set₁ where
  field
    atomValue atomMajorant : Background → State → Cell → Atom → ℚ
    localRemainder localCharge radius : Background → State → Cell → ℚ

    expansionExact : ∀ background state cell →
      localRemainder background state cell
      ≡ Pointwise.sumℚ
          (map (atomValue background state cell) fixedAtoms)

    atomAbsoluteBound : ∀ background state cell atom →
      atomValue background state cell atom
      ≤ atomMajorant background state cell atom

    finiteAtomSumBound : ∀ background state cell →
      Pointwise.sumℚ (map (atomValue background state cell) fixedAtoms)
      ≤ Pointwise.sumℚ (map (atomMajorant background state cell) fixedAtoms)

    majorantSumBelowConfiguredCharge : ∀ background state cell →
      Pointwise.sumℚ (map (atomMajorant background state cell) fixedAtoms)
      ≤ fixedCoefficient * radius background state cell * localCharge background state cell

open FixedAtomExpansionInput public

asFinitePointwiseExpansion :
  ∀ {Background State Cell Atom fixedAtoms fixedCoefficient} →
  FixedAtomExpansionInput Background State Cell Atom fixedAtoms fixedCoefficient →
  Pointwise.FinitePointwiseExpansion Background State Cell Atom
asFinitePointwiseExpansion {fixedAtoms = fixedAtoms} {fixedCoefficient = coefficient} dataSet = record
  { atoms = λ _ _ _ → fixedAtoms
  ; atomValue = atomValue dataSet
  ; atomMajorant = atomMajorant dataSet
  ; localRemainder = localRemainder dataSet
  ; localCharge = localCharge dataSet
  ; radius = radius dataSet
  ; coefficient = λ _ _ _ → coefficient
  ; mappedValues = λ background state cell → map (atomValue dataSet background state cell)
  ; mappedMajorants = λ background state cell → map (atomMajorant dataSet background state cell)
  ; mappedValuesEmpty = λ _ _ _ → refl
  ; mappedValuesStep = λ _ _ _ _ _ → refl
  ; mappedMajorantsEmpty = λ _ _ _ → refl
  ; mappedMajorantsStep = λ _ _ _ _ _ → refl
  ; expansionExact = expansionExact dataSet
  ; atomAbsoluteBound = atomAbsoluteBound dataSet
  ; finiteAtomSumBound = finiteAtomSumBound dataSet
  ; majorantSumBelowConfiguredCharge = majorantSumBelowConfiguredCharge dataSet
  ; transitive = ℚP.≤-trans
  }

record ConfiguredFivePhysicalAtomInputs
    (Background State Plaquette Edge Link Site Block : Set) : Set₁ where
  field
    curvatureExpansion : FixedAtomExpansionInput
      Background State Plaquette CurvatureAtom curvatureAtoms curvatureCoefficient
    transportExpansion : FixedAtomExpansionInput
      Background State Edge TransportAtom transportAtoms transportCoefficient
    chartExpansion : FixedAtomExpansionInput
      Background State Link ChartAtom chartAtoms chartCoefficient
    gaugeExpansion : FixedAtomExpansionInput
      Background State Site GaugeAtom gaugeAtoms gaugeCoefficient
    constraintExpansion : FixedAtomExpansionInput
      Background State Block ConstraintAtom constraintAtoms constraintCoefficient

    wilsonPlaquetteSecondVariationAtBackgroundExact :
      ∀ background state plaquette → Set
    wilsonPlaquetteSecondVariationAtIdentityExact : ∀ state plaquette → Set
    plaquetteCurvatureDifferenceExact : ∀ background state plaquette → Set
    su2BracketCrossProductExact : ∀ background state plaquette atom → Set
    plaquetteHasFourOrientedEdges : ∀ plaquette → Set
    positiveEdgeOccursInSixPlaquettes : Set

    covariantForwardDifferenceExact : ∀ background state edge → Set
    adjointTransportMinusIdentityExact : ∀ background state edge → Set
    adjointTransportChordalBound : ∀ background state edge → Set
    transportedEdgeDifferenceExact : ∀ background state edge → Set
    orientedEdgeIncidenceExact : Set

    rightJacobianMetricExact : ∀ background link → Set
    rightJacobianInverseMetricExact : ∀ background link → Set
    pulledBackMetricUsesInverseTransposeInverse : ∀ background link → Set
    chartMetricMinusIdentityExact : ∀ background link → Set
    correctedPerpendicularSingularValueExact : ∀ background link → Set

    backgroundCovariantDivergenceExact : ∀ background state site → Set
    covariantDivergenceMinusReferenceExact : ∀ background state site → Set
    gaugeFixingQuadraticDifferenceExact : ∀ background state site → Set
    fixedYoungParameterExact : Set
    gaugeYoungInequalityBound : ∀ background state site → Set
    siteHasEightOrientedEdges : Set

    nonlinearBlockAverageDerivativeExact : ∀ background state block → Set
    referenceBlockAverageDerivativeExact : ∀ state block → Set
    blockPathTransportTelescopingExact : ∀ background state block → Set
    canonicalBoolean4PathLengthAtMostFour : Set
    blockPenaltyQuadraticDifferenceExact : ∀ background state block → Set

open ConfiguredFivePhysicalAtomInputs public

asLiteralFivePointwiseHessianPackage :
  ∀ {Background State Plaquette Edge Link Site Block} →
  ConfiguredFivePhysicalAtomInputs Background State Plaquette Edge Link Site Block →
  Pointwise.LiteralFivePointwiseHessianPackage
    Background State Plaquette Edge Link Site Block
    CurvatureAtom TransportAtom ChartAtom GaugeAtom ConstraintAtom
asLiteralFivePointwiseHessianPackage dataSet = record
  { curvature = record
      { expansion = asFinitePointwiseExpansion (curvatureExpansion dataSet)
      ; wilsonPlaquetteSecondVariationAtBackgroundExact =
          wilsonPlaquetteSecondVariationAtBackgroundExact dataSet
      ; wilsonPlaquetteSecondVariationAtIdentityExact =
          wilsonPlaquetteSecondVariationAtIdentityExact dataSet
      ; plaquetteCurvatureDifferenceExact = plaquetteCurvatureDifferenceExact dataSet
      ; su2BracketCrossProductExact = su2BracketCrossProductExact dataSet
      ; plaquetteHasFourOrientedEdges = plaquetteHasFourOrientedEdges dataSet
      ; positiveEdgeOccursInSixPlaquettes = positiveEdgeOccursInSixPlaquettes dataSet
      }
  ; transport = record
      { expansion = asFinitePointwiseExpansion (transportExpansion dataSet)
      ; covariantForwardDifferenceExact = covariantForwardDifferenceExact dataSet
      ; adjointTransportMinusIdentityExact = adjointTransportMinusIdentityExact dataSet
      ; adjointTransportChordalBound = adjointTransportChordalBound dataSet
      ; transportedEdgeDifferenceExact = transportedEdgeDifferenceExact dataSet
      ; orientedEdgeIncidenceExact = orientedEdgeIncidenceExact dataSet
      }
  ; chart = record
      { expansion = asFinitePointwiseExpansion (chartExpansion dataSet)
      ; rightJacobianMetricExact = rightJacobianMetricExact dataSet
      ; rightJacobianInverseMetricExact = rightJacobianInverseMetricExact dataSet
      ; pulledBackMetricUsesInverseTransposeInverse =
          pulledBackMetricUsesInverseTransposeInverse dataSet
      ; chartMetricMinusIdentityExact = chartMetricMinusIdentityExact dataSet
      ; correctedPerpendicularSingularValueExact =
          correctedPerpendicularSingularValueExact dataSet
      }
  ; gauge = record
      { expansion = asFinitePointwiseExpansion (gaugeExpansion dataSet)
      ; backgroundCovariantDivergenceExact = backgroundCovariantDivergenceExact dataSet
      ; covariantDivergenceMinusReferenceExact =
          covariantDivergenceMinusReferenceExact dataSet
      ; gaugeFixingQuadraticDifferenceExact = gaugeFixingQuadraticDifferenceExact dataSet
      ; fixedYoungParameterExact = fixedYoungParameterExact dataSet
      ; gaugeYoungInequalityBound = gaugeYoungInequalityBound dataSet
      ; siteHasEightOrientedEdges = siteHasEightOrientedEdges dataSet
      }
  ; constraint = record
      { expansion = asFinitePointwiseExpansion (constraintExpansion dataSet)
      ; nonlinearBlockAverageDerivativeExact = nonlinearBlockAverageDerivativeExact dataSet
      ; referenceBlockAverageDerivativeExact = referenceBlockAverageDerivativeExact dataSet
      ; blockPathTransportTelescopingExact = blockPathTransportTelescopingExact dataSet
      ; canonicalBoolean4PathLengthAtMostFour = canonicalBoolean4PathLengthAtMostFour dataSet
      ; blockPenaltyQuadraticDifferenceExact = blockPenaltyQuadraticDifferenceExact dataSet
      }
  }

configuredAtomListsLevel : ProofLevel
configuredAtomListsLevel = machineChecked

fixedAtomListAdapterLevel : ProofLevel
fixedAtomListAdapterLevel = machineChecked

literalConfiguredAtomValueInputsLevel : ProofLevel
literalConfiguredAtomValueInputsLevel = conditional
