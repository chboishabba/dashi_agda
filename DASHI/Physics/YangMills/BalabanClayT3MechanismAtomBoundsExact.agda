module DASHI.Physics.YangMills.BalabanClayT3MechanismAtomBoundsExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; _≤_)

import DASHI.Physics.YangMills.BalabanClayT2GeneratedQuaternionJetExact as Jet
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredFiniteAtomListsExact as Fixed
import DASHI.Physics.YangMills.BalabanClayT3LiteralFixedAtomFormulaInstanceExact as Formula
import DASHI.Physics.YangMills.BalabanClayT3LiteralPointwiseHessianEstimatesExact as Pointwise
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Replace sixty-two atom-by-atom assumptions by the five actual mechanisms:
-- bracket/adjoint transport, covariant edge difference, right-Jacobian metric,
-- divergence Young bounds, and block-path telescoping.
------------------------------------------------------------------------

record MechanismAtomBounds
    {Background State Plaquette Edge Link Site Block : Set}
    (environment :
      Formula.LiteralFixedAtomEnvironment
        Background State Plaquette Edge Link Site Block) : Set₁ where
  field
    bracketBound : ∀ background state plaquette left right →
      Formula.curvatureBracketValue environment background state plaquette left right
      ≤ Formula.uniformMajorant
          (Formula.radiusAt environment background state)
          (Formula.curvatureLocalCharge environment background state plaquette)

    adjointTransportBound : ∀ background state plaquette left right →
      Formula.curvatureTransportValue environment background state plaquette left right
      ≤ Formula.uniformMajorant
          (Formula.radiusAt environment background state)
          (Formula.curvatureLocalCharge environment background state plaquette)

    forwardDifferenceBound : ∀ background state edge axis →
      Formula.normSquared (Formula.edgeForward environment background state edge axis)
      ≤ Formula.uniformMajorant
          (Formula.radiusAt environment background state)
          (Formula.transportLocalCharge environment background state edge)

    backwardDifferenceBound : ∀ background state edge axis →
      Formula.normSquared (Formula.edgeBackward environment background state edge axis)
      ≤ Formula.uniformMajorant
          (Formula.radiusAt environment background state)
          (Formula.transportLocalCharge environment background state edge)

    chartAxisBound : ∀ background state link →
      Formula.chartValue environment background state link Fixed.chartAxis
      ≤ Formula.uniformMajorant
          (Formula.radiusAt environment background state)
          (Formula.chartLocalCharge environment background state link)

    chartPerpendicular0Bound : ∀ background state link →
      Formula.chartValue environment background state link Fixed.chartPerpendicular0
      ≤ Formula.uniformMajorant
          (Formula.radiusAt environment background state)
          (Formula.chartLocalCharge environment background state link)

    chartPerpendicular1Bound : ∀ background state link →
      Formula.chartValue environment background state link Fixed.chartPerpendicular1
      ≤ Formula.uniformMajorant
          (Formula.radiusAt environment background state)
          (Formula.chartLocalCharge environment background state link)

    chartSkewBound : ∀ background state link →
      Formula.chartValue environment background state link Fixed.chartSkew
      ≤ Formula.uniformMajorant
          (Formula.radiusAt environment background state)
          (Formula.chartLocalCharge environment background state link)

    gaugeIncomingBound : ∀ background state site axis →
      Formula.gaugeIncomingValue environment background state site axis
      ≤ Formula.uniformMajorant
          (Formula.radiusAt environment background state)
          (Formula.gaugeLocalCharge environment background state site)

    gaugeOutgoingBound : ∀ background state site axis →
      Formula.gaugeOutgoingValue environment background state site axis
      ≤ Formula.uniformMajorant
          (Formula.radiusAt environment background state)
          (Formula.gaugeLocalCharge environment background state site)

    gaugeCrossBound : ∀ background state site axis →
      Formula.gaugeCrossValue environment background state site axis
      ≤ Formula.uniformMajorant
          (Formula.radiusAt environment background state)
          (Formula.gaugeLocalCharge environment background state site)

    gaugeSquareBound : ∀ background state site axis →
      Formula.gaugeSquareValue environment background state site axis
      ≤ Formula.uniformMajorant
          (Formula.radiusAt environment background state)
          (Formula.gaugeLocalCharge environment background state site)

    blockPathTelescopingBound : ∀ background state block first second →
      Formula.dot (Formula.blockReferenceDerivative environment state block)
        (Formula.blockPathError environment background state block first second)
      ≤ Formula.uniformMajorant
          (Formula.radiusAt environment background state)
          (Formula.constraintLocalCharge environment background state block)

open MechanismAtomBounds public

curvatureAtomBound :
  ∀ {Background State Plaquette Edge Link Site Block environment} →
  MechanismAtomBounds
    {Background} {State} {Plaquette} {Edge} {Link} {Site} {Block} environment →
  ∀ background state plaquette atom →
  Formula.curvatureValue environment background state plaquette atom
  ≤ Formula.uniformMajorant
      (Formula.radiusAt environment background state)
      (Formula.curvatureLocalCharge environment background state plaquette)
curvatureAtomBound mechanisms background state plaquette Fixed.curvatureBracket01 = bracketBound mechanisms background state plaquette Jet.link0 Jet.link1
curvatureAtomBound mechanisms background state plaquette Fixed.curvatureBracket02 = bracketBound mechanisms background state plaquette Jet.link0 Jet.link2
curvatureAtomBound mechanisms background state plaquette Fixed.curvatureBracket03 = bracketBound mechanisms background state plaquette Jet.link0 Jet.link3
curvatureAtomBound mechanisms background state plaquette Fixed.curvatureBracket12 = bracketBound mechanisms background state plaquette Jet.link1 Jet.link2
curvatureAtomBound mechanisms background state plaquette Fixed.curvatureBracket13 = bracketBound mechanisms background state plaquette Jet.link1 Jet.link3
curvatureAtomBound mechanisms background state plaquette Fixed.curvatureBracket23 = bracketBound mechanisms background state plaquette Jet.link2 Jet.link3
curvatureAtomBound mechanisms background state plaquette Fixed.curvatureTransport01 = adjointTransportBound mechanisms background state plaquette Jet.link0 Jet.link1
curvatureAtomBound mechanisms background state plaquette Fixed.curvatureTransport02 = adjointTransportBound mechanisms background state plaquette Jet.link0 Jet.link2
curvatureAtomBound mechanisms background state plaquette Fixed.curvatureTransport03 = adjointTransportBound mechanisms background state plaquette Jet.link0 Jet.link3
curvatureAtomBound mechanisms background state plaquette Fixed.curvatureTransport10 = adjointTransportBound mechanisms background state plaquette Jet.link1 Jet.link0
curvatureAtomBound mechanisms background state plaquette Fixed.curvatureTransport12 = adjointTransportBound mechanisms background state plaquette Jet.link1 Jet.link2
curvatureAtomBound mechanisms background state plaquette Fixed.curvatureTransport13 = adjointTransportBound mechanisms background state plaquette Jet.link1 Jet.link3
curvatureAtomBound mechanisms background state plaquette Fixed.curvatureTransport20 = adjointTransportBound mechanisms background state plaquette Jet.link2 Jet.link0
curvatureAtomBound mechanisms background state plaquette Fixed.curvatureTransport21 = adjointTransportBound mechanisms background state plaquette Jet.link2 Jet.link1
curvatureAtomBound mechanisms background state plaquette Fixed.curvatureTransport23 = adjointTransportBound mechanisms background state plaquette Jet.link2 Jet.link3
curvatureAtomBound mechanisms background state plaquette Fixed.curvatureTransport30 = adjointTransportBound mechanisms background state plaquette Jet.link3 Jet.link0
curvatureAtomBound mechanisms background state plaquette Fixed.curvatureTransport31 = adjointTransportBound mechanisms background state plaquette Jet.link3 Jet.link1
curvatureAtomBound mechanisms background state plaquette Fixed.curvatureTransport32 = adjointTransportBound mechanisms background state plaquette Jet.link3 Jet.link2

transportAtomBound :
  ∀ {Background State Plaquette Edge Link Site Block environment} →
  MechanismAtomBounds
    {Background} {State} {Plaquette} {Edge} {Link} {Site} {Block} environment →
  ∀ background state edge atom →
  Formula.transportValue environment background state edge atom
  ≤ Formula.uniformMajorant
      (Formula.radiusAt environment background state)
      (Formula.transportLocalCharge environment background state edge)
transportAtomBound mechanisms background state edge Fixed.transportForward0 = forwardDifferenceBound mechanisms background state edge Jet.link0
transportAtomBound mechanisms background state edge Fixed.transportBackward0 = backwardDifferenceBound mechanisms background state edge Jet.link0
transportAtomBound mechanisms background state edge Fixed.transportForward1 = forwardDifferenceBound mechanisms background state edge Jet.link1
transportAtomBound mechanisms background state edge Fixed.transportBackward1 = backwardDifferenceBound mechanisms background state edge Jet.link1
transportAtomBound mechanisms background state edge Fixed.transportForward2 = forwardDifferenceBound mechanisms background state edge Jet.link2
transportAtomBound mechanisms background state edge Fixed.transportBackward2 = backwardDifferenceBound mechanisms background state edge Jet.link2
transportAtomBound mechanisms background state edge Fixed.transportForward3 = forwardDifferenceBound mechanisms background state edge Jet.link3
transportAtomBound mechanisms background state edge Fixed.transportBackward3 = backwardDifferenceBound mechanisms background state edge Jet.link3

chartAtomBound :
  ∀ {Background State Plaquette Edge Link Site Block environment} →
  MechanismAtomBounds
    {Background} {State} {Plaquette} {Edge} {Link} {Site} {Block} environment →
  ∀ background state link atom →
  Formula.chartValue environment background state link atom
  ≤ Formula.uniformMajorant
      (Formula.radiusAt environment background state)
      (Formula.chartLocalCharge environment background state link)
chartAtomBound mechanisms background state link Fixed.chartAxis = chartAxisBound mechanisms background state link
chartAtomBound mechanisms background state link Fixed.chartPerpendicular0 = chartPerpendicular0Bound mechanisms background state link
chartAtomBound mechanisms background state link Fixed.chartPerpendicular1 = chartPerpendicular1Bound mechanisms background state link
chartAtomBound mechanisms background state link Fixed.chartSkew = chartSkewBound mechanisms background state link

record ExpansionAndFiniteSumReceipts
    {Background State Plaquette Edge Link Site Block : Set}
    (environment :
      Formula.LiteralFixedAtomEnvironment
        Background State Plaquette Edge Link Site Block) : Set₁ where
  field
    curvatureExpansionExact : ∀ background state plaquette →
      Formula.curvatureLocalRemainder environment background state plaquette
      ≡ Pointwise.sumℚ
          (Fixed.map (Formula.curvatureValue environment background state plaquette) Fixed.curvatureAtoms)
    transportExpansionExact : ∀ background state edge →
      Formula.transportLocalRemainder environment background state edge
      ≡ Pointwise.sumℚ
          (Fixed.map (Formula.transportValue environment background state edge) Fixed.transportAtoms)
    chartExpansionExact : ∀ background state link →
      Formula.chartLocalRemainder environment background state link
      ≡ Pointwise.sumℚ
          (Fixed.map (Formula.chartValue environment background state link) Fixed.chartAtoms)
    gaugeExpansionExact : ∀ background state site → Set
    constraintExpansionExact : ∀ background state block → Set

    curvatureFiniteSumBelow32 : ∀ background state plaquette → Set
    transportFiniteSumBelow64 : ∀ background state edge → Set
    chartFiniteSumBelow32 : ∀ background state link → Set
    gaugeFiniteSumBelow64 : ∀ background state site → Set
    constraintFiniteSumBelow64 : ∀ background state block → Set

    derivativeFormulaAgreement : Set

open ExpansionAndFiniteSumReceipts public

mechanismAtomEnumerationLevel : ProofLevel
mechanismAtomEnumerationLevel = machineChecked

mechanismInequalityInputsLevel : ProofLevel
mechanismInequalityInputsLevel = conditional

fixedExpansionReceiptInputsLevel : ProofLevel
fixedExpansionReceiptInputsLevel = conditional
