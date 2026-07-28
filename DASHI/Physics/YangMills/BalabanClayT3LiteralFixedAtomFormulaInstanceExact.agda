module DASHI.Physics.YangMills.BalabanClayT3LiteralFixedAtomFormulaInstanceExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ; _+_; _-_; _*_; -_; _≤_)

import DASHI.Physics.YangMills.BalabanClayT2GeneratedQuaternionJetExact as Jet
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredFiniteAtomListsExact as Fixed
import DASHI.Physics.YangMills.BalabanClayT3LiteralPointwiseHessianEstimatesExact as Pointwise
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literal rational coordinate formulas for the five fixed atom lists.
--
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- The papers motivate the local expansions.  The coordinate formulas and the
-- fixed assignment of every tag below are DASHI-owned.  A physical instance now
-- proves that its Wilson/block-map derivatives equal these explicit expressions;
-- it can no longer choose arbitrary atom values.
------------------------------------------------------------------------

record Vec3ℚ : Set where
  constructor vec3
  field
    x y z : ℚ

open Vec3ℚ public

dot : Vec3ℚ → Vec3ℚ → ℚ
dot (vec3 ax ay az) (vec3 bx by bz) =
  ax * bx + ay * by + az * bz

cross : Vec3ℚ → Vec3ℚ → Vec3ℚ
cross (vec3 ax ay az) (vec3 bx by bz) = vec3
  (ay * bz - az * by)
  (az * bx - ax * bz)
  (ax * by - ay * bx)

scale : ℚ → Vec3ℚ → Vec3ℚ
scale coefficient (vec3 ax ay az) =
  vec3 (coefficient * ax) (coefficient * ay) (coefficient * az)

addVec : Vec3ℚ → Vec3ℚ → Vec3ℚ
addVec (vec3 ax ay az) (vec3 bx by bz) =
  vec3 (ax + bx) (ay + by) (az + bz)

negVec : Vec3ℚ → Vec3ℚ
negVec (vec3 ax ay az) = vec3 (- ax) (- ay) (- az)

normSquared : Vec3ℚ → ℚ
normSquared vector = dot vector vector

link0 link1 link2 link3 : Jet.Link4
link0 = Jet.link0
link1 = Jet.link1
link2 = Jet.link2
link3 = Jet.link3

record LiteralFixedAtomEnvironment
    (Background State Plaquette Edge Link Site Block : Set) : Set₁ where
  field
    radiusAt : Background → State → ℚ

    plaquetteBackground : Background → Plaquette → Jet.Link4 → Vec3ℚ
    plaquetteFluctuation : State → Plaquette → Jet.Link4 → Vec3ℚ
    plaquetteTransportDefect :
      Background → State → Plaquette → Jet.Link4 → Jet.Link4 → Vec3ℚ

    edgeForward edgeBackward :
      Background → State → Edge → Jet.Link4 → Vec3ℚ

    linkFluctuation : State → Link → Vec3ℚ
    chartAxisCoefficient chartPerpendicularCoefficient chartSkewCoefficient :
      Background → Link → ℚ

    siteIncoming siteOutgoing :
      Background → State → Site → Jet.Link4 → Vec3ℚ
    siteReferenceDivergence : State → Site → Vec3ℚ

    blockReferenceDerivative : State → Block → Vec3ℚ
    blockPathError :
      Background → State → Block → Jet.Link4 → Jet.Link4 → Vec3ℚ

    curvatureLocalRemainder : Background → State → Plaquette → ℚ
    transportLocalRemainder : Background → State → Edge → ℚ
    chartLocalRemainder : Background → State → Link → ℚ
    gaugeLocalRemainder : Background → State → Site → ℚ
    constraintLocalRemainder : Background → State → Block → ℚ

    curvatureLocalCharge : Background → State → Plaquette → ℚ
    transportLocalCharge : Background → State → Edge → ℚ
    chartLocalCharge : Background → State → Link → ℚ
    gaugeLocalCharge : Background → State → Site → ℚ
    constraintLocalCharge : Background → State → Block → ℚ

open LiteralFixedAtomEnvironment public

curvatureBracketValue :
  ∀ {Background State Plaquette Edge Link Site Block} →
  LiteralFixedAtomEnvironment Background State Plaquette Edge Link Site Block →
  Background → State → Plaquette → Jet.Link4 → Jet.Link4 → ℚ
curvatureBracketValue environment background state plaquette left right =
  dot
    (plaquetteFluctuation environment state plaquette left)
    (cross
      (plaquetteBackground environment background plaquette left)
      (plaquetteFluctuation environment state plaquette right))

curvatureTransportValue :
  ∀ {Background State Plaquette Edge Link Site Block} →
  LiteralFixedAtomEnvironment Background State Plaquette Edge Link Site Block →
  Background → State → Plaquette → Jet.Link4 → Jet.Link4 → ℚ
curvatureTransportValue environment background state plaquette left right =
  dot
    (plaquetteFluctuation environment state plaquette left)
    (plaquetteTransportDefect environment background state plaquette left right)

curvatureValue :
  ∀ {Background State Plaquette Edge Link Site Block} →
  LiteralFixedAtomEnvironment Background State Plaquette Edge Link Site Block →
  Background → State → Plaquette → Fixed.CurvatureAtom → ℚ
curvatureValue e b h p Fixed.curvatureBracket01 = curvatureBracketValue e b h p link0 link1
curvatureValue e b h p Fixed.curvatureBracket02 = curvatureBracketValue e b h p link0 link2
curvatureValue e b h p Fixed.curvatureBracket03 = curvatureBracketValue e b h p link0 link3
curvatureValue e b h p Fixed.curvatureBracket12 = curvatureBracketValue e b h p link1 link2
curvatureValue e b h p Fixed.curvatureBracket13 = curvatureBracketValue e b h p link1 link3
curvatureValue e b h p Fixed.curvatureBracket23 = curvatureBracketValue e b h p link2 link3
curvatureValue e b h p Fixed.curvatureTransport01 = curvatureTransportValue e b h p link0 link1
curvatureValue e b h p Fixed.curvatureTransport02 = curvatureTransportValue e b h p link0 link2
curvatureValue e b h p Fixed.curvatureTransport03 = curvatureTransportValue e b h p link0 link3
curvatureValue e b h p Fixed.curvatureTransport10 = curvatureTransportValue e b h p link1 link0
curvatureValue e b h p Fixed.curvatureTransport12 = curvatureTransportValue e b h p link1 link2
curvatureValue e b h p Fixed.curvatureTransport13 = curvatureTransportValue e b h p link1 link3
curvatureValue e b h p Fixed.curvatureTransport20 = curvatureTransportValue e b h p link2 link0
curvatureValue e b h p Fixed.curvatureTransport21 = curvatureTransportValue e b h p link2 link1
curvatureValue e b h p Fixed.curvatureTransport23 = curvatureTransportValue e b h p link2 link3
curvatureValue e b h p Fixed.curvatureTransport30 = curvatureTransportValue e b h p link3 link0
curvatureValue e b h p Fixed.curvatureTransport31 = curvatureTransportValue e b h p link3 link1
curvatureValue e b h p Fixed.curvatureTransport32 = curvatureTransportValue e b h p link3 link2

transportValue :
  ∀ {Background State Plaquette Edge Link Site Block} →
  LiteralFixedAtomEnvironment Background State Plaquette Edge Link Site Block →
  Background → State → Edge → Fixed.TransportAtom → ℚ
transportValue e b h edge Fixed.transportForward0 = normSquared (edgeForward e b h edge link0)
transportValue e b h edge Fixed.transportBackward0 = normSquared (edgeBackward e b h edge link0)
transportValue e b h edge Fixed.transportForward1 = normSquared (edgeForward e b h edge link1)
transportValue e b h edge Fixed.transportBackward1 = normSquared (edgeBackward e b h edge link1)
transportValue e b h edge Fixed.transportForward2 = normSquared (edgeForward e b h edge link2)
transportValue e b h edge Fixed.transportBackward2 = normSquared (edgeBackward e b h edge link2)
transportValue e b h edge Fixed.transportForward3 = normSquared (edgeForward e b h edge link3)
transportValue e b h edge Fixed.transportBackward3 = normSquared (edgeBackward e b h edge link3)

chartValue :
  ∀ {Background State Plaquette Edge Link Site Block} →
  LiteralFixedAtomEnvironment Background State Plaquette Edge Link Site Block →
  Background → State → Link → Fixed.ChartAtom → ℚ
chartValue e b h link Fixed.chartAxis =
  chartAxisCoefficient e b link * normSquared (linkFluctuation e h link)
chartValue e b h link Fixed.chartPerpendicular0 =
  chartPerpendicularCoefficient e b link *
    (x (linkFluctuation e h link) * x (linkFluctuation e h link))
chartValue e b h link Fixed.chartPerpendicular1 =
  chartPerpendicularCoefficient e b link *
    (y (linkFluctuation e h link) * y (linkFluctuation e h link) +
     z (linkFluctuation e h link) * z (linkFluctuation e h link))
chartValue e b h link Fixed.chartSkew =
  chartSkewCoefficient e b link *
    dot (linkFluctuation e h link)
      (cross (linkFluctuation e h link) (linkFluctuation e h link))

gaugeIncomingValue :
  ∀ {Background State Plaquette Edge Link Site Block} →
  LiteralFixedAtomEnvironment Background State Plaquette Edge Link Site Block →
  Background → State → Site → Jet.Link4 → ℚ
gaugeIncomingValue e b h site axis = normSquared (siteIncoming e b h site axis)

gaugeOutgoingValue :
  ∀ {Background State Plaquette Edge Link Site Block} →
  LiteralFixedAtomEnvironment Background State Plaquette Edge Link Site Block →
  Background → State → Site → Jet.Link4 → ℚ
gaugeOutgoingValue e b h site axis = normSquared (siteOutgoing e b h site axis)

gaugeCrossValue :
  ∀ {Background State Plaquette Edge Link Site Block} →
  LiteralFixedAtomEnvironment Background State Plaquette Edge Link Site Block →
  Background → State → Site → Jet.Link4 → ℚ
gaugeCrossValue e b h site axis =
  dot (siteReferenceDivergence e h site)
    (addVec (siteIncoming e b h site axis) (siteOutgoing e b h site axis))

gaugeSquareValue :
  ∀ {Background State Plaquette Edge Link Site Block} →
  LiteralFixedAtomEnvironment Background State Plaquette Edge Link Site Block →
  Background → State → Site → Jet.Link4 → ℚ
gaugeSquareValue e b h site axis =
  normSquared (addVec (siteIncoming e b h site axis) (siteOutgoing e b h site axis))

gaugeValue :
  ∀ {Background State Plaquette Edge Link Site Block} →
  LiteralFixedAtomEnvironment Background State Plaquette Edge Link Site Block →
  Background → State → Site → Fixed.GaugeAtom → ℚ
gaugeValue e b h s Fixed.gaugeIncoming0 = gaugeIncomingValue e b h s link0
gaugeValue e b h s Fixed.gaugeOutgoing0 = gaugeOutgoingValue e b h s link0
gaugeValue e b h s Fixed.gaugeIncoming1 = gaugeIncomingValue e b h s link1
gaugeValue e b h s Fixed.gaugeOutgoing1 = gaugeOutgoingValue e b h s link1
gaugeValue e b h s Fixed.gaugeIncoming2 = gaugeIncomingValue e b h s link2
gaugeValue e b h s Fixed.gaugeOutgoing2 = gaugeOutgoingValue e b h s link2
gaugeValue e b h s Fixed.gaugeIncoming3 = gaugeIncomingValue e b h s link3
gaugeValue e b h s Fixed.gaugeOutgoing3 = gaugeOutgoingValue e b h s link3
gaugeValue e b h s Fixed.gaugeCross0 = gaugeCrossValue e b h s link0
gaugeValue e b h s Fixed.gaugeCross1 = gaugeCrossValue e b h s link1
gaugeValue e b h s Fixed.gaugeCross2 = gaugeCrossValue e b h s link2
gaugeValue e b h s Fixed.gaugeCross3 = gaugeCrossValue e b h s link3
gaugeValue e b h s Fixed.gaugeSquare0 = gaugeSquareValue e b h s link0
gaugeValue e b h s Fixed.gaugeSquare1 = gaugeSquareValue e b h s link1
gaugeValue e b h s Fixed.gaugeSquare2 = gaugeSquareValue e b h s link2
gaugeValue e b h s Fixed.gaugeSquare3 = gaugeSquareValue e b h s link3

constraintPath : Fixed.ConstraintAtom → Jet.Link4 × Jet.Link4
constraintPath Fixed.blockPath0Step0 = link0 , link0
constraintPath Fixed.blockPath0Step1 = link0 , link1
constraintPath Fixed.blockPath0Step2 = link0 , link2
constraintPath Fixed.blockPath0Step3 = link0 , link3
constraintPath Fixed.blockPath1Step0 = link1 , link0
constraintPath Fixed.blockPath1Step1 = link1 , link1
constraintPath Fixed.blockPath1Step2 = link1 , link2
constraintPath Fixed.blockPath1Step3 = link1 , link3
constraintPath Fixed.blockPath2Step0 = link2 , link0
constraintPath Fixed.blockPath2Step1 = link2 , link1
constraintPath Fixed.blockPath2Step2 = link2 , link2
constraintPath Fixed.blockPath2Step3 = link2 , link3
constraintPath Fixed.blockPath3Step0 = link3 , link0
constraintPath Fixed.blockPath3Step1 = link3 , link1
constraintPath Fixed.blockPath3Step2 = link3 , link2
constraintPath Fixed.blockPath3Step3 = link3 , link3

constraintValue :
  ∀ {Background State Plaquette Edge Link Site Block} →
  LiteralFixedAtomEnvironment Background State Plaquette Edge Link Site Block →
  Background → State → Block → Fixed.ConstraintAtom → ℚ
constraintValue e b h block atom =
  dot (blockReferenceDerivative e h block)
    (blockPathError e b h block
      (proj₁ (constraintPath atom)) (proj₂ (constraintPath atom)))

uniformMajorant : ℚ → ℚ → ℚ
uniformMajorant radius charge = radius * charge

record LiteralFixedAtomProofs
    {Background State Plaquette Edge Link Site Block : Set}
    (environment :
      LiteralFixedAtomEnvironment
        Background State Plaquette Edge Link Site Block) : Set₁ where
  field
    curvatureAtomBound : ∀ background state plaquette atom →
      curvatureValue environment background state plaquette atom
      ≤ uniformMajorant (radiusAt environment background state)
          (curvatureLocalCharge environment background state plaquette)

    transportAtomBound : ∀ background state edge atom →
      transportValue environment background state edge atom
      ≤ uniformMajorant (radiusAt environment background state)
          (transportLocalCharge environment background state edge)

    chartAtomBound : ∀ background state link atom →
      chartValue environment background state link atom
      ≤ uniformMajorant (radiusAt environment background state)
          (chartLocalCharge environment background state link)

    gaugeAtomBound : ∀ background state site atom →
      gaugeValue environment background state site atom
      ≤ uniformMajorant (radiusAt environment background state)
          (gaugeLocalCharge environment background state site)

    constraintAtomBound : ∀ background state block atom →
      constraintValue environment background state block atom
      ≤ uniformMajorant (radiusAt environment background state)
          (constraintLocalCharge environment background state block)

    curvatureExpansionExact : ∀ background state plaquette →
      curvatureLocalRemainder environment background state plaquette
      ≡ Pointwise.sumℚ
          (Fixed.map
            (curvatureValue environment background state plaquette)
            Fixed.curvatureAtoms)

    transportExpansionExact : ∀ background state edge →
      transportLocalRemainder environment background state edge
      ≡ Pointwise.sumℚ
          (Fixed.map
            (transportValue environment background state edge)
            Fixed.transportAtoms)

    chartExpansionExact : ∀ background state link →
      chartLocalRemainder environment background state link
      ≡ Pointwise.sumℚ
          (Fixed.map
            (chartValue environment background state link)
            Fixed.chartAtoms)

    gaugeExpansionExact : ∀ background state site →
      gaugeLocalRemainder environment background state site
      ≡ Pointwise.sumℚ
          (Fixed.map
            (gaugeValue environment background state site)
            Fixed.gaugeAtoms)

    constraintExpansionExact : ∀ background state block →
      constraintLocalRemainder environment background state block
      ≡ Pointwise.sumℚ
          (Fixed.map
            (constraintValue environment background state block)
            Fixed.constraintAtoms)

    curvatureFiniteSumBelow32 : ∀ background state plaquette → Set
    transportFiniteSumBelow64 : ∀ background state edge → Set
    chartFiniteSumBelow32 : ∀ background state link → Set
    gaugeFiniteSumBelow64 : ∀ background state site → Set
    constraintFiniteSumBelow64 : ∀ background state block → Set

    wilsonPlaquetteSecondVariationAtBackgroundExact :
      ∀ background state plaquette → Set
    wilsonPlaquetteSecondVariationAtIdentityExact : ∀ state plaquette → Set
    plaquetteCurvatureDifferenceIsFixedAtomSum :
      ∀ background state plaquette → Set

    covariantForwardDifferenceIsFixedAtomSum :
      ∀ background state edge → Set
    inverseRightJacobianMetricIsFixedAtomSum :
      ∀ background link → Set
    covariantDivergenceDifferenceIsFixedAtomSum :
      ∀ background state site → Set
    nonlinearBlockDerivativeIsFixedAtomSum :
      ∀ background state block → Set

open LiteralFixedAtomProofs public

literalFixedAtomFormulaLevel : ProofLevel
literalFixedAtomFormulaLevel = machineChecked

literalFixedAtomEnumerationLevel : ProofLevel
literalFixedAtomEnumerationLevel = machineChecked

literalFixedAtomInequalityInputsLevel : ProofLevel
literalFixedAtomInequalityInputsLevel = conditional
