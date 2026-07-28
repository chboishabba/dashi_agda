module DASHI.Physics.YangMills.BalabanClayT3LiteralFixedAtomFormulaInstanceExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _*_; -_; _≤_; _/_)

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

curvatureValue :
  ∀ {Background State Plaquette Edge Link Site Block} →
  LiteralFixedAtomEnvironment Background State Plaquette Edge Link Site Block →
  Background → State → Plaquette → Fixed.CurvatureAtom → ℚ
curvatureValue environment background state plaquette atom =
  let
    A = plaquetteBackground environment background plaquette
    h = plaquetteFluctuation environment state plaquette
    T = plaquetteTransportDefect environment background state plaquette
  in
  case atom of λ where
    Fixed.curvatureBracket01 → dot (h link0) (cross (A link0) (h link1))
    Fixed.curvatureBracket02 → dot (h link0) (cross (A link0) (h link2))
    Fixed.curvatureBracket03 → dot (h link0) (cross (A link0) (h link3))
    Fixed.curvatureBracket12 → dot (h link1) (cross (A link1) (h link2))
    Fixed.curvatureBracket13 → dot (h link1) (cross (A link1) (h link3))
    Fixed.curvatureBracket23 → dot (h link2) (cross (A link2) (h link3))
    Fixed.curvatureTransport01 → dot (h link0) (T link0 link1)
    Fixed.curvatureTransport02 → dot (h link0) (T link0 link2)
    Fixed.curvatureTransport03 → dot (h link0) (T link0 link3)
    Fixed.curvatureTransport10 → dot (h link1) (T link1 link0)
    Fixed.curvatureTransport12 → dot (h link1) (T link1 link2)
    Fixed.curvatureTransport13 → dot (h link1) (T link1 link3)
    Fixed.curvatureTransport20 → dot (h link2) (T link2 link0)
    Fixed.curvatureTransport21 → dot (h link2) (T link2 link1)
    Fixed.curvatureTransport23 → dot (h link2) (T link2 link3)
    Fixed.curvatureTransport30 → dot (h link3) (T link3 link0)
    Fixed.curvatureTransport31 → dot (h link3) (T link3 link1)
    Fixed.curvatureTransport32 → dot (h link3) (T link3 link2)
  where
  case : ∀ {A B : Set} → A → (A → B) → B
  case value branch = branch value

transportValue :
  ∀ {Background State Plaquette Edge Link Site Block} →
  LiteralFixedAtomEnvironment Background State Plaquette Edge Link Site Block →
  Background → State → Edge → Fixed.TransportAtom → ℚ
transportValue environment background state edge atom =
  case atom of λ where
    Fixed.transportForward0 → normSquared (edgeForward environment background state edge link0)
    Fixed.transportBackward0 → normSquared (edgeBackward environment background state edge link0)
    Fixed.transportForward1 → normSquared (edgeForward environment background state edge link1)
    Fixed.transportBackward1 → normSquared (edgeBackward environment background state edge link1)
    Fixed.transportForward2 → normSquared (edgeForward environment background state edge link2)
    Fixed.transportBackward2 → normSquared (edgeBackward environment background state edge link2)
    Fixed.transportForward3 → normSquared (edgeForward environment background state edge link3)
    Fixed.transportBackward3 → normSquared (edgeBackward environment background state edge link3)
  where
  case : ∀ {A B : Set} → A → (A → B) → B
  case value branch = branch value

chartValue :
  ∀ {Background State Plaquette Edge Link Site Block} →
  LiteralFixedAtomEnvironment Background State Plaquette Edge Link Site Block →
  Background → State → Link → Fixed.ChartAtom → ℚ
chartValue environment background state link atom =
  let h = linkFluctuation environment state link in
  case atom of λ where
    Fixed.chartAxis → chartAxisCoefficient environment background link * normSquared h
    Fixed.chartPerpendicular0 →
      chartPerpendicularCoefficient environment background link * (x h * x h)
    Fixed.chartPerpendicular1 →
      chartPerpendicularCoefficient environment background link *
        (y h * y h + z h * z h)
    Fixed.chartSkew → chartSkewCoefficient environment background link * dot h (cross h h)
  where
  case : ∀ {A B : Set} → A → (A → B) → B
  case value branch = branch value

gaugeValue :
  ∀ {Background State Plaquette Edge Link Site Block} →
  LiteralFixedAtomEnvironment Background State Plaquette Edge Link Site Block →
  Background → State → Site → Fixed.GaugeAtom → ℚ
gaugeValue environment background state site atom =
  let
    incoming = siteIncoming environment background state site
    outgoing = siteOutgoing environment background state site
    reference = siteReferenceDivergence environment state site
  in
  case atom of λ where
    Fixed.gaugeIncoming0 → normSquared (incoming link0)
    Fixed.gaugeOutgoing0 → normSquared (outgoing link0)
    Fixed.gaugeIncoming1 → normSquared (incoming link1)
    Fixed.gaugeOutgoing1 → normSquared (outgoing link1)
    Fixed.gaugeIncoming2 → normSquared (incoming link2)
    Fixed.gaugeOutgoing2 → normSquared (outgoing link2)
    Fixed.gaugeIncoming3 → normSquared (incoming link3)
    Fixed.gaugeOutgoing3 → normSquared (outgoing link3)
    Fixed.gaugeCross0 → dot reference (addVec (incoming link0) (outgoing link0))
    Fixed.gaugeCross1 → dot reference (addVec (incoming link1) (outgoing link1))
    Fixed.gaugeCross2 → dot reference (addVec (incoming link2) (outgoing link2))
    Fixed.gaugeCross3 → dot reference (addVec (incoming link3) (outgoing link3))
    Fixed.gaugeSquare0 → normSquared (addVec (incoming link0) (outgoing link0))
    Fixed.gaugeSquare1 → normSquared (addVec (incoming link1) (outgoing link1))
    Fixed.gaugeSquare2 → normSquared (addVec (incoming link2) (outgoing link2))
    Fixed.gaugeSquare3 → normSquared (addVec (incoming link3) (outgoing link3))
  where
  case : ∀ {A B : Set} → A → (A → B) → B
  case value branch = branch value

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
  where open import Data.Product using (_×_; _,_)

constraintValue :
  ∀ {Background State Plaquette Edge Link Site Block} →
  LiteralFixedAtomEnvironment Background State Plaquette Edge Link Site Block →
  Background → State → Block → Fixed.ConstraintAtom → ℚ
constraintValue environment background state block atom =
  let pair = constraintPath atom in
  dot (blockReferenceDerivative environment state block)
    (blockPathError environment background state block
      (Data.Product.proj₁ pair) (Data.Product.proj₂ pair))
  where import Data.Product

------------------------------------------------------------------------
-- Majorants are fixed formulas: radius times a local quadratic charge.  The
-- physical work is proving each coordinate expression is below this majorant.
------------------------------------------------------------------------

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
