module DASHI.Physics.Foundations.FiniteGraphGaugeScalarExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Exact Z2 gauge group.

data Z2Gauge : Set where
  gaugePlus : Z2Gauge
  gaugeMinus : Z2Gauge

infixl 30 _*g_

_*g_ : Z2Gauge → Z2Gauge → Z2Gauge
gaugePlus *g g = g
gaugeMinus *g gaugePlus = gaugeMinus
gaugeMinus *g gaugeMinus = gaugePlus

inverseGauge : Z2Gauge → Z2Gauge
inverseGauge gaugePlus = gaugePlus
inverseGauge gaugeMinus = gaugeMinus

leftIdentityGauge : (g : Z2Gauge) → gaugePlus *g g ≡ g
leftIdentityGauge gaugePlus = refl
leftIdentityGauge gaugeMinus = refl

rightIdentityGauge : (g : Z2Gauge) → g *g gaugePlus ≡ g
rightIdentityGauge gaugePlus = refl
rightIdentityGauge gaugeMinus = refl

selfInverseGauge : (g : Z2Gauge) → inverseGauge g *g g ≡ gaugePlus
selfInverseGauge gaugePlus = refl
selfInverseGauge gaugeMinus = refl

associativeGauge :
  (a b c : Z2Gauge) →
  (a *g b) *g c ≡ a *g (b *g c)
associativeGauge gaugePlus gaugePlus gaugePlus = refl
associativeGauge gaugePlus gaugePlus gaugeMinus = refl
associativeGauge gaugePlus gaugeMinus gaugePlus = refl
associativeGauge gaugePlus gaugeMinus gaugeMinus = refl
associativeGauge gaugeMinus gaugePlus gaugePlus = refl
associativeGauge gaugeMinus gaugePlus gaugeMinus = refl
associativeGauge gaugeMinus gaugeMinus gaugePlus = refl
associativeGauge gaugeMinus gaugeMinus gaugeMinus = refl

------------------------------------------------------------------------
-- Triangle connection and local gauge transformation.

data Vertex3 : Set where
  vertex0 : Vertex3
  vertex1 : Vertex3
  vertex2 : Vertex3

data Edge3 : Set where
  edge01 : Edge3
  edge12 : Edge3
  edge20 : Edge3

source : Edge3 → Vertex3
source edge01 = vertex0
source edge12 = vertex1
source edge20 = vertex2

target : Edge3 → Vertex3
target edge01 = vertex1
target edge12 = vertex2
target edge20 = vertex0

Connection : Set
Connection = Edge3 → Z2Gauge

GaugeTransformation : Set
GaugeTransformation = Vertex3 → Z2Gauge

canonicalConnection : Connection
canonicalConnection edge01 = gaugeMinus
canonicalConnection edge12 = gaugePlus
canonicalConnection edge20 = gaugePlus

canonicalLocalGauge : GaugeTransformation
canonicalLocalGauge vertex0 = gaugeMinus
canonicalLocalGauge vertex1 = gaugePlus
canonicalLocalGauge vertex2 = gaugeMinus

transformEdge :
  GaugeTransformation → Connection → Edge3 → Z2Gauge
transformEdge g connection edge =
  g (source edge)
  *g
  connection edge
  *g
  inverseGauge (g (target edge))

transformedConnection : Connection
transformedConnection = transformEdge canonicalLocalGauge canonicalConnection

loopHolonomy : Connection → Z2Gauge
loopHolonomy connection =
  connection edge01 *g connection edge12 *g connection edge20

canonicalLoopHolonomyIsMinus :
  loopHolonomy canonicalConnection ≡ gaugeMinus
canonicalLoopHolonomyIsMinus = refl

transformedLoopHolonomyIsMinus :
  loopHolonomy transformedConnection ≡ gaugeMinus
transformedLoopHolonomyIsMinus = refl

loopHolonomyGaugeInvariantInCanonicalCase :
  loopHolonomy transformedConnection
  ≡
  loopHolonomy canonicalConnection
loopHolonomyGaugeInvariantInCanonicalCase = refl

------------------------------------------------------------------------
-- Covariant scalar mismatch on one edge.

data ScalarSign : Set where
  scalarPlus : ScalarSign
  scalarMinus : ScalarSign

actOnScalar : Z2Gauge → ScalarSign → ScalarSign
actOnScalar gaugePlus scalar = scalar
actOnScalar gaugeMinus scalarPlus = scalarMinus
actOnScalar gaugeMinus scalarMinus = scalarPlus

transportScalar : Z2Gauge → ScalarSign → ScalarSign
transportScalar = actOnScalar

mismatch : ScalarSign → ScalarSign → Bool
mismatch scalarPlus scalarPlus = false
mismatch scalarMinus scalarMinus = false
mismatch scalarPlus scalarMinus = true
mismatch scalarMinus scalarPlus = true

canonicalField : Vertex3 → ScalarSign
canonicalField vertex0 = scalarPlus
canonicalField vertex1 = scalarMinus
canonicalField vertex2 = scalarMinus

transformField :
  GaugeTransformation → (Vertex3 → ScalarSign) → Vertex3 → ScalarSign
transformField g field vertex = actOnScalar (g vertex) (field vertex)

edgeMismatch :
  Connection → (Vertex3 → ScalarSign) → Edge3 → Bool
edgeMismatch connection field edge =
  mismatch
    (transportScalar (connection edge) (field (source edge)))
    (field (target edge))

canonicalEdge01IsCovariantlyMatched :
  edgeMismatch canonicalConnection canonicalField edge01 ≡ false
canonicalEdge01IsCovariantlyMatched = refl

transformedEdge01RemainsCovariantlyMatched :
  edgeMismatch
    transformedConnection
    (transformField canonicalLocalGauge canonicalField)
    edge01
  ≡
  false
transformedEdge01RemainsCovariantlyMatched = refl

record FiniteGraphGaugeBoundary : Set where
  constructor finiteGraphGaugeBoundary
  field
    localZ2GaugeModelIsContinuumYangMills : Bool
    localZ2GaugeModelIsContinuumYangMillsIsFalse :
      localZ2GaugeModelIsContinuumYangMills ≡ false

    oneFiniteCovarianceWitnessProvesStandardModelGaugeContent : Bool
    oneFiniteCovarianceWitnessProvesStandardModelGaugeContentIsFalse :
      oneFiniteCovarianceWitnessProvesStandardModelGaugeContent ≡ false

    graphScalarSignIsACompletedRelativisticScalarField : Bool
    graphScalarSignIsACompletedRelativisticScalarFieldIsFalse :
      graphScalarSignIsACompletedRelativisticScalarField ≡ false

open FiniteGraphGaugeBoundary public

canonicalFiniteGraphGaugeBoundary : FiniteGraphGaugeBoundary
canonicalFiniteGraphGaugeBoundary =
  finiteGraphGaugeBoundary false refl false refl false refl
