module DASHI.Physics.YangMills.BalabanLiteralArbitrarySideWilsonFourthJetExact where

------------------------------------------------------------------------
-- LITERAL ARBITRARY-SIDE WILSON PLAQUETTE FOUR-JET
--
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10
-- (1974), 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
--
-- Martin Lüscher and Peter Weisz, "Background field technique and
-- renormalization in lattice gauge theory", Nuclear Physics B 452 (1995),
-- 213--233. DOI: 10.1016/0550-3213(95)00346-T.
--
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Materialize the Wilson cubic and quartic plaquette coefficients on every
-- finite periodic L^4 carrier.  The previous P33 construction evaluates the
-- same formula on L=4.  Here the *actual* four oriented links, the six
-- plaquette planes, and the complete finite site sum are defined for arbitrary
-- L.  This is the finite-volume object which a Fourier transform may consume;
-- it is not a side-four proxy for the cutoff-uniform beta coefficient.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  ( CyclicIndex; Axis4; PositiveBond; Product; pair; cartesian
  ; periodicTorus4Definition; zeroᵢ; sucᵢ )
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  ( PhysicalBlockL; physicalBlockSites )
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  ( sumRational )
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionCoreExact as Q
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonFourthJetExact as Wilson4
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonLinkExponentialFourthJetExact as Link4

------------------------------------------------------------------------
-- Periodic translation on every nonempty cyclic side.
------------------------------------------------------------------------

cyclicNext : ∀ {n} → CyclicIndex (suc n) → CyclicIndex (suc n)
cyclicNext {zero} zeroᵢ = zeroᵢ
cyclicNext {suc n} zeroᵢ = sucᵢ zeroᵢ
cyclicNext {suc n} (sucᵢ index) with cyclicNext {n} index
... | zeroᵢ = zeroᵢ
... | sucᵢ next = sucᵢ (sucᵢ next)

shiftForward : ∀ {n} → Axis4 → periodicTorus4Definition (suc n) →
  periodicTorus4Definition (suc n)
shiftForward zeroᵢ (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair (cyclicNext x0) x1) (pair x2 x3)
shiftForward (sucᵢ zeroᵢ) (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 (cyclicNext x1)) (pair x2 x3)
shiftForward (sucᵢ (sucᵢ zeroᵢ)) (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair (cyclicNext x2) x3)
shiftForward (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair (pair x0 x1) (pair x2 x3)) =
  pair (pair x0 x1) (pair x2 (cyclicNext x3))

------------------------------------------------------------------------
-- Literal SU(2) fields and the six positive plaquette planes.
------------------------------------------------------------------------

quaternionConjugate : Q.RationalQuaternion → Q.RationalQuaternion
quaternionConjugate (Q.quat a0 a1 a2 a3) = Q.quat a0 (- a1) (- a2) (- a3)

quaternionNormSq : Q.RationalQuaternion → ℚ
quaternionNormSq (Q.quat a0 a1 a2 a3) =
  a0 * a0 + a1 * a1 + a2 * a2 + a3 * a3

record RationalSU2Background (L : Nat) : Set where
  field
    link : PositiveBond L → Q.RationalQuaternion
    unitNorm : ∀ bond → quaternionNormSq (link bond) ≡ 1ℚ
open RationalSU2Background public

inverseLink : ∀ {L} → RationalSU2Background L → PositiveBond L →
  Q.RationalQuaternion
inverseLink background bond = quaternionConjugate (link background bond)

-- This is the same three-coordinate tangent field as the finite physical
-- carrier.  Packaging it here as a pure quaternion keeps the vertex tied to
-- the actual physical coordinate system rather than to an abstract generator.
tangentQuaternion : ∀ {L} → Physical.PhysicalSU2BondField L →
  PhysicalBlockL L → Axis4 → Q.RationalQuaternion
tangentQuaternion field site axis = Q.quat 0ℚ
  (field Physical.coordinateX (pair site axis))
  (field Physical.coordinateY (pair site axis))
  (field Physical.coordinateZ (pair site axis))

data AxisPair6 : Set where
  pair01 pair02 pair03 pair12 pair13 pair23 : AxisPair6

axisPairs6 : List AxisPair6
axisPairs6 = pair01 ∷ pair02 ∷ pair03 ∷ pair12 ∷ pair13 ∷ pair23 ∷ []

pairLeft : AxisPair6 → Axis4
pairLeft pair01 = zeroᵢ
pairLeft pair02 = zeroᵢ
pairLeft pair03 = zeroᵢ
pairLeft pair12 = sucᵢ zeroᵢ
pairLeft pair13 = sucᵢ zeroᵢ
pairLeft pair23 = sucᵢ (sucᵢ zeroᵢ)

pairRight : AxisPair6 → Axis4
pairRight pair01 = sucᵢ zeroᵢ
pairRight pair02 = sucᵢ (sucᵢ zeroᵢ)
pairRight pair03 = sucᵢ (sucᵢ (sucᵢ zeroᵢ))
pairRight pair12 = sucᵢ (sucᵢ zeroᵢ)
pairRight pair13 = sucᵢ (sucᵢ (sucᵢ zeroᵢ))
pairRight pair23 = sucᵢ (sucᵢ (sucᵢ zeroᵢ))

Plaquette : Nat → Set
Plaquette L = Product (PhysicalBlockL L) AxisPair6

plaquettes : (n : Nat) → List (Plaquette (suc n))
plaquettes n = cartesian (physicalBlockSites (suc n)) axisPairs6

------------------------------------------------------------------------
-- The literal four oriented factors and their finite-volume vertices.
------------------------------------------------------------------------

positiveLinkJet4 : ∀ {L} → RationalSU2Background L →
  Physical.PhysicalSU2BondField L → PhysicalBlockL L → Axis4 →
  Wilson4.QuaternionFactorJet4
positiveLinkJet4 background field site axis =
  Link4.positiveLinkExponentialJet4
    (link background (pair site axis))
    (tangentQuaternion field site axis)

inverseLinkJet4 : ∀ {L} → RationalSU2Background L →
  Physical.PhysicalSU2BondField L → PhysicalBlockL L → Axis4 →
  Wilson4.QuaternionFactorJet4
inverseLinkJet4 background field site axis =
  Link4.inverseLinkExponentialJet4
    (inverseLink background (pair site axis))
    (tangentQuaternion field site axis)

plaquetteFourthJet : ∀ {n} → RationalSU2Background (suc n) →
  Physical.PhysicalSU2BondField (suc n) → Plaquette (suc n) →
  Wilson4.LiteralFourLinkWilsonFourthJet
plaquetteFourthJet background field (pair site axes) =
  let
    left = pairLeft axes
    right = pairRight axes
  in
  record
    { Wilson4.link0 = positiveLinkJet4 background field site left
    ; Wilson4.link1 = positiveLinkJet4 background field
        (shiftForward left site) right
    ; Wilson4.link2 = inverseLinkJet4 background field
        (shiftForward right site) left
    ; Wilson4.link3 = inverseLinkJet4 background field site right
    }

plaquetteWilsonCubicCoefficient : ∀ {n} → RationalSU2Background (suc n) →
  Physical.PhysicalSU2BondField (suc n) → Plaquette (suc n) → ℚ
plaquetteWilsonCubicCoefficient background field plaquette =
  Wilson4.wilsonCubicCoefficient (plaquetteFourthJet background field plaquette)

plaquetteWilsonQuarticCoefficient : ∀ {n} → RationalSU2Background (suc n) →
  Physical.PhysicalSU2BondField (suc n) → Plaquette (suc n) → ℚ
plaquetteWilsonQuarticCoefficient background field plaquette =
  Wilson4.wilsonQuarticCoefficient (plaquetteFourthJet background field plaquette)

physicalWilsonCubicVertex : ∀ {n} → RationalSU2Background (suc n) →
  Physical.PhysicalSU2BondField (suc n) → ℚ
physicalWilsonCubicVertex {n} background field =
  sumRational (plaquettes n)
    (plaquetteWilsonCubicCoefficient background field)

physicalWilsonQuarticVertex : ∀ {n} → RationalSU2Background (suc n) →
  Physical.PhysicalSU2BondField (suc n) → ℚ
physicalWilsonQuarticVertex {n} background field =
  sumRational (plaquettes n)
    (plaquetteWilsonQuarticCoefficient background field)

------------------------------------------------------------------------
-- Four-direction polarization of the literal quartic vertex.
--
-- For a homogeneous quartic q, the alternating 16-evaluation formula below
-- is its symmetric four-linear coefficient.  Writing it explicitly prevents
-- a future momentum rule from silently replacing an off-diagonal vertex by a
-- diagonal one.  It is the finite-volume precursor of the mixed two-jet.
------------------------------------------------------------------------

zeroTangent : ∀ {L} → Physical.PhysicalSU2BondField L
zeroTangent coordinate bond = 0ℚ

addTangent : ∀ {L} → Physical.PhysicalSU2BondField L →
  Physical.PhysicalSU2BondField L → Physical.PhysicalSU2BondField L
addTangent left right coordinate bond =
  left coordinate bond + right coordinate bond

sum2Tangent : ∀ {L} → Physical.PhysicalSU2BondField L →
  Physical.PhysicalSU2BondField L → Physical.PhysicalSU2BondField L
sum2Tangent = addTangent

sum3Tangent : ∀ {L} → Physical.PhysicalSU2BondField L →
  Physical.PhysicalSU2BondField L → Physical.PhysicalSU2BondField L →
  Physical.PhysicalSU2BondField L
sum3Tangent first second third = addTangent (addTangent first second) third

sum4Tangent : ∀ {L} → Physical.PhysicalSU2BondField L →
  Physical.PhysicalSU2BondField L → Physical.PhysicalSU2BondField L →
  Physical.PhysicalSU2BondField L → Physical.PhysicalSU2BondField L
sum4Tangent first second third fourth =
  addTangent (sum3Tangent first second third) fourth

physicalWilsonQuarticMixedVertex : ∀ {n} → RationalSU2Background (suc n) →
  Physical.PhysicalSU2BondField (suc n) →
  Physical.PhysicalSU2BondField (suc n) →
  Physical.PhysicalSU2BondField (suc n) →
  Physical.PhysicalSU2BondField (suc n) → ℚ
physicalWilsonQuarticMixedVertex background first second third fourth =
  (+ 1 / 24) *
  ( physicalWilsonQuarticVertex background (sum4Tangent first second third fourth)
    - ( physicalWilsonQuarticVertex background (sum3Tangent first second third)
      + physicalWilsonQuarticVertex background (sum3Tangent first second fourth)
      + physicalWilsonQuarticVertex background (sum3Tangent first third fourth)
      + physicalWilsonQuarticVertex background (sum3Tangent second third fourth))
    + ( physicalWilsonQuarticVertex background (sum2Tangent first second)
      + physicalWilsonQuarticVertex background (sum2Tangent first third)
      + physicalWilsonQuarticVertex background (sum2Tangent first fourth)
      + physicalWilsonQuarticVertex background (sum2Tangent second third)
      + physicalWilsonQuarticVertex background (sum2Tangent second fourth)
      + physicalWilsonQuarticVertex background (sum2Tangent third fourth))
    - ( physicalWilsonQuarticVertex background first
      + physicalWilsonQuarticVertex background second
      + physicalWilsonQuarticVertex background third
      + physicalWilsonQuarticVertex background fourth)
    + physicalWilsonQuarticVertex background zeroTangent )

-- This remains conditional until the source file is type-checked and, more
-- importantly, its discrete Fourier transform and p=0 mixed derivative are
-- derived on the same carrier.  It must not be mistaken for beta positivity.
literalArbitrarySideWilsonFourthJetLevel : ProofLevel
literalArbitrarySideWilsonFourthJetLevel = conditional

literalArbitrarySideWilsonCubicQuarticVertexLevel : ProofLevel
literalArbitrarySideWilsonCubicQuarticVertexLevel = conditional

literalArbitrarySideWilsonMixedQuarticVertexLevel : ProofLevel
literalArbitrarySideWilsonMixedQuarticVertexLevel = conditional
