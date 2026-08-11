module DASHI.Reasoning.RelationalTernaryPhaseGeometry where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import Data.Integer.Tactic.RingSolver as IntRS
import Tactic.RingSolver.NonReflective as NR

import DASHI.Physics.ShiftDiscreteWaveStep as CartesianWave
import DASHI.Physics.ShiftPhaseTableInterference as Phase4
import DASHI.Reasoning.RelationalBranchInterference as Cartesian

------------------------------------------------------------------------
-- Exact symmetric ternary phase geometry.
--
-- The existing integer-pair carrier exactly represents quarter turns
-- 0, pi/2, pi, 3pi/2.  A symmetric three-way phase system instead needs the
-- Eisenstein lattice Z[omega], where omega^2 + omega + 1 = 0.  This module
-- therefore separates:
--
--   * ordered relational alignment: 0, pi/2, pi on the Cartesian carrier;
--   * symmetric ternary alternatives: 0, 2pi/3, 4pi/3 on Z[omega].
--
-- No analytic complex-number or physical quantum claim is required.
------------------------------------------------------------------------

module RingZ = NR IntRS.ring
open RingZ using (Expr; Κ; Ι; _⊕_; _⊗_; ⊝_; _⊜_; solve)

record EisensteinWave : Set where
  constructor eisensteinWave
  field
    oneCoefficient : ℤ
    omegaCoefficient : ℤ

open EisensteinWave public

zeroE : EisensteinWave
zeroE = eisensteinWave (+ 0) (+ 0)

addE : EisensteinWave → EisensteinWave → EisensteinWave
addE x y =
  eisensteinWave
    (oneCoefficient x + oneCoefficient y)
    (omegaCoefficient x + omegaCoefficient y)

mulE : EisensteinWave → EisensteinWave → EisensteinWave
mulE x y =
  eisensteinWave
    ((oneCoefficient x * oneCoefficient y)
      - (omegaCoefficient x * omegaCoefficient y))
    (((oneCoefficient x * omegaCoefficient y)
      + (omegaCoefficient x * oneCoefficient y))
      - (omegaCoefficient x * omegaCoefficient y))

sumE : List EisensteinWave → EisensteinWave
sumE [] = zeroE
sumE (x ∷ xs) = addE x (sumE xs)

normE : EisensteinWave → ℤ
normE x =
  (oneCoefficient x * oneCoefficient x)
  - (oneCoefficient x * omegaCoefficient x)
  + (omegaCoefficient x * omegaCoefficient x)

pairInterferenceE : EisensteinWave → EisensteinWave → ℤ
pairInterferenceE x y =
  ((+ 2) *
    ((oneCoefficient x * oneCoefficient y)
      + (omegaCoefficient x * omegaCoefficient y)))
  -
  ((oneCoefficient x * omegaCoefficient y)
    + (omegaCoefficient x * oneCoefficient y))

------------------------------------------------------------------------
-- Eisenstein polarization identity.
------------------------------------------------------------------------

eisensteinDoubleSlitLaw :
  (x y : EisensteinWave) →
  normE (addE x y)
  ≡
  (normE x + normE y) + pairInterferenceE x y
eisensteinDoubleSlitLaw
  (eisensteinWave a b)
  (eisensteinWave c d) =
  RingZ.solve 4
    (λ a b c d →
      let
        nsum =
          ((a ⊕ c) ⊗ (a ⊕ c))
          ⊝ ((a ⊕ c) ⊗ (b ⊕ d))
          ⊕ ((b ⊕ d) ⊗ (b ⊕ d))
        nx = (a ⊗ a) ⊝ (a ⊗ b) ⊕ (b ⊗ b)
        ny = (c ⊗ c) ⊝ (c ⊗ d) ⊕ (d ⊗ d)
        cross =
          (Κ (+ 2) ⊗ ((a ⊗ c) ⊕ (b ⊗ d)))
          ⊝ ((a ⊗ d) ⊕ (b ⊗ c))
      in
      ( nsum , (nx ⊕ ny) ⊕ cross ))
    refl a b c d

------------------------------------------------------------------------
-- The exact cubic roots of unity.
--
-- omega^2 is represented by -1 - omega.
------------------------------------------------------------------------

rootOne rootOmega rootOmegaSquared : EisensteinWave
rootOne = eisensteinWave (+ 1) (+ 0)
rootOmega = eisensteinWave (+ 0) (+ 1)
rootOmegaSquared = eisensteinWave (-[1+ 0 ]) (-[1+ 0 ])

rootOneNormIsOne : normE rootOne ≡ + 1
rootOneNormIsOne = refl

rootOmegaNormIsOne : normE rootOmega ≡ + 1
rootOmegaNormIsOne = refl

rootOmegaSquaredNormIsOne : normE rootOmegaSquared ≡ + 1
rootOmegaSquaredNormIsOne = refl

omegaTimesOneIsOmega : mulE rootOmega rootOne ≡ rootOmega
omegaTimesOneIsOmega = refl

omegaTimesOmegaIsOmegaSquared :
  mulE rootOmega rootOmega ≡ rootOmegaSquared
omegaTimesOmegaIsOmegaSquared = refl

omegaTimesOmegaSquaredIsOne :
  mulE rootOmega rootOmegaSquared ≡ rootOne
omegaTimesOmegaSquaredIsOne = refl

ternaryRootsCancel :
  sumE (rootOne ∷ rootOmega ∷ rootOmegaSquared ∷ []) ≡ zeroE
ternaryRootsCancel = refl

rootOneOmegaInterferenceIsMinusOne :
  pairInterferenceE rootOne rootOmega ≡ -[1+ 0 ]
rootOneOmegaInterferenceIsMinusOne = refl

rootOneOmegaSquaredInterferenceIsMinusOne :
  pairInterferenceE rootOne rootOmegaSquared ≡ -[1+ 0 ]
rootOneOmegaSquaredInterferenceIsMinusOne = refl

rootOmegaOmegaSquaredInterferenceIsMinusOne :
  pairInterferenceE rootOmega rootOmegaSquared ≡ -[1+ 0 ]
rootOmegaOmegaSquaredInterferenceIsMinusOne = refl

ternarySymmetricIntensityIsZero :
  normE (sumE (rootOne ∷ rootOmega ∷ rootOmegaSquared ∷ [])) ≡ + 0
ternarySymmetricIntensityIsZero = refl

ternaryDiagonalMassIsThree :
  normE rootOne + normE rootOmega + normE rootOmegaSquared ≡ + 3
ternaryDiagonalMassIsThree = refl

ternaryPairwiseMassIsMinusThree :
  pairInterferenceE rootOne rootOmega
  + pairInterferenceE rootOne rootOmegaSquared
  + pairInterferenceE rootOmega rootOmegaSquared
  ≡ -[1+ 2 ]
ternaryPairwiseMassIsMinusThree = refl

ternaryCancellationLedger :
  (normE rootOne + normE rootOmega + normE rootOmegaSquared)
  +
  (pairInterferenceE rootOne rootOmega
    + pairInterferenceE rootOne rootOmegaSquared
    + pairInterferenceE rootOmega rootOmegaSquared)
  ≡ + 0
ternaryCancellationLedger = refl

------------------------------------------------------------------------
-- Ordered relational alignment on the existing Cartesian phase-4 carrier.
------------------------------------------------------------------------

data OrderedAlignment : Set where
  alignedDirection openOrthogonalDirection opposedDirection : OrderedAlignment

orderedWave : OrderedAlignment → Cartesian.BranchWave
orderedWave alignedDirection =
  CartesianWave.encodePhase4 Phase4.φ0
orderedWave openOrthogonalDirection =
  CartesianWave.encodePhase4 Phase4.φ1
orderedWave opposedDirection =
  CartesianWave.encodePhase4 Phase4.φ2

alignedOpenInterferenceIsZero :
  Cartesian.pairInterference
    (orderedWave alignedDirection)
    (orderedWave openOrthogonalDirection)
  ≡ + 0
alignedOpenInterferenceIsZero = refl

alignedOpposedInterferenceIsMinusTwo :
  Cartesian.pairInterference
    (orderedWave alignedDirection)
    (orderedWave opposedDirection)
  ≡ -[1+ 1 ]
alignedOpposedInterferenceIsMinusTwo = refl

openOpposedInterferenceIsZero :
  Cartesian.pairInterference
    (orderedWave openOrthogonalDirection)
    (orderedWave opposedDirection)
  ≡ + 0
openOpposedInterferenceIsZero = refl

orderedThreeWayIntensityIsOne :
  Cartesian.coherentIntensity
    (orderedWave alignedDirection
      ∷ orderedWave openOrthogonalDirection
      ∷ orderedWave opposedDirection
      ∷ [])
  ≡ + 1
orderedThreeWayIntensityIsOne = refl

------------------------------------------------------------------------
-- Geometry-selection boundary.
------------------------------------------------------------------------

data TernaryGeometryKind : Set where
  symmetricRootsOfUnity orderedHalfCircle : TernaryGeometryKind

record TernaryGeometryChoice : Set where
  constructor ternaryGeometryChoice
  field
    geometryKind : TernaryGeometryKind
    alternativesStructurallySymmetric : Bool
    alternativesOrderedRelativeToInput : Bool
    choiceReceipt : String

symmetricTernaryChoice : TernaryGeometryChoice
symmetricTernaryChoice = ternaryGeometryChoice
  symmetricRootsOfUnity
  true
  false
  "Use 0, 2pi/3, 4pi/3 when the three alternatives are symmetric channels."

orderedRelationalChoice : TernaryGeometryChoice
orderedRelationalChoice = ternaryGeometryChoice
  orderedHalfCircle
  false
  true
  "Use 0, pi/2, pi when the states mean aligned, open/orthogonal, opposed."

record TernaryPhaseAuthorityBoundary : Set where
  field
    exactEisensteinCancellation : Bool
    exactOrderedCartesianComparison : Bool
    symmetricAndOrderedGeometriesAreInterchangeable : Bool
    literalComplexAnalyticPhaseClaimed : Bool
    literalQuantumDecisionClaimed : Bool
    modularJInvariantClaimed : Bool
    boundaryNote : String

canonicalTernaryPhaseAuthorityBoundary : TernaryPhaseAuthorityBoundary
canonicalTernaryPhaseAuthorityBoundary = record
  { exactEisensteinCancellation = true
  ; exactOrderedCartesianComparison = true
  ; symmetricAndOrderedGeometriesAreInterchangeable = false
  ; literalComplexAnalyticPhaseClaimed = false
  ; literalQuantumDecisionClaimed = false
  ; modularJInvariantClaimed = false
  ; boundaryNote =
      "Z[omega] gives an exact finite carrier for symmetric three-way phase cancellation. The Cartesian phase-4 carrier gives the ordered aligned/open/opposed geometry. The labels j-coarse and j-fine are scale metaphors here, not claims about the modular j-invariant."
  }
