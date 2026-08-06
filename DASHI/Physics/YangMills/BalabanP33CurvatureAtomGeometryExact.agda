module DASHI.Physics.YangMills.BalabanP33CurvatureAtomGeometryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks",
-- Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Prove that the configured 18 curvature atoms are not an arbitrary list.
-- They are exactly the disjoint geometric decomposition
--
--   6 unordered positive coordinate planes
--     + 12 ordered pairs of distinct coordinate axes.
--
-- The first six atoms are the bracket/curvature terms for planes 01, 02, 03,
-- 12, 13 and 23.  The remaining twelve are the ordered transport defects
-- 01, 02, 03, 10, 12, 13, 20, 21, 23, 30, 31 and 32.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  ( Axis4; CyclicIndex; zeroᵢ; sucᵢ; Not; _≢_; map; _++_; _∈_; here; there )
open import DASHI.Physics.YangMills.BalabanPath4PlaquetteOrientationExact using
  ( PositivePlaquettePlane4
  ; plane01; plane02; plane03; plane12; plane13; plane23
  ; positivePlaquettePlanes4
  )
open import DASHI.Physics.YangMills.BalabanClayT3ConfiguredFiniteAtomListsExact using
  ( CurvatureAtom
  ; curvatureBracket01; curvatureBracket02; curvatureBracket03
  ; curvatureBracket12; curvatureBracket13; curvatureBracket23
  ; curvatureTransport01; curvatureTransport02; curvatureTransport03
  ; curvatureTransport10; curvatureTransport12; curvatureTransport13
  ; curvatureTransport20; curvatureTransport21; curvatureTransport23
  ; curvatureTransport30; curvatureTransport31; curvatureTransport32
  ; curvatureAtoms
  )

axis0 axis1 axis2 axis3 : Axis4
axis0 = zeroᵢ
axis1 = sucᵢ zeroᵢ
axis2 = sucᵢ (sucᵢ zeroᵢ)
axis3 = sucᵢ (sucᵢ (sucᵢ zeroᵢ))

data DirectedAxisPair4 : Set where
  directed01 directed02 directed03 directed10 : DirectedAxisPair4
  directed12 directed13 directed20 directed21 : DirectedAxisPair4
  directed23 directed30 directed31 directed32 : DirectedAxisPair4

directedAxisPairFirst : DirectedAxisPair4 → Axis4
directedAxisPairFirst directed01 = axis0
directedAxisPairFirst directed02 = axis0
directedAxisPairFirst directed03 = axis0
directedAxisPairFirst directed10 = axis1
directedAxisPairFirst directed12 = axis1
directedAxisPairFirst directed13 = axis1
directedAxisPairFirst directed20 = axis2
directedAxisPairFirst directed21 = axis2
directedAxisPairFirst directed23 = axis2
directedAxisPairFirst directed30 = axis3
directedAxisPairFirst directed31 = axis3
directedAxisPairFirst directed32 = axis3

directedAxisPairSecond : DirectedAxisPair4 → Axis4
directedAxisPairSecond directed01 = axis1
directedAxisPairSecond directed02 = axis2
directedAxisPairSecond directed03 = axis3
directedAxisPairSecond directed10 = axis0
directedAxisPairSecond directed12 = axis2
directedAxisPairSecond directed13 = axis3
directedAxisPairSecond directed20 = axis0
directedAxisPairSecond directed21 = axis1
directedAxisPairSecond directed23 = axis3
directedAxisPairSecond directed30 = axis0
directedAxisPairSecond directed31 = axis1
directedAxisPairSecond directed32 = axis2

directedAxisPairDistinct : ∀ pair →
  directedAxisPairFirst pair ≢ directedAxisPairSecond pair
directedAxisPairDistinct directed01 ()
directedAxisPairDistinct directed02 ()
directedAxisPairDistinct directed03 ()
directedAxisPairDistinct directed10 ()
directedAxisPairDistinct directed12 ()
directedAxisPairDistinct directed13 ()
directedAxisPairDistinct directed20 ()
directedAxisPairDistinct directed21 ()
directedAxisPairDistinct directed23 ()
directedAxisPairDistinct directed30 ()
directedAxisPairDistinct directed31 ()
directedAxisPairDistinct directed32 ()

directedAxisPairs4 : List DirectedAxisPair4
directedAxisPairs4 =
  directed01 ∷ directed02 ∷ directed03 ∷ directed10 ∷
  directed12 ∷ directed13 ∷ directed20 ∷ directed21 ∷
  directed23 ∷ directed30 ∷ directed31 ∷ directed32 ∷ []

directedAxisPairs4Complete : ∀ pair → pair ∈ directedAxisPairs4
directedAxisPairs4Complete directed01 = here
directedAxisPairs4Complete directed02 = there here
directedAxisPairs4Complete directed03 = there (there here)
directedAxisPairs4Complete directed10 = there (there (there here))
directedAxisPairs4Complete directed12 = there (there (there (there here)))
directedAxisPairs4Complete directed13 =
  there (there (there (there (there here))))
directedAxisPairs4Complete directed20 =
  there (there (there (there (there (there here)))))
directedAxisPairs4Complete directed21 =
  there (there (there (there (there (there (there here))))))
directedAxisPairs4Complete directed23 =
  there (there (there (there (there (there (there (there here)))))))
directedAxisPairs4Complete directed30 =
  there (there (there (there (there (there (there (there (there here))))))))
directedAxisPairs4Complete directed31 =
  there (there (there (there (there (there (there (there (there (there here)))))))))
directedAxisPairs4Complete directed32 =
  there (there (there (there (there (there (there (there (there (there (there here))))))))))

curvatureBracketAtom : PositivePlaquettePlane4 → CurvatureAtom
curvatureBracketAtom plane01 = curvatureBracket01
curvatureBracketAtom plane02 = curvatureBracket02
curvatureBracketAtom plane03 = curvatureBracket03
curvatureBracketAtom plane12 = curvatureBracket12
curvatureBracketAtom plane13 = curvatureBracket13
curvatureBracketAtom plane23 = curvatureBracket23

curvatureTransportAtom : DirectedAxisPair4 → CurvatureAtom
curvatureTransportAtom directed01 = curvatureTransport01
curvatureTransportAtom directed02 = curvatureTransport02
curvatureTransportAtom directed03 = curvatureTransport03
curvatureTransportAtom directed10 = curvatureTransport10
curvatureTransportAtom directed12 = curvatureTransport12
curvatureTransportAtom directed13 = curvatureTransport13
curvatureTransportAtom directed20 = curvatureTransport20
curvatureTransportAtom directed21 = curvatureTransport21
curvatureTransportAtom directed23 = curvatureTransport23
curvatureTransportAtom directed30 = curvatureTransport30
curvatureTransportAtom directed31 = curvatureTransport31
curvatureTransportAtom directed32 = curvatureTransport32

curvatureAtomsAreGeometricDecomposition :
  curvatureAtoms
  ≡ map curvatureBracketAtom positivePlaquettePlanes4
      ++ map curvatureTransportAtom directedAxisPairs4
curvatureAtomsAreGeometricDecomposition = refl

positivePlaneCountExact : length positivePlaquettePlanes4 ≡ 6
positivePlaneCountExact = refl

directedDistinctAxisPairCountExact : length directedAxisPairs4 ≡ 12
directedDistinctAxisPairCountExact = refl

curvatureAtomCountExact : length curvatureAtoms ≡ 18
curvatureAtomCountExact = refl

curvatureAtomGeometryLevel : ProofLevel
curvatureAtomGeometryLevel = machineChecked

curvatureAtomMultiplicityLevel : ProofLevel
curvatureAtomMultiplicityLevel = machineChecked
