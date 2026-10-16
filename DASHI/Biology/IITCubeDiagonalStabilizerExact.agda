module DASHI.Biology.IITCubeDiagonalStabilizerExact where

------------------------------------------------------------------------
-- DIAGONAL STABILIZER OF THE CONCRETE CUBE IMAGE
--
-- The full trinification action does not preserve the selected causal graph;
-- IITCubeTrinificationSymmetryBreakingExact already supplies an explicit shear
-- counterexample.  The productive remaining question is therefore the exact
-- stabilizer of the graph under one and the same linear face map on all three
-- layers.
--
-- For additive/zero-preserving face maps T, graph preservation is equivalent
-- to commuting with the concrete face operator B = bop.  Thus the diagonal
-- stabilizer is the centralizer of B, not the whole exceptional action.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.IITCubeConcreteTorusImageExact as Cube
import DASHI.Biology.JFinePhaseQuotientFieldExact as Fine

record FaceLinearEndo : Set where
  constructor face-linear-endo
  field
    map : Cube.Face9 → Cube.Face9
    mapZero : map Cube.zeroFace ≡ Cube.zeroFace
    mapSub : (x y : Cube.Face9) →
      map (Cube.subFace x y) ≡ Cube.subFace (map x) (map y)
open FaceLinearEndo public

CommutesWithB : FaceLinearEndo → Set
CommutesWithB T = (f : Cube.Face9) → map T (Cube.bop f) ≡ Cube.bop (map T f)

mapCube : FaceLinearEndo → Cube.CubeFaces → Cube.CubeFaces
mapCube T c = Cube.cube-faces
  (map T (Cube.face0 c))
  (map T (Cube.face1 c))
  (map T (Cube.face2 c))

PreservesGraph : FaceLinearEndo → Set
PreservesGraph T = (c : Cube.CubeFaces) → Cube.GraphLaw c → Cube.GraphLaw (mapCube T c)

bop2Zero : Cube.bop2 Cube.zeroFace ≡ Cube.zeroFace
bop2Zero = trans (cong Cube.bop Cube.bopZero) Cube.bopZero

negZeroFace : Cube.negFace Cube.zeroFace ≡ Cube.zeroFace
negZeroFace = refl

subZeroRFace : (f : Cube.Face9) → Cube.subFace f Cube.zeroFace ≡ f
subZeroRFace f =
  trans
    (cong (Cube.addFace f) negZeroFace)
    (Cube.addZeroRFace f)

commuteB2 : (T : FaceLinearEndo) → CommutesWithB T →
  (f : Cube.Face9) → map T (Cube.bop2 f) ≡ Cube.bop2 (map T f)
commuteB2 T commutes f =
  trans
    (commutes (Cube.bop f))
    (cong Cube.bop (commutes f))

centralizerPreservesGraph :
  (T : FaceLinearEndo) → CommutesWithB T → PreservesGraph T
centralizerPreservesGraph T commutes c graph =
  trans
    (cong (map T) graph)
    (trans
      (mapSub T (Cube.bop (Cube.face1 c)) (Cube.bop2 (Cube.face0 c)))
      (trans
        (cong
          (λ x → Cube.subFace x (map T (Cube.bop2 (Cube.face0 c))))
          (commutes (Cube.face1 c)))
        (cong
          (Cube.subFace (Cube.bop (map T (Cube.face1 c))))
          (commuteB2 T commutes (Cube.face0 c)))))

probeCube : Cube.Face9 → Cube.CubeFaces
probeCube f = Cube.cube-faces Cube.zeroFace f (Cube.bop f)

probeGraphLaw : (f : Cube.Face9) → Cube.GraphLaw (probeCube f)
probeGraphLaw f =
  sym
    (trans
      (cong (Cube.subFace (Cube.bop f)) bop2Zero)
      (subZeroRFace (Cube.bop f)))

preservesGraphForcesCentralizer :
  (T : FaceLinearEndo) → PreservesGraph T → CommutesWithB T
preservesGraphForcesCentralizer T preserves f =
  trans
    (preserves (probeCube f) (probeGraphLaw f))
    (trans
      (cong
        (Cube.subFace (Cube.bop (map T f)))
        (trans (cong Cube.bop2 (mapZero T)) bop2Zero))
      (subZeroRFace (Cube.bop (map T f))))

record DiagonalGraphStabilizerCharacterization (T : FaceLinearEndo) : Set where
  constructor diagonal-graph-stabilizer-characterization
  field
    centralizerImpliesGraphPreservation : CommutesWithB T → PreservesGraph T
    graphPreservationImpliesCentralizer : PreservesGraph T → CommutesWithB T
open DiagonalGraphStabilizerCharacterization public

diagonalStabilizerIffCentralizer :
  (T : FaceLinearEndo) → DiagonalGraphStabilizerCharacterization T
diagonalStabilizerIffCentralizer T =
  diagonal-graph-stabilizer-characterization
    (centralizerPreservesGraph T)
    (preservesGraphForcesCentralizer T)

identityFaceEndo : FaceLinearEndo
identityFaceEndo = face-linear-endo
  (λ x → x)
  refl
  (λ x y → refl)

identityCommutesWithB : CommutesWithB identityFaceEndo
identityCommutesWithB f = refl

identityPreservesGraph : PreservesGraph identityFaceEndo
identityPreservesGraph = centralizerPreservesGraph identityFaceEndo identityCommutesWithB

------------------------------------------------------------------------
-- Explicit nontrivial centralizer subgroup: the two cyclic translations of
-- the 3x3 face.  Each has period three and they commute with B by construction.
------------------------------------------------------------------------

rowShift : Cube.Face9 → Cube.Face9
rowShift f = Fine.phaseFineTable9
  (Fine.q10 f) (Fine.q11 f) (Fine.q12 f)
  (Fine.q20 f) (Fine.q21 f) (Fine.q22 f)
  (Fine.q00 f) (Fine.q01 f) (Fine.q02 f)

columnShift : Cube.Face9 → Cube.Face9
columnShift f = Fine.phaseFineTable9
  (Fine.q01 f) (Fine.q02 f) (Fine.q00 f)
  (Fine.q11 f) (Fine.q12 f) (Fine.q10 f)
  (Fine.q21 f) (Fine.q22 f) (Fine.q20 f)

rowShiftEndo : FaceLinearEndo
rowShiftEndo = face-linear-endo rowShift refl (λ x y → refl)

columnShiftEndo : FaceLinearEndo
columnShiftEndo = face-linear-endo columnShift refl (λ x y → refl)

rowShiftCommutesWithB : CommutesWithB rowShiftEndo
rowShiftCommutesWithB f = refl

columnShiftCommutesWithB : CommutesWithB columnShiftEndo
columnShiftCommutesWithB f = refl

rowShiftPreservesGraph : PreservesGraph rowShiftEndo
rowShiftPreservesGraph = centralizerPreservesGraph rowShiftEndo rowShiftCommutesWithB

columnShiftPreservesGraph : PreservesGraph columnShiftEndo
columnShiftPreservesGraph = centralizerPreservesGraph columnShiftEndo columnShiftCommutesWithB

rowShiftOrderThree : (f : Cube.Face9) → rowShift (rowShift (rowShift f)) ≡ f
rowShiftOrderThree f = refl

columnShiftOrderThree : (f : Cube.Face9) → columnShift (columnShift (columnShift f)) ≡ f
columnShiftOrderThree f = refl

rowColumnCommute : (f : Cube.Face9) →
  rowShift (columnShift f) ≡ columnShift (rowShift f)
rowColumnCommute f = refl

------------------------------------------------------------------------
-- Row/column reflection.  B = rowShift + columnShift is symmetric in the two
-- directions, so table transpose belongs to the same diagonal graph stabilizer.
-- Together with the commuting order-three translations this gives the exact
-- generator relations of the expected C3^2 semidirect C2 permutation spine.
-- This does NOT claim those permutation generators exhaust the full 27-
-- dimensional linear centralizer found by the independent finite audit.
------------------------------------------------------------------------

transposeFace : Cube.Face9 → Cube.Face9
transposeFace f = Fine.phaseFineTable9
  (Fine.q00 f) (Fine.q10 f) (Fine.q20 f)
  (Fine.q01 f) (Fine.q11 f) (Fine.q21 f)
  (Fine.q02 f) (Fine.q12 f) (Fine.q22 f)

transposeEndo : FaceLinearEndo
transposeEndo = face-linear-endo transposeFace refl (λ x y → refl)

transposeCommutesWithB : CommutesWithB transposeEndo
transposeCommutesWithB f = refl

transposePreservesGraph : PreservesGraph transposeEndo
transposePreservesGraph =
  centralizerPreservesGraph transposeEndo transposeCommutesWithB

transposeInvolutive : (f : Cube.Face9) → transposeFace (transposeFace f) ≡ f
transposeInvolutive f = refl

transposeRowToColumn : (f : Cube.Face9) →
  transposeFace (rowShift f) ≡ columnShift (transposeFace f)
transposeRowToColumn f = refl

transposeColumnToRow : (f : Cube.Face9) →
  transposeFace (columnShift f) ≡ rowShift (transposeFace f)
transposeColumnToRow f = refl
