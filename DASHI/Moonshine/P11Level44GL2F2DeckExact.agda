module DASHI.Moonshine.P11Level44GL2F2DeckExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
-- Full level-2 structures and change of frame.
--
-- DASHI CONTRIBUTION
--
-- Complete the finite local quotient left implicit by
-- P11Level44TwoAdicFixedVectorSeparationExact.
--
-- There are exactly six invertible 2x2 matrices over F_2.  We enumerate them,
-- classify every determinant-one matrix into that six-element carrier, and
-- identify their action on
--
--   P^1(F_2) = {(1,0),(0,1),(1,1)}
--
-- with the repository's six existing TriPermutation constructors.
--
-- Thus the marked deck action is not merely "S3-shaped": its finite local
-- quotient is explicitly GL_2(F_2), acting on the three projective points in
-- the standard faithful permutation representation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Tri
import DASHI.Moonshine.P11Level44TwoAdicFixedVectorSeparationExact as Local2

------------------------------------------------------------------------
-- Determinant over F_2.  Subtraction equals addition in characteristic two.
------------------------------------------------------------------------

determinant : Local2.Mat2F2 → Local2.F2
determinant M =
  Local2._+₂_
    (Local2._*₂_ (Local2.a11 M) (Local2.a22 M))
    (Local2._*₂_ (Local2.a12 M) (Local2.a21 M))

------------------------------------------------------------------------
-- The six elements of GL_2(F_2), written in the S3 normal form
-- 1,r,r^2,s,rs,r^2s.
------------------------------------------------------------------------

data GL2F2 : Set where
  g1 gr gr2 gs grs gr2s : GL2F2

matrixOf : GL2F2 → Local2.Mat2F2
matrixOf g1 = Local2.mat2 Local2.f1 Local2.f0 Local2.f0 Local2.f1
matrixOf gr = Local2.mat2 Local2.f0 Local2.f1 Local2.f1 Local2.f1
matrixOf gr2 = Local2.mat2 Local2.f1 Local2.f1 Local2.f1 Local2.f0
matrixOf gs = Local2.mat2 Local2.f1 Local2.f1 Local2.f0 Local2.f1
matrixOf grs = Local2.mat2 Local2.f0 Local2.f1 Local2.f1 Local2.f0
matrixOf gr2s = Local2.mat2 Local2.f1 Local2.f0 Local2.f1 Local2.f1

matrixOfIsInvertible : (g : GL2F2) → determinant (matrixOf g) ≡ Local2.f1
matrixOfIsInvertible g1 = refl
matrixOfIsInvertible gr = refl
matrixOfIsInvertible gr2 = refl
matrixOfIsInvertible gs = refl
matrixOfIsInvertible grs = refl
matrixOfIsInvertible gr2s = refl

------------------------------------------------------------------------
-- Exhaustiveness: inspect all sixteen matrices.  The ten singular cases make
-- determinant=1 impossible; the six surviving cases are exactly the list.
------------------------------------------------------------------------

classifyInvertible :
  (M : Local2.Mat2F2) → determinant M ≡ Local2.f1 → GL2F2
classifyInvertible (Local2.mat2 Local2.f0 Local2.f0 Local2.f0 Local2.f0) ()
classifyInvertible (Local2.mat2 Local2.f0 Local2.f0 Local2.f0 Local2.f1) ()
classifyInvertible (Local2.mat2 Local2.f0 Local2.f0 Local2.f1 Local2.f0) ()
classifyInvertible (Local2.mat2 Local2.f0 Local2.f0 Local2.f1 Local2.f1) ()
classifyInvertible (Local2.mat2 Local2.f0 Local2.f1 Local2.f0 Local2.f0) ()
classifyInvertible (Local2.mat2 Local2.f0 Local2.f1 Local2.f0 Local2.f1) ()
classifyInvertible (Local2.mat2 Local2.f0 Local2.f1 Local2.f1 Local2.f0) proof = grs
classifyInvertible (Local2.mat2 Local2.f0 Local2.f1 Local2.f1 Local2.f1) proof = gr
classifyInvertible (Local2.mat2 Local2.f1 Local2.f0 Local2.f0 Local2.f0) ()
classifyInvertible (Local2.mat2 Local2.f1 Local2.f0 Local2.f0 Local2.f1) proof = g1
classifyInvertible (Local2.mat2 Local2.f1 Local2.f0 Local2.f1 Local2.f0) ()
classifyInvertible (Local2.mat2 Local2.f1 Local2.f0 Local2.f1 Local2.f1) proof = gr2s
classifyInvertible (Local2.mat2 Local2.f1 Local2.f1 Local2.f0 Local2.f0) ()
classifyInvertible (Local2.mat2 Local2.f1 Local2.f1 Local2.f0 Local2.f1) proof = gs
classifyInvertible (Local2.mat2 Local2.f1 Local2.f1 Local2.f1 Local2.f0) proof = gr2
classifyInvertible (Local2.mat2 Local2.f1 Local2.f1 Local2.f1 Local2.f1) ()

classificationExact :
  (M : Local2.Mat2F2) →
  (proof : determinant M ≡ Local2.f1) →
  matrixOf (classifyInvertible M proof) ≡ M
classificationExact (Local2.mat2 Local2.f0 Local2.f0 Local2.f0 Local2.f0) ()
classificationExact (Local2.mat2 Local2.f0 Local2.f0 Local2.f0 Local2.f1) ()
classificationExact (Local2.mat2 Local2.f0 Local2.f0 Local2.f1 Local2.f0) ()
classificationExact (Local2.mat2 Local2.f0 Local2.f0 Local2.f1 Local2.f1) ()
classificationExact (Local2.mat2 Local2.f0 Local2.f1 Local2.f0 Local2.f0) ()
classificationExact (Local2.mat2 Local2.f0 Local2.f1 Local2.f0 Local2.f1) ()
classificationExact (Local2.mat2 Local2.f0 Local2.f1 Local2.f1 Local2.f0) proof = refl
classificationExact (Local2.mat2 Local2.f0 Local2.f1 Local2.f1 Local2.f1) proof = refl
classificationExact (Local2.mat2 Local2.f1 Local2.f0 Local2.f0 Local2.f0) ()
classificationExact (Local2.mat2 Local2.f1 Local2.f0 Local2.f0 Local2.f1) proof = refl
classificationExact (Local2.mat2 Local2.f1 Local2.f0 Local2.f1 Local2.f0) ()
classificationExact (Local2.mat2 Local2.f1 Local2.f0 Local2.f1 Local2.f1) proof = refl
classificationExact (Local2.mat2 Local2.f1 Local2.f1 Local2.f0 Local2.f0) ()
classificationExact (Local2.mat2 Local2.f1 Local2.f1 Local2.f0 Local2.f1) proof = refl
classificationExact (Local2.mat2 Local2.f1 Local2.f1 Local2.f1 Local2.f0) proof = refl
classificationExact (Local2.mat2 Local2.f1 Local2.f1 Local2.f1 Local2.f1) ()

------------------------------------------------------------------------
-- Six projective permutations and their existing repository names.
------------------------------------------------------------------------

actGL2P1 : GL2F2 → Local2.P1F2 → Local2.P1F2
actGL2P1 g1 x = x
actGL2P1 gr x = Local2.rotateP1 x
actGL2P1 gr2 x = Local2.rotateP1 (Local2.rotateP1 x)
actGL2P1 gs x = Local2.reflectP1 x
actGL2P1 grs Local2.point1 = Local2.point2
actGL2P1 grs Local2.point2 = Local2.point1
actGL2P1 grs Local2.point4 = Local2.point4
actGL2P1 gr2s Local2.point1 = Local2.point4
actGL2P1 gr2s Local2.point2 = Local2.point2
actGL2P1 gr2s Local2.point4 = Local2.point1

matrixActionMatchesProjectiveAction :
  (g : GL2F2) → (x : Local2.P1F2) →
  Local2.actMatrix (matrixOf g) (Local2.p1Vector x)
  ≡ Local2.p1Vector (actGL2P1 g x)
matrixActionMatchesProjectiveAction g1 Local2.point1 = refl
matrixActionMatchesProjectiveAction g1 Local2.point2 = refl
matrixActionMatchesProjectiveAction g1 Local2.point4 = refl
matrixActionMatchesProjectiveAction gr Local2.point1 = refl
matrixActionMatchesProjectiveAction gr Local2.point2 = refl
matrixActionMatchesProjectiveAction gr Local2.point4 = refl
matrixActionMatchesProjectiveAction gr2 Local2.point1 = refl
matrixActionMatchesProjectiveAction gr2 Local2.point2 = refl
matrixActionMatchesProjectiveAction gr2 Local2.point4 = refl
matrixActionMatchesProjectiveAction gs Local2.point1 = refl
matrixActionMatchesProjectiveAction gs Local2.point2 = refl
matrixActionMatchesProjectiveAction gs Local2.point4 = refl
matrixActionMatchesProjectiveAction grs Local2.point1 = refl
matrixActionMatchesProjectiveAction grs Local2.point2 = refl
matrixActionMatchesProjectiveAction grs Local2.point4 = refl
matrixActionMatchesProjectiveAction gr2s Local2.point1 = refl
matrixActionMatchesProjectiveAction gr2s Local2.point2 = refl
matrixActionMatchesProjectiveAction gr2s Local2.point4 = refl

p1ToTri : Local2.P1F2 → Base.TriTruth
p1ToTri Local2.point1 = Base.tri-low
p1ToTri Local2.point2 = Base.tri-mid
p1ToTri Local2.point4 = Base.tri-high

gl2ToTriPermutation : GL2F2 → Tri.TriPermutation
gl2ToTriPermutation g1 = Tri.permIdentity
gl2ToTriPermutation gr = Tri.permRotate
gl2ToTriPermutation gr2 = Tri.permRotate2
gl2ToTriPermutation gs = Tri.permSwapMidHigh
gl2ToTriPermutation grs = Tri.permSwapLowMid
gl2ToTriPermutation gr2s = Tri.permSwapLowHigh

projectiveActionIsExistingS3Action :
  (g : GL2F2) → (x : Local2.P1F2) →
  p1ToTri (actGL2P1 g x)
  ≡ Tri.applyPermutation (gl2ToTriPermutation g) (p1ToTri x)
projectiveActionIsExistingS3Action g1 Local2.point1 = refl
projectiveActionIsExistingS3Action g1 Local2.point2 = refl
projectiveActionIsExistingS3Action g1 Local2.point4 = refl
projectiveActionIsExistingS3Action gr Local2.point1 = refl
projectiveActionIsExistingS3Action gr Local2.point2 = refl
projectiveActionIsExistingS3Action gr Local2.point4 = refl
projectiveActionIsExistingS3Action gr2 Local2.point1 = refl
projectiveActionIsExistingS3Action gr2 Local2.point2 = refl
projectiveActionIsExistingS3Action gr2 Local2.point4 = refl
projectiveActionIsExistingS3Action gs Local2.point1 = refl
projectiveActionIsExistingS3Action gs Local2.point2 = refl
projectiveActionIsExistingS3Action gs Local2.point4 = refl
projectiveActionIsExistingS3Action grs Local2.point1 = refl
projectiveActionIsExistingS3Action grs Local2.point2 = refl
projectiveActionIsExistingS3Action grs Local2.point4 = refl
projectiveActionIsExistingS3Action gr2s Local2.point1 = refl
projectiveActionIsExistingS3Action gr2s Local2.point2 = refl
projectiveActionIsExistingS3Action gr2s Local2.point4 = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record P11Level44GL2F2DeckBoundary : Set where
  field
    allSixInvertibleMatricesEnumerated : Bool
    invertibleClassificationExact : Bool
    projectiveActionConstructed : Bool
    existingTriPermutationActionIdentified : Bool
    markedDeckFiniteQuotientIsExplicitGL2F2 : Bool
    twoAdicAnalyticLiftConstructed : Bool

canonicalP11Level44GL2F2DeckBoundary : P11Level44GL2F2DeckBoundary
canonicalP11Level44GL2F2DeckBoundary = record
  { allSixInvertibleMatricesEnumerated = true
  ; invertibleClassificationExact = true
  ; projectiveActionConstructed = true
  ; existingTriPermutationActionIdentified = true
  ; markedDeckFiniteQuotientIsExplicitGL2F2 = true
  ; twoAdicAnalyticLiftConstructed = false
  }
