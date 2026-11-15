module DASHI.Mathematics.Algebra.RationalAlbertInnerDerivationLawExact where

------------------------------------------------------------------------
-- GENERIC INNER-DERIVATION LAW ON THE ACTUAL RATIONAL ALBERT PRODUCT
--
-- The earlier F4 boundary had exact-rational runtime checks for all 351
-- coordinate-basis pairs.  This theorem is stronger: for arbitrary Albert
-- elements a,b, the commutator [L_a,L_b] satisfies the derivation identity on
-- arbitrary x,y.  As with the Jordan-law owner, the proof is a direct exact
-- rational polynomial exhaustion of the literal coordinate formulas.
--
-- This removes "basis-pair derivation law" from the F4 mathematical frontier.
-- It does not prove that the span of inner derivations has dimension 52 or
-- identify its Lie type as F4.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O
import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanLawsExact as Laws
import DASHI.Mathematics.Algebra.RationalAlbertInnerDerivationF4BoundaryExact as D

innerDerivationLaw :
  (left right : A.RationalAlbert) →
  D.DerivationLaw (D.innerDerivation left right)
innerDerivationLaw
  (A.albert a0 a1 a2
    (O.oct (Q.quat ax0 ax1 ax2 ax3) (Q.quat ax4 ax5 ax6 ax7))
    (O.oct (Q.quat ay0 ay1 ay2 ay3) (Q.quat ay4 ay5 ay6 ay7))
    (O.oct (Q.quat az0 az1 az2 az3) (Q.quat az4 az5 az6 az7)))
  (A.albert b0 b1 b2
    (O.oct (Q.quat bx0 bx1 bx2 bx3) (Q.quat bx4 bx5 bx6 bx7))
    (O.oct (Q.quat by0 by1 by2 by3) (Q.quat by4 by5 by6 by7))
    (O.oct (Q.quat bz0 bz1 bz2 bz3) (Q.quat bz4 bz5 bz6 bz7)))
  (A.albert c0 c1 c2
    (O.oct (Q.quat cx0 cx1 cx2 cx3) (Q.quat cx4 cx5 cx6 cx7))
    (O.oct (Q.quat cy0 cy1 cy2 cy3) (Q.quat cy4 cy5 cy6 cy7))
    (O.oct (Q.quat cz0 cz1 cz2 cz3) (Q.quat cz4 cz5 cz6 cz7)))
  (A.albert d0 d1 d2
    (O.oct (Q.quat dx0 dx1 dx2 dx3) (Q.quat dx4 dx5 dx6 dx7))
    (O.oct (Q.quat dy0 dy1 dy2 dy3) (Q.quat dy4 dy5 dy6 dy7))
    (O.oct (Q.quat dz0 dz1 dz2 dz3) (Q.quat dz4 dz5 dz6 dz7))) =
  Laws.albertExt
    (solve vars) (solve vars) (solve vars)
    (O.octonionExt
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars)))
    (O.octonionExt
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars)))
    (O.octonionExt
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars))
      (Q.quaternionExt (solve vars) (solve vars) (solve vars) (solve vars)))
  where
    vars : List ℚ
    vars =
      a0 ∷ a1 ∷ a2 ∷
      ax0 ∷ ax1 ∷ ax2 ∷ ax3 ∷ ax4 ∷ ax5 ∷ ax6 ∷ ax7 ∷
      ay0 ∷ ay1 ∷ ay2 ∷ ay3 ∷ ay4 ∷ ay5 ∷ ay6 ∷ ay7 ∷
      az0 ∷ az1 ∷ az2 ∷ az3 ∷ az4 ∷ az5 ∷ az6 ∷ az7 ∷
      b0 ∷ b1 ∷ b2 ∷
      bx0 ∷ bx1 ∷ bx2 ∷ bx3 ∷ bx4 ∷ bx5 ∷ bx6 ∷ bx7 ∷
      by0 ∷ by1 ∷ by2 ∷ by3 ∷ by4 ∷ by5 ∷ by6 ∷ by7 ∷
      bz0 ∷ bz1 ∷ bz2 ∷ bz3 ∷ bz4 ∷ bz5 ∷ bz6 ∷ bz7 ∷
      c0 ∷ c1 ∷ c2 ∷
      cx0 ∷ cx1 ∷ cx2 ∷ cx3 ∷ cx4 ∷ cx5 ∷ cx6 ∷ cx7 ∷
      cy0 ∷ cy1 ∷ cy2 ∷ cy3 ∷ cy4 ∷ cy5 ∷ cy6 ∷ cy7 ∷
      cz0 ∷ cz1 ∷ cz2 ∷ cz3 ∷ cz4 ∷ cz5 ∷ cz6 ∷ cz7 ∷
      d0 ∷ d1 ∷ d2 ∷
      dx0 ∷ dx1 ∷ dx2 ∷ dx3 ∷ dx4 ∷ dx5 ∷ dx6 ∷ dx7 ∷
      dy0 ∷ dy1 ∷ dy2 ∷ dy3 ∷ dy4 ∷ dy5 ∷ dy6 ∷ dy7 ∷
      dz0 ∷ dz1 ∷ dz2 ∷ dz3 ∷ dz4 ∷ dz5 ∷ dz6 ∷ dz7 ∷ []
