module DASHI.Mathematics.Topology.HopfU1CurvatureNaturalityExact where

-- Exact algebraic fragment of the future Hopf / Kaluza--Klein connection.
-- This theorem does not require a smooth manifold: along the selected
-- Cartan U(1) direction the SU(2) curvature bracket term vanishes.
-- Differentiation and a physical 4D pullback remain separately required.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; sym)
import DASHI.Physics.Electromagnetism.U1AsSU2AbelianRestrictionExact as EM
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as SU2
import DASHI.Physics.YangMills.BalabanSU2LieBracket as Bracket

-- The existing proof applies to arbitrary two phase coefficients.
cartanSelfInteractionVanishes :
  (a b : EM.U1LieAlgebra) →
  Bracket.lieBracket (EM.embedU1Lie a) (EM.embedU1Lie b)
    ≡ SU2.lieZero
cartanSelfInteractionVanishes = EM.u1EmbeddedLieBracketZero

-- The structural homomorphism at the Lie bracket level for the
-- abelian source. This is the genuinely available part of the
-- curvature naturality theorem.
abelianCurvatureBracketCompatibility :
  (a b : EM.U1LieAlgebra) →
  Bracket.lieBracket (EM.embedU1Lie a) (EM.embedU1Lie b)
    ≡ Bracket.lieBracket
        (EM.embedU1Lie b) (EM.embedU1Lie a)
abelianCurvatureBracketCompatibility a b =
  trans (EM.u1EmbeddedLieBracketZero a b)
        (sym (EM.u1EmbeddedLieBracketZero b a))
