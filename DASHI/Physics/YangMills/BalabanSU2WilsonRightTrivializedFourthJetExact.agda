module DASHI.Physics.YangMills.BalabanSU2WilsonRightTrivializedFourthJetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall, "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I.", Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
-- Work on the ACTUAL repository SU(2) quaternion carrier.  For the canonical
-- right-trivialized fluctuation split
--
--        U(g) = U_0 exp(g X)
--
-- the one-link derivatives at g=0 are algebraically
--
--        U_0, U_0 X, U_0 X^2, U_0 X^3, U_0 X^4.
--
-- For the oppositely oriented plaquette link
--
--        U(g)^-1 = exp(-g X) U_0^-1,
--
-- they are
--
--        U_0^-1, -X U_0^-1, X^2 U_0^-1,
--        -X^3 U_0^-1, X^4 U_0^-1.
--
-- These are the physical one-link jets consumed by the fourth-order Wilson
-- product Leibniz rule.  The only analytic chart fact left is that the chosen
-- SU(2) exponential really has D^n exp(gX)|_0 = X^n for n<=4; the vertex
-- placements and inverse-link signs are no longer independent inputs.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Foundations.RealAnalysisAxioms as Real
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2QuaternionCarrier
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (SU2LieAlgebra; lieQuaternion)

record SU2QuaternionJet4 : Set where
  constructor su2Jet4
  field
    jet0 jet1 jet2 jet3 jet4 : Quaternion
open SU2QuaternionJet4 public

squareQ cubeQ fourthPowerQ : Quaternion → Quaternion
squareQ x = x *q x
cubeQ x = squareQ x *q x
fourthPowerQ x = squareQ x *q squareQ x

rightTrivializedLinkJet4 : Quaternion → SU2LieAlgebra → SU2QuaternionJet4
rightTrivializedLinkJet4 background insertion =
  let x = lieQuaternion insertion
  in su2Jet4
    background
    (background *q x)
    (background *q squareQ x)
    (background *q cubeQ x)
    (background *q fourthPowerQ x)

inverseOrientedLinkJet4 : Quaternion → SU2LieAlgebra → SU2QuaternionJet4
inverseOrientedLinkJet4 inverseBackground insertion =
  let x = lieQuaternion insertion
  in su2Jet4
    inverseBackground
    (negQ (x *q inverseBackground))
    (squareQ x *q inverseBackground)
    (negQ (cubeQ x *q inverseBackground))
    (fourthPowerQ x *q inverseBackground)

-- Natural multiplicities in D^n(ab); kept as repeated quaternion addition so
-- no scalar-carrier coercion is introduced.
doubleQ tripleQ quadrupleQ sixQ : Quaternion → Quaternion
doubleQ q = q +q q
tripleQ q = q +q (q +q q)
quadrupleQ q = (q +q q) +q (q +q q)
sixQ q = tripleQ q +q tripleQ q

multiplyJet4 : SU2QuaternionJet4 → SU2QuaternionJet4 → SU2QuaternionJet4
multiplyJet4 left right = su2Jet4
  (jet0 left *q jet0 right)
  ((jet1 left *q jet0 right)
    +q (jet0 left *q jet1 right))
  ((jet2 left *q jet0 right)
    +q (doubleQ (jet1 left *q jet1 right)
      +q (jet0 left *q jet2 right)))
  ((jet3 left *q jet0 right)
    +q (tripleQ (jet2 left *q jet1 right)
      +q (tripleQ (jet1 left *q jet2 right)
        +q (jet0 left *q jet3 right))))
  ((jet4 left *q jet0 right)
    +q (quadrupleQ (jet3 left *q jet1 right)
      +q (sixQ (jet2 left *q jet2 right)
        +q (quadrupleQ (jet1 left *q jet3 right)
          +q (jet0 left *q jet4 right)))))

identityJet4 : SU2QuaternionJet4
identityJet4 = su2Jet4 oneQ zeroQ zeroQ zeroQ zeroQ

orderedProductJet4 : List SU2QuaternionJet4 → SU2QuaternionJet4
orderedProductJet4 [] = identityJet4
orderedProductJet4 (factor ∷ factors) =
  multiplyJet4 factor (orderedProductJet4 factors)

fourLinkPlaquetteJet4 :
  SU2QuaternionJet4 → SU2QuaternionJet4 →
  SU2QuaternionJet4 → SU2QuaternionJet4 → SU2QuaternionJet4
fourLinkPlaquetteJet4 first second third fourth =
  orderedProductJet4 (first ∷ second ∷ third ∷ fourth ∷ [])

record RightTrivializedWilsonPlaquetteData : Set where
  field
    forward0 forward1 inverse2 inverse3 : Quaternion
    insertion0 insertion1 insertion2 insertion3 : SU2LieAlgebra
open RightTrivializedWilsonPlaquetteData public

literalPlaquetteJet4 : RightTrivializedWilsonPlaquetteData → SU2QuaternionJet4
literalPlaquetteJet4 data =
  fourLinkPlaquetteJet4
    (rightTrivializedLinkJet4 (forward0 data) (insertion0 data))
    (rightTrivializedLinkJet4 (forward1 data) (insertion1 data))
    (inverseOrientedLinkJet4 (inverse2 data) (insertion2 data))
    (inverseOrientedLinkJet4 (inverse3 data) (insertion3 data))

wilsonQuadraticNumerator wilsonCubicNumerator wilsonQuarticNumerator :
  RightTrivializedWilsonPlaquetteData → Real.ℝ
wilsonQuadraticNumerator data = -R (q0 (jet2 (literalPlaquetteJet4 data)))
wilsonCubicNumerator data = -R (q0 (jet3 (literalPlaquetteJet4 data)))
wilsonQuarticNumerator data = -R (q0 (jet4 (literalPlaquetteJet4 data)))

su2WilsonRightTrivializedFourthJetAlgebraLevel : ProofLevel
su2WilsonRightTrivializedFourthJetAlgebraLevel = machineChecked

-- Analytic leaf only: identify the literal exponential chart derivatives with
-- the powers used above.  Once supplied, quadratic/cubic/quartic plaquette
-- coefficients are all generated by one object.
su2LiteralExponentialDirectionalDerivativesThroughFourLevel : ProofLevel
su2LiteralExponentialDirectionalDerivativesThroughFourLevel = conditional
