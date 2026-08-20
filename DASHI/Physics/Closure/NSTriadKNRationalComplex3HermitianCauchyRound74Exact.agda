module DASHI.Physics.Closure.NSTriadKNRationalComplex3HermitianCauchyRound74Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical finite-dimensional Cauchy--Schwarz inequality; DOI not applicable.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- ROUND74 / EXACT RATIONAL C3 HERMITIAN CAUCHY
--
-- The generic Round65 interface states the correct finite complex Cauchy
-- theorem but leaves its ordered-real instantiation external.  For the exact
-- rational C3 carrier needed by the current source audit we can prove the sharp
-- three-coordinate theorem directly from the complex Lagrange identity:
--
--   ||u||^2 ||v||^2
--     = |<u,v>|^2
--       + |u1 v2-u2 v1|^2
--       + |u1 v3-u3 v1|^2
--       + |u2 v3-u3 v2|^2.
--
-- Every defect term is a literal complex modulus square and hence nonnegative.
-- Combining this with the already-proved rational Leray Pythagorean contraction
-- yields the exact response estimate used by Round74's canonical W-mass:
--
--   |<test, P_k value>|^2 <= ||test||^2 ||value||^2.
--
-- This remains a finite rational theorem.  The physical continuum/trajectory
-- carrier transport and the summed frame normalization are still separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as RationalL2
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNRationalComplex3LerayPythagoras as Leray

F : C3.RealField _
F = RationalL2.rationalRealField

complexSubtract : C3.Complex F → C3.Complex F → C3.Complex F
complexSubtract = C3.complexSubtract

complexMinor :
  C3.Complex F → C3.Complex F → C3.Complex F → C3.Complex F →
  C3.Complex F
complexMinor ui vj uj vi =
  complexSubtract
    (C3.complexMultiply ui vj)
    (C3.complexMultiply uj vi)

hermitianGramDefect : C3.Complex3 F → C3.Complex3 F → ℚ
hermitianGramDefect u v =
    L2.complexModulusSquared (complexMinor (C3.x u) (C3.y v) (C3.y u) (C3.x v))
  + L2.complexModulusSquared (complexMinor (C3.x u) (C3.z v) (C3.z u) (C3.x v))
  + L2.complexModulusSquared (complexMinor (C3.y u) (C3.z v) (C3.z u) (C3.y v))

hermitianGramIdentity : ∀ u v →
  L2.complex3NormSquared u * L2.complex3NormSquared v
  ≡
  L2.complexModulusSquared (C3.hermitianPairing3 u v)
  + hermitianGramDefect u v
hermitianGramIdentity
  (C3.complex3
    (C3.complex ur1 ui1) (C3.complex ur2 ui2) (C3.complex ur3 ui3))
  (C3.complex3
    (C3.complex vr1 vi1) (C3.complex vr2 vi2) (C3.complex vr3 vi3)) =
  solve
    ( ur1 ∷ ui1 ∷ ur2 ∷ ui2 ∷ ur3 ∷ ui3
    ∷ vr1 ∷ vi1 ∷ vr2 ∷ vi2 ∷ vr3 ∷ vi3 ∷ [] )

hermitianGramDefectNonnegative : ∀ u v →
  0ℚ ≤ hermitianGramDefect u v
hermitianGramDefectNonnegative u v =
  RationalL2.addNonnegative
    (RationalL2.addNonnegative
      (Separation.complexModulusSquaredNonnegative
        (complexMinor (C3.x u) (C3.y v) (C3.y u) (C3.x v)))
      (Separation.complexModulusSquaredNonnegative
        (complexMinor (C3.x u) (C3.z v) (C3.z u) (C3.x v))))
    (Separation.complexModulusSquaredNonnegative
      (complexMinor (C3.y u) (C3.z v) (C3.z u) (C3.y v)))

rationalComplex3HermitianCauchy : ∀ u v →
  L2.complexModulusSquared (C3.hermitianPairing3 u v)
  ≤ L2.complex3NormSquared u * L2.complex3NormSquared v
rationalComplex3HermitianCauchy u v =
  let
    innerMass = L2.complexModulusSquared (C3.hermitianPairing3 u v)
    defect = hermitianGramDefect u v
    addDefect : innerMass ≤ innerMass + defect
    addDefect =
      subst
        (λ lower → lower ≤ innerMass + defect)
        (ℚP.+-identityʳ innerMass)
        (ℚP.+-monoʳ-≤ innerMass (hermitianGramDefectNonnegative u v))
  in
  subst
    (λ upper → innerMass ≤ upper)
    (sym (hermitianGramIdentity u v))
    addDefect

productMonotoneRightNonnegative :
  ∀ {left lower upper : ℚ} →
  0ℚ ≤ left → lower ≤ upper →
  left * lower ≤ left * upper
productMonotoneRightNonnegative {left} leftNN lower≤upper =
  let instance leftNNI = nonNegative leftNN
  in ℚP.*-monoˡ-≤-nonNeg left lower≤upper

rationalTestedLerayResponseBound :
  ∀ (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (O : Leray.RationalInverseNormOrder E I)
    (mode : Z3.FourierMode)
    (test value : C3.Complex3 F) →
  (nonzero : Z3.NonZeroMode mode) →
  L2.complexModulusSquared
    (C3.hermitianPairing3 test (C3.lerayProject3 E I mode value))
  ≤ L2.complex3NormSquared test * L2.complex3NormSquared value
rationalTestedLerayResponseBound E I O mode test value nonzero =
  let
    projected = C3.lerayProject3 E I mode value
    cauchy = rationalComplex3HermitianCauchy test projected
    projectedContraction =
      Leray.rationalLerayNormSquaredContraction E I O mode value nonzero
    testNN = Separation.complex3NormSquaredNonnegative test
    scaled = productMonotoneRightNonnegative testNN projectedContraction
  in
  ℚP.≤-trans cauchy scaled

round74RationalComplex3HermitianCauchyConstructed : Bool
round74RationalComplex3HermitianCauchyConstructed = true

round74RationalTestedLerayResponseEnergyBoundConstructed : Bool
round74RationalTestedLerayResponseEnergyBoundConstructed = true

round74ContinuumPhysicalResponseFrameTransportConstructed : Bool
round74ContinuumPhysicalResponseFrameTransportConstructed = false

round74RationalTestedLerayResponseEnergyBoundConstructedIsTrue :
  round74RationalTestedLerayResponseEnergyBoundConstructed ≡ true
round74RationalTestedLerayResponseEnergyBoundConstructedIsTrue = refl
