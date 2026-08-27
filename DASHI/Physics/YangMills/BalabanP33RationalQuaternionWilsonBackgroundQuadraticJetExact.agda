module DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonBackgroundQuadraticJetExact where

------------------------------------------------------------------------
-- ROW A1: EXACT MIXED THIRD WILSON PRODUCT JET
--
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- The Gaussian Wilson source term A'(U) is the background derivative of the
-- Wilson Hessian.  For one background parameter s and one fluctuation
-- parameter t, the relevant plaquette coefficient is therefore
--
--       d/ds d^2/dt^2  U_p(s,t) |_(0,0).
--
-- Existing quaternion owners stop at the t^2 jet and therefore prove the 16
-- placements of the ordinary Hessian.  This owner adds the exact noncommutative
-- product recursion for the mixed s t^2 jet.  Every one of the three labelled
-- derivatives chooses one of four ordered plaquette factors, so the four-link
-- product has exactly 4^3 = 64 Leibniz placements.
--
-- This file owns only the generic ordered-product algebra.  The physical
-- right-exponential values of the six factor jets (s, t, tt, st, stt) are a
-- separate source-facing producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (map; _++_; length)
open import Data.Rational.Base as ℚ using (ℚ; -_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonJetExact as Jet

record QuaternionBackgroundQuadraticFactorJet : Set where
  constructor mixedFactorJet
  field
    factorValue : Jet.RationalQuaternion
    factorBackground : Jet.RationalQuaternion
    factorFluctuation : Jet.RationalQuaternion
    factorFluctuationSecond : Jet.RationalQuaternion
    factorBackgroundFluctuation : Jet.RationalQuaternion
    factorBackgroundFluctuationSecond : Jet.RationalQuaternion

open QuaternionBackgroundQuadraticFactorJet public

orderedValueProduct : List QuaternionBackgroundQuadraticFactorJet → Jet.RationalQuaternion
orderedValueProduct [] = Jet.oneQ
orderedValueProduct (factor ∷ factors) =
  factorValue factor Jet.*q orderedValueProduct factors

orderedBackgroundProduct : List QuaternionBackgroundQuadraticFactorJet → Jet.RationalQuaternion
orderedBackgroundProduct [] = Jet.zeroQ
orderedBackgroundProduct (factor ∷ factors) =
  (factorBackground factor Jet.*q orderedValueProduct factors)
  Jet.+q (factorValue factor Jet.*q orderedBackgroundProduct factors)

orderedFluctuationProduct : List QuaternionBackgroundQuadraticFactorJet → Jet.RationalQuaternion
orderedFluctuationProduct [] = Jet.zeroQ
orderedFluctuationProduct (factor ∷ factors) =
  (factorFluctuation factor Jet.*q orderedValueProduct factors)
  Jet.+q (factorValue factor Jet.*q orderedFluctuationProduct factors)

orderedFluctuationSecondProduct :
  List QuaternionBackgroundQuadraticFactorJet → Jet.RationalQuaternion
orderedFluctuationSecondProduct [] = Jet.zeroQ
orderedFluctuationSecondProduct (factor ∷ factors) =
  (factorFluctuationSecond factor Jet.*q orderedValueProduct factors)
  Jet.+q
    (((factorFluctuation factor Jet.*q orderedFluctuationProduct factors)
      Jet.+q (factorFluctuation factor Jet.*q orderedFluctuationProduct factors))
      Jet.+q (factorValue factor Jet.*q orderedFluctuationSecondProduct factors))

orderedBackgroundFluctuationProduct :
  List QuaternionBackgroundQuadraticFactorJet → Jet.RationalQuaternion
orderedBackgroundFluctuationProduct [] = Jet.zeroQ
orderedBackgroundFluctuationProduct (factor ∷ factors) =
  (factorBackgroundFluctuation factor Jet.*q orderedValueProduct factors)
  Jet.+q
    ((factorBackground factor Jet.*q orderedFluctuationProduct factors)
      Jet.+q
      ((factorFluctuation factor Jet.*q orderedBackgroundProduct factors)
        Jet.+q
        (factorValue factor Jet.*q orderedBackgroundFluctuationProduct factors)))

orderedBackgroundFluctuationSecondProduct :
  List QuaternionBackgroundQuadraticFactorJet → Jet.RationalQuaternion
orderedBackgroundFluctuationSecondProduct [] = Jet.zeroQ
orderedBackgroundFluctuationSecondProduct (factor ∷ factors) =
  (factorBackgroundFluctuationSecond factor Jet.*q orderedValueProduct factors)
  Jet.+q
    ((factorFluctuationSecond factor Jet.*q orderedBackgroundProduct factors)
      Jet.+q
      ((factorBackgroundFluctuation factor Jet.*q orderedFluctuationProduct factors)
        Jet.+q
        ((factorBackgroundFluctuation factor Jet.*q orderedFluctuationProduct factors)
          Jet.+q
          ((factorFluctuation factor Jet.*q orderedBackgroundFluctuationProduct factors)
            Jet.+q
            ((factorFluctuation factor Jet.*q orderedBackgroundFluctuationProduct factors)
              Jet.+q
              ((factorBackground factor Jet.*q orderedFluctuationSecondProduct factors)
                Jet.+q
                (factorValue factor Jet.*q
                  orderedBackgroundFluctuationSecondProduct factors)))))))

------------------------------------------------------------------------
-- Explicit Leibniz atoms.  The recurrence mirrors the derivative formula
-- above and exposes the finite 4^3 placement count used by physical consumers.
------------------------------------------------------------------------

backgroundTerms :
  List QuaternionBackgroundQuadraticFactorJet → List Jet.RationalQuaternion
backgroundTerms [] = []
backgroundTerms (factor ∷ factors) =
  (factorBackground factor Jet.*q orderedValueProduct factors)
  ∷ map (factorValue factor Jet.*q_) (backgroundTerms factors)

fluctuationTerms :
  List QuaternionBackgroundQuadraticFactorJet → List Jet.RationalQuaternion
fluctuationTerms [] = []
fluctuationTerms (factor ∷ factors) =
  (factorFluctuation factor Jet.*q orderedValueProduct factors)
  ∷ map (factorValue factor Jet.*q_) (fluctuationTerms factors)

fluctuationSecondTerms :
  List QuaternionBackgroundQuadraticFactorJet → List Jet.RationalQuaternion
fluctuationSecondTerms [] = []
fluctuationSecondTerms (factor ∷ factors) =
  (factorFluctuationSecond factor Jet.*q orderedValueProduct factors)
  ∷ (map (factorFluctuation factor Jet.*q_) (fluctuationTerms factors)
    ++ (map (factorFluctuation factor Jet.*q_) (fluctuationTerms factors)
      ++ map (factorValue factor Jet.*q_) (fluctuationSecondTerms factors)))

backgroundFluctuationTerms :
  List QuaternionBackgroundQuadraticFactorJet → List Jet.RationalQuaternion
backgroundFluctuationTerms [] = []
backgroundFluctuationTerms (factor ∷ factors) =
  (factorBackgroundFluctuation factor Jet.*q orderedValueProduct factors)
  ∷ (map (factorBackground factor Jet.*q_) (fluctuationTerms factors)
    ++ (map (factorFluctuation factor Jet.*q_) (backgroundTerms factors)
      ++ map (factorValue factor Jet.*q_) (backgroundFluctuationTerms factors)))

backgroundFluctuationSecondTerms :
  List QuaternionBackgroundQuadraticFactorJet → List Jet.RationalQuaternion
backgroundFluctuationSecondTerms [] = []
backgroundFluctuationSecondTerms (factor ∷ factors) =
  (factorBackgroundFluctuationSecond factor Jet.*q orderedValueProduct factors)
  ∷ (map (factorFluctuationSecond factor Jet.*q_) (backgroundTerms factors)
    ++ (map (factorBackgroundFluctuation factor Jet.*q_) (fluctuationTerms factors)
      ++ (map (factorBackgroundFluctuation factor Jet.*q_) (fluctuationTerms factors)
        ++ (map (factorFluctuation factor Jet.*q_) (backgroundFluctuationTerms factors)
          ++ (map (factorFluctuation factor Jet.*q_) (backgroundFluctuationTerms factors)
            ++ (map (factorBackground factor Jet.*q_) (fluctuationSecondTerms factors)
              ++ map (factorValue factor Jet.*q_)
                   (backgroundFluctuationSecondTerms factors)))))))

fourFactorJets :
  QuaternionBackgroundQuadraticFactorJet →
  QuaternionBackgroundQuadraticFactorJet →
  QuaternionBackgroundQuadraticFactorJet →
  QuaternionBackgroundQuadraticFactorJet →
  List QuaternionBackgroundQuadraticFactorJet
fourFactorJets first second third fourth = first ∷ second ∷ third ∷ fourth ∷ []

fourFactorBackgroundFluctuationSecondAtomCountExact :
  ∀ first second third fourth →
  length (backgroundFluctuationSecondTerms
    (fourFactorJets first second third fourth)) ≡ 64
fourFactorBackgroundFluctuationSecondAtomCountExact first second third fourth = refl

------------------------------------------------------------------------
-- Wilson scalar numerator: S_p = 1 - q0(U_p), so every nonconstant variation
-- carries the scalar coefficient -q0 of the corresponding product derivative.
------------------------------------------------------------------------

wilsonBackgroundFluctuationSecondNumerator :
  List QuaternionBackgroundQuadraticFactorJet → ℚ
wilsonBackgroundFluctuationSecondNumerator factors =
  - Jet.q0 (orderedBackgroundFluctuationSecondProduct factors)

wilsonBackgroundFluctuationSecondAtomSum :
  List QuaternionBackgroundQuadraticFactorJet → ℚ
wilsonBackgroundFluctuationSecondAtomSum factors =
  Jet.sumRational
    (map Jet.wilsonAtomContribution
      (backgroundFluctuationSecondTerms factors))

------------------------------------------------------------------------
-- Proof levels / source boundary
------------------------------------------------------------------------

wilsonBackgroundQuadraticProductJetLevel : ProofLevel
wilsonBackgroundQuadraticProductJetLevel = machineChecked

wilsonBackgroundQuadraticFourFactor64AtomLevel : ProofLevel
wilsonBackgroundQuadraticFourFactor64AtomLevel = machineChecked

-- Still open: prove the finite atom sum equals the recursive mixed product and
-- instantiate every physical right-exponential link factor from the literal
-- background/fluctuation coordinates.  These are intentionally distinct seams.
wilsonBackgroundQuadraticAtomSumIdentityLevel : ProofLevel
wilsonBackgroundQuadraticAtomSumIdentityLevel = conditional

wilsonPhysicalBackgroundQuadraticLinkJetLevel : ProofLevel
wilsonPhysicalBackgroundQuadraticLinkJetLevel = conditional
