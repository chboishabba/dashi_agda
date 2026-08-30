module DASHI.Analysis.FiniteSignedGramTelescopeExact where

------------------------------------------------------------------------
-- SCALAR-GENERIC EXACT FINITE GRAM TELESCOPE
--
-- Cross-lane extraction from NS Round180.
--
-- Round180 specialized the finite identity to rational Complex3.  RH's literal
-- three-taper response is real-valued, so reusing that rational specialization
-- directly would be a type error.  The actual algebra needed by the telescope
-- is much smaller:
--
--   * a commutative additive scalar monoid;
--   * a vector zero and vector addition;
--   * a squared-mass map;
--   * a SIGNED cross-increment;
--   * exact polarization
--
--       mass(u + v) = mass(u) + mass(v) + cross(u,v).
--
-- From only those laws we prove
--
--   mass(sum cells) = diagonalMass(cells) + gramDebt(cells).
--
-- This module is type-agnostic: NS rational Complex3 and RH real three-taper
-- cells can instantiate the same theorem without identifying R with Q.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym)

record FiniteGramCarrier : Set₁ where
  constructor finite-gram-carrier
  field
    Scalar : Set
    Vec : Set

    zeroScalar : Scalar
    addScalar : Scalar → Scalar → Scalar
    addAssoc : ∀ a b c →
      addScalar (addScalar a b) c ≡ addScalar a (addScalar b c)
    addComm : ∀ a b → addScalar a b ≡ addScalar b a
    addZeroLeft : ∀ a → addScalar zeroScalar a ≡ a

    zeroVec : Vec
    addVec : Vec → Vec → Vec

    mass : Vec → Scalar
    signedCrossIncrement : Vec → Vec → Scalar

    zeroMass : mass zeroVec ≡ zeroScalar
    polarization : ∀ u v →
      mass (addVec u v)
      ≡ addScalar
          (addScalar (mass u) (mass v))
          (signedCrossIncrement u v)

open FiniteGramCarrier public

sumCells : (C : FiniteGramCarrier) → List (Vec C) → Vec C
sumCells C [] = zeroVec C
sumCells C (u ∷ us) = addVec C u (sumCells C us)

diagonalMass : (C : FiniteGramCarrier) → List (Vec C) → Scalar C
diagonalMass C [] = zeroScalar C
diagonalMass C (u ∷ us) =
  addScalar C (mass C u) (diagonalMass C us)

gramDebt : (C : FiniteGramCarrier) → List (Vec C) → Scalar C
gramDebt C [] = zeroScalar C
gramDebt C (u ∷ us) =
  addScalar C
    (signedCrossIncrement C u (sumCells C us))
    (gramDebt C us)

-- The only scalar rearrangement needed by the induction.
ledgerReassociate :
  (C : FiniteGramCarrier) →
  (a b c d : Scalar C) →
  addScalar C (addScalar C a (addScalar C b d)) c
  ≡ addScalar C (addScalar C a b) (addScalar C c d)
ledgerReassociate C a b c d =
  trans
    (sym (addAssoc C a (addScalar C b d) c))
    (trans
      (cong (addScalar C a)
        (addAssoc C b d c))
      (trans
        (cong (addScalar C a)
          (cong (addScalar C b) (addComm C d c)))
        (sym (addAssoc C a b (addScalar C c d)))))
  where
    open import Relation.Binary.PropositionalEquality using (trans)

finiteGramLedger :
  (C : FiniteGramCarrier) →
  (cells : List (Vec C)) →
  mass C (sumCells C cells)
  ≡ addScalar C (diagonalMass C cells) (gramDebt C cells)
finiteGramLedger C []
  rewrite zeroMass C
        | addZeroLeft C (zeroScalar C) = refl
finiteGramLedger C (u ∷ us)
  rewrite polarization C u (sumCells C us)
        | finiteGramLedger C us =
  ledgerReassociate C
    (mass C u)
    (diagonalMass C us)
    (signedCrossIncrement C u (sumCells C us))
    (gramDebt C us)

finiteSignedGramTelescopeClosed : Bool
finiteSignedGramTelescopeClosed = true

finiteSignedGramTelescopeClosedIsTrue :
  finiteSignedGramTelescopeClosed ≡ true
finiteSignedGramTelescopeClosedIsTrue = refl
