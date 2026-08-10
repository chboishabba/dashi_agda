module DASHI.Physics.Closure.NSTriadKNCanonicalVelocityRealityRound35Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Close the remaining reality seam in the Round-33 executable same-object
-- velocity lookup.  The state stores positive representatives; the negative
-- sheet is reconstructed by conjugation, while the executable lookup gives
-- priority to a positive representative when the two sheets overlap.
--
-- `SameObjectCompatibleState` contains exactly the two coherence laws needed
-- for that priority rule to be harmless.  Round 35 proves globally, including
-- modes outside the retained support,
--
--   literalVelocityAt(-k) = conjugate(literalVelocityAt(k)).
--
-- The outside-support case is not assumed: if neither k nor -k is a positive
-- representative then both negative lookups are proved to be zero.  Thus the
-- canonical finite-system velocity now carries a literal Fourier reality
-- theorem, rather than a marker field.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as State
import DASHI.Physics.Closure.NSTriadKNSameObjectLookupConsistencyRound33Exact as Lookup

falseCannotEqualTrue : false ≡ true → ⊥
falseCannotEqualTrue ()

complex3ConjugateZero :
  ∀ {r} {F : C3.RealField r} →
  C3.complex3Conjugate (C3.complex3Zero F) ≡ C3.complex3Zero F
complex3ConjugateZero {F = F}
  rewrite C3.negateZero F = refl

negatedEqualityToPositive :
  ∀ {mode positive} →
  mode ≡ Z3.negateMode positive →
  Z3.negateMode mode ≡ positive
negatedEqualityToPositive {mode} {positive} equality =
  trans
    (cong Z3.negateMode equality)
    (Symmetry.negateModeInvolutive positive)

positiveAtNegationFromNegativeHit :
  ∀ {mode positive} →
  Output.modeEqual mode (Z3.negateMode positive) ≡ true →
  Output.modeEqual (Z3.negateMode mode) positive ≡ true
positiveAtNegationFromNegativeHit negativeHit =
  Output.modeEqualComplete
    (negatedEqualityToPositive (Output.modeEqualSound negativeHit))

lookupNegativeZeroFromOppositePositiveAbsent :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (coefficients : List (Phase.TransverseModeCoefficient F E))
    (mode : Z3.FourierMode) →
  Lookup.positiveModeOccurs coefficients (Z3.negateMode mode) ≡ false →
  Lookup.lookupNegative coefficients mode ≡ C3.complex3Zero F
lookupNegativeZeroFromOppositePositiveAbsent [] mode absent = refl
lookupNegativeZeroFromOppositePositiveAbsent
    (head ∷ rest) mode absent
  with Output.modeEqual
    (Z3.negateMode mode) (Phase.coefficientMode head)
... | true = ⊥-elim (falseCannotEqualTrue (sym absent))
... | false
  with Output.modeEqual mode (Phase.reconstructedNegativeMode head)
...   | true =
      ⊥-elim
        (falseCannotEqualTrue
          (positiveAtNegationFromNegativeHit refl))
...   | false =
      lookupNegativeZeroFromOppositePositiveAbsent rest mode absent

literalVelocityZeroIfNeitherPositive :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (compatibility : Lookup.SameObjectCompatibleState F E state)
    (mode : Z3.FourierMode) →
  Lookup.positiveModeOccurs
    (State.positiveOrbitCoefficients state) mode ≡ false →
  Lookup.positiveModeOccurs
    (State.positiveOrbitCoefficients state) (Z3.negateMode mode) ≡ false →
  Lookup.literalVelocityAt compatibility mode ≡ C3.complex3Zero F
literalVelocityZeroIfNeitherPositive {state = state}
    compatibility mode noPositive noOpposite
  rewrite noPositive =
  lookupNegativeZeroFromOppositePositiveAbsent
    (State.positiveOrbitCoefficients state) mode noOpposite

literalVelocityAtPositiveHit :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (compatibility : Lookup.SameObjectCompatibleState F E state)
    {mode : Z3.FourierMode} →
  Lookup.PositiveModeHit
    (State.positiveOrbitCoefficients state) mode →
  C3.Complex3 F
literalVelocityAtPositiveHit compatibility
    (Lookup.positive-mode-hit coefficient member sameMode) =
  Phase.coefficientValue coefficient

literalVelocityPositiveHitExact :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (compatibility : Lookup.SameObjectCompatibleState F E state)
    {mode : Z3.FourierMode}
    (hit : Lookup.PositiveModeHit
      (State.positiveOrbitCoefficients state) mode) →
  Lookup.literalVelocityAt compatibility mode
  ≡ literalVelocityAtPositiveHit compatibility hit
literalVelocityPositiveHitExact compatibility
    (Lookup.positive-mode-hit coefficient member sameMode) =
  trans
    (cong (Lookup.literalVelocityAt compatibility) sameMode)
    (Lookup.literalVelocityAtPositiveExact
      compatibility coefficient member)

literalVelocityNegativeOfPositiveHitExact :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (compatibility : Lookup.SameObjectCompatibleState F E state)
    {mode : Z3.FourierMode}
    (hit : Lookup.PositiveModeHit
      (State.positiveOrbitCoefficients state) mode) →
  Lookup.literalVelocityAt compatibility (Z3.negateMode mode)
  ≡ C3.complex3Conjugate
      (literalVelocityAtPositiveHit compatibility hit)
literalVelocityNegativeOfPositiveHitExact compatibility
    (Lookup.positive-mode-hit coefficient member sameMode) =
  trans
    (cong
      (Lookup.literalVelocityAt compatibility)
      (cong Z3.negateMode sameMode))
    (Lookup.literalVelocityAtNegativeExact
      compatibility coefficient member)

literalVelocityReality :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (compatibility : Lookup.SameObjectCompatibleState F E state) →
  Reality.RealityCondition (Lookup.literalVelocityAt compatibility)
literalVelocityReality {F = F} {state = state} compatibility mode
  with Lookup.positiveModeOccurs
    (State.positiveOrbitCoefficients state) mode
... | true
  with Lookup.positiveModeOccursSound
    {coefficients = State.positiveOrbitCoefficients state}
    {mode = mode} refl
...   | hit =
      trans
        (literalVelocityNegativeOfPositiveHitExact compatibility hit)
        (sym
          (cong C3.complex3Conjugate
            (literalVelocityPositiveHitExact compatibility hit)))
... | false
  with Lookup.positiveModeOccurs
    (State.positiveOrbitCoefficients state) (Z3.negateMode mode)
...   | true
  with Lookup.positiveModeOccursSound
    {coefficients = State.positiveOrbitCoefficients state}
    {mode = Z3.negateMode mode} refl
...     | hit =
      let
        positiveAtNegation :
          Lookup.literalVelocityAt compatibility (Z3.negateMode mode)
          ≡ literalVelocityAtPositiveHit compatibility hit
        positiveAtNegation =
          literalVelocityPositiveHitExact compatibility hit

        originalAsNegative :
          Lookup.literalVelocityAt compatibility mode
          ≡ C3.complex3Conjugate
              (literalVelocityAtPositiveHit compatibility hit)
        originalAsNegative =
          trans
            (cong
              (Lookup.literalVelocityAt compatibility)
              (sym (Symmetry.negateModeInvolutive mode)))
            (literalVelocityNegativeOfPositiveHitExact compatibility hit)

        conjugatedOriginal :
          C3.complex3Conjugate
            (Lookup.literalVelocityAt compatibility mode)
          ≡ literalVelocityAtPositiveHit compatibility hit
        conjugatedOriginal =
          trans
            (cong C3.complex3Conjugate originalAsNegative)
            (C3.complex3ConjugateInvolutive
              (literalVelocityAtPositiveHit compatibility hit))
      in
      trans positiveAtNegation (sym conjugatedOriginal)
...   | false =
      let
        noDoublePositive :
          Lookup.positiveModeOccurs
            (State.positiveOrbitCoefficients state)
            (Z3.negateMode (Z3.negateMode mode))
          ≡ false
        noDoublePositive =
          trans
            (cong
              (Lookup.positiveModeOccurs
                (State.positiveOrbitCoefficients state))
              (Symmetry.negateModeInvolutive mode))
            refl

        negativeZero :
          Lookup.literalVelocityAt compatibility (Z3.negateMode mode)
          ≡ C3.complex3Zero F
        negativeZero =
          literalVelocityZeroIfNeitherPositive
            compatibility (Z3.negateMode mode) refl noDoublePositive

        originalZero :
          Lookup.literalVelocityAt compatibility mode
          ≡ C3.complex3Zero F
        originalZero =
          literalVelocityZeroIfNeitherPositive
            compatibility mode refl refl
      in
      trans
        negativeZero
        (sym
          (trans
            (cong C3.complex3Conjugate originalZero)
            complex3ConjugateZero))

canonicalVelocityRealityClosed : Bool
canonicalVelocityRealityClosed = true

canonicalVelocityRealityClosedIsTrue :
  canonicalVelocityRealityClosed ≡ true
canonicalVelocityRealityClosedIsTrue = refl
