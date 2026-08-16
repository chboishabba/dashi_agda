module DASHI.Physics.YangMills.BalabanCMP109LeftRightInverseDexpCancellationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- DASHI CONTRIBUTION
--
-- Remove the algebraic part of the remaining CMP109 Federbush convention
-- receipt.  The source centre leg uses the opposite trivialisation.  If the
-- two differentials are related by
--
--        dexp+ = Ad_exp o dexp-
--
-- and J+ is a left inverse of dexp+ while J- is a right inverse of dexp-,
-- then inverse uniqueness forces
--
--        J+ o Ad_exp = J-.
--
-- This is exactly the identity required by the printed equation-(0.11)
-- cancellation.  Importantly, the identity is DERIVED here; it is not a field
-- of the source dictionary.  The only remaining physical obligation is now
-- the literal source identification of the two trivialisations and their
-- derivative/inverse laws.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4SU2DexpInverseClosedFormExact as Dexp

record LeftRightDexpCancellationData (Lie : Set) : Set₁ where
  field
    dexpPlus dexpMinus : Dexp.Endomorphism Lie
    Jplus Jminus : Dexp.Endomorphism Lie
    adjointExp : Dexp.Endomorphism Lie

    -- Source left/right trivialisation relation.
    plusIsAdjointOfMinus : ∀ vector →
      dexpPlus vector ≡ adjointExp (dexpMinus vector)

    -- Only the inverse directions needed by inverse uniqueness.
    JplusAfterDexpPlus : ∀ vector →
      Jplus (dexpPlus vector) ≡ vector

    dexpMinusAfterJminus : ∀ vector →
      dexpMinus (Jminus vector) ≡ vector

open LeftRightDexpCancellationData public

JplusAdjointAfterDexpMinus :
  ∀ {Lie} (dataSet : LeftRightDexpCancellationData Lie) vector →
  Jplus dataSet (adjointExp dataSet (dexpMinus dataSet vector)) ≡ vector
JplusAdjointAfterDexpMinus dataSet vector =
  trans
    (cong (Jplus dataSet) (sym (plusIsAdjointOfMinus dataSet vector)))
    (JplusAfterDexpPlus dataSet vector)

leftRightInverseDexpCancellation :
  ∀ {Lie} (dataSet : LeftRightDexpCancellationData Lie) vector →
  Jplus dataSet (adjointExp dataSet vector) ≡ Jminus dataSet vector
leftRightInverseDexpCancellation dataSet =
  Dexp.inverseUniquePointwise
    (dexpMinus dataSet)
    (λ vector → Jplus dataSet (adjointExp dataSet vector))
    (Jminus dataSet)
    (dexpMinusAfterJminus dataSet)
    (JplusAdjointAfterDexpMinus dataSet)

centreLegCancellation :
  ∀ {Lie} (dataSet : LeftRightDexpCancellationData Lie) vector →
  Jplus dataSet (adjointExp dataSet vector) ≡ Jminus dataSet vector
centreLegCancellation = leftRightInverseDexpCancellation

cmp109LeftRightDexpCancellationAlgebraLevel : ProofLevel
cmp109LeftRightDexpCancellationAlgebraLevel = machineChecked

-- This is deliberately the only remaining source-facing leaf: instantiate the
-- record with the literal CMP98/CMP109 trivialisation conventions.
cmp109LiteralLeftRightDexpIdentificationLevel : ProofLevel
cmp109LiteralLeftRightDexpIdentificationLevel = conditional
