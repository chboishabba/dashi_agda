module DASHI.Physics.YangMills.BalabanSelectedFlatGaugeSectionAsymmetryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Exhibit the asymmetry of the flat gauge quotient/section concretely.  The
-- based section maps a nonzero constant gauge multiplier pointwise to the zero
-- representative.  Hence selecting a representative after quotienting is not
-- the identity on the unreduced carrier: information along the redundant
-- constant direction has really been discarded.
--
-- This is the finite gauge-theory realization of the section identity
-- pi o s = id on quotient classes together with the generally false converse
-- s o pi = id on unreduced representatives.  No claim is made that the same
-- constant fibre describes a noncentral background; the holonomy guard and
-- stabilizer-stratification theorem explicitly forbid that shortcut.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _<_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open ℚP using (_<?_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Nullary.Negation.Core using (¬_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeBasedSectionExact as Based

unitConstantMultiplier : Based.GaugeMultiplier
unitConstantMultiplier row = 1ℚ

unitConstantBasedRepresentativePointwiseZero :
  ∀ coordinate site →
  Based.basedRepresentative unitConstantMultiplier (pair coordinate site)
  ≡ 0ℚ
unitConstantBasedRepresentativePointwiseZero coordinate site = ℚRing.solve []

unitConstantBasedAtBaseZero :
  Based.basedRepresentative unitConstantMultiplier
    (pair Coordinates.coordinateX Based.baseSite)
  ≡ 0ℚ
unitConstantBasedAtBaseZero =
  unitConstantBasedRepresentativePointwiseZero
    Coordinates.coordinateX Based.baseSite

unitConstantAtBaseOne :
  unitConstantMultiplier (pair Coordinates.coordinateX Based.baseSite) ≡ 1ℚ
unitConstantAtBaseOne = refl

zeroLessOne : 0ℚ < 1ℚ
zeroLessOne = toWitness {a? = 0ℚ <? 1ℚ} _

basedSectionNotIdentityOnUnreducedCarrier :
  ¬ (∀ row →
    Based.basedRepresentative unitConstantMultiplier row
    ≡ unitConstantMultiplier row)
basedSectionNotIdentityOnUnreducedCarrier sectionIdentity =
  let
    atBase = sectionIdentity (pair Coordinates.coordinateX Based.baseSite)

    zeroEqualsOne : 0ℚ ≡ 1ℚ
    zeroEqualsOne =
      trans
        (sym unitConstantBasedAtBaseZero)
        (trans atBase unitConstantAtBaseOne)

    impossible : 0ℚ < 0ℚ
    impossible =
      subst (λ value → 0ℚ < value) (sym zeroEqualsOne) zeroLessOne
  in
  ℚP.<-irrefl 0ℚ impossible

unitConstantEquivalentToZeroBasedRepresentative :
  Based.FlatConstantGaugeEquivalent
    unitConstantMultiplier (Based.basedRepresentative unitConstantMultiplier)
unitConstantEquivalentToZeroBasedRepresentative =
  Based.originalEquivalentToBased unitConstantMultiplier

selectedFlatGaugeSectionAsymmetryLevel : ProofLevel
selectedFlatGaugeSectionAsymmetryLevel = machineChecked
