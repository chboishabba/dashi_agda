module DASHI.Analysis.NonArchimedeanContinuousGibbsUniquenessBidiExact where

------------------------------------------------------------------------
-- CONTINUOUS GIBBS UNIQUENESS BIDI
--
-- ContinuousTransfer.lean owns:
--   * IsConformalGibbs;
--   * IsMarkovInvariant;
--   * gibbs_iff_markov_invariant;
--   * branch invariance -> Gibbs;
--   * a measure-level Gibbs identity conditional on branch integral invariance.
--
-- The README/monograph strengthens this to uniqueness of normalized Haar.
-- No source theorem proving that every conformal Gibbs state equals Haar was
-- located in the audited formalization.  Uniqueness is therefore its own leaf.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record GibbsSourceAudit : Set where
  constructor gibbsSourceAudit
  field
    gibbsPredicateOwned : Bool
    markovInvariantPredicateOwned : Bool
    gibbsIffMarkovInvariantOwned : Bool
    branchInvariantImpliesGibbsOwned : Bool
    measureGibbsIdentityOwnedConditionally : Bool
    haarExistenceAsGibbsEnoughForUniqueness : Bool
    allGibbsStatesEqualHaarTheoremLocated : Bool

canonicalGibbsSourceAudit : GibbsSourceAudit
canonicalGibbsSourceAudit =
  gibbsSourceAudit true true true true true false false

record GibbsUniquenessProducer : Set₁ where
  field
    State : Set
    Haar : State
    IsGibbs : State → Set
    haarIsGibbs : IsGibbs Haar
    unique : (state : State) → IsGibbs state → state ≡ Haar

open GibbsUniquenessProducer public

record GibbsFirewall : Set where
  constructor gibbsFirewall
  field
    invarianceImpliesUniqueness : Bool
    existenceImpliesUniqueness : Bool
    ergodicityMayBeOmittedFromUniquenessRoute : Bool
    uniquenessNeedsDedicatedProducer : Bool

canonicalGibbsFirewall : GibbsFirewall
canonicalGibbsFirewall =
  gibbsFirewall false false false true

invarianceDoesNotCloseUniqueness :
  GibbsFirewall.invarianceImpliesUniqueness canonicalGibbsFirewall ≡ false
invarianceDoesNotCloseUniqueness = refl

uniquenessProducerStillLive :
  GibbsSourceAudit.allGibbsStatesEqualHaarTheoremLocated
    canonicalGibbsSourceAudit
  ≡ false
uniquenessProducerStillLive = refl
