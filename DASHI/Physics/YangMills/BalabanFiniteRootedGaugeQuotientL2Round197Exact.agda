{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFiniteRootedGaugeQuotientL2Round197Exact where

------------------------------------------------------------------------
-- ROUND197 BIDI / X-POLLINATION: FINITE SELECTED-ENSEMBLE L2 ON THE ACTUAL
-- ROOTED GAUGE-QUOTIENT CARRIER.
--
-- R196 constructs the set-level rooted quotient carrier.  Round42 and the NS
-- finite-L2 lane already prove exact rational finite-selector definiteness.
-- Reuse that theorem on observable functions over a proof-bearing finite
-- ensemble of R196 quotient representatives.
--
-- This is deliberately NOT a claim that the full compact-group configuration
-- quotient is finite.  It is the exact finite selected-ensemble/pre-Hilbert
-- layer used by finite RG sums.  Haar/Gibbs L2 completion remains separate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (NonZero)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using (Cube4)
import DASHI.Physics.YangMills.BalabanPeriodicGaugeTransport as Transport
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSelectorL2DefinitenessExact as Definite
import DASHI.Physics.YangMills.BalabanFinitePhysicalGaugeQuotientCarrierRound196Exact as R196

QuotientObservable :
  ∀ {N : Nat} {{_ : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact.RootedPathSystem base} →
  Set
QuotientObservable {group = group} {base = base} {paths = paths} =
  R196.FiniteRootedGaugeQuotientCarrier group base paths → ℚ

record FiniteRootedQuotientEnsemble
    {N : Nat} {{_ : NonZero N}}
    (group : Transport.GroupStructure)
    (base : Cube4 N)
    (paths : DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact.RootedPathSystem base) : Set₁ where
  field
    selector : Basis.FiniteSelector
      (R196.FiniteRootedGaugeQuotientCarrier group base paths)

open FiniteRootedQuotientEnsemble public

finiteQuotientPairing :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact.RootedPathSystem base} →
  FiniteRootedQuotientEnsemble group base paths →
  QuotientObservable {group = group} {base = base} {paths = paths} →
  QuotientObservable {group = group} {base = base} {paths = paths} →
  ℚ
finiteQuotientPairing ensemble left right =
  Sums.sumRational (Basis.elements (selector ensemble))
    (λ state → left state * right state)

finiteQuotientNormSq :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact.RootedPathSystem base} →
  FiniteRootedQuotientEnsemble group base paths →
  QuotientObservable {group = group} {base = base} {paths = paths} →
  ℚ
finiteQuotientNormSq ensemble observable =
  finiteQuotientPairing ensemble observable observable

finiteQuotientNormIsExistingSelectorNorm :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact.RootedPathSystem base}
    (ensemble : FiniteRootedQuotientEnsemble group base paths)
    observable →
  finiteQuotientNormSq ensemble observable
  ≡ Definite.finiteSelectorNormSq (selector ensemble) observable
finiteQuotientNormIsExistingSelectorNorm ensemble observable =
  Sums.sumRationalCong (Basis.elements (selector ensemble)) _ _
    (λ state → ℚP.*-comm (observable state) (observable state))

finiteQuotientPairingSymmetric :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact.RootedPathSystem base}
    (ensemble : FiniteRootedQuotientEnsemble group base paths)
    left right →
  finiteQuotientPairing ensemble left right
  ≡ finiteQuotientPairing ensemble right left
finiteQuotientPairingSymmetric ensemble left right =
  Sums.sumRationalCong (Basis.elements (selector ensemble)) _ _
    (λ state → ℚP.*-comm (left state) (right state))

finiteQuotientPairingAdditiveLeft :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact.RootedPathSystem base}
    (ensemble : FiniteRootedQuotientEnsemble group base paths)
    left middle right →
  finiteQuotientPairing ensemble
    (λ state → left state + middle state) right
  ≡ finiteQuotientPairing ensemble left right
    + finiteQuotientPairing ensemble middle right
finiteQuotientPairingAdditiveLeft ensemble left middle right =
  let
    values = Basis.elements (selector ensemble)
  in
  trans
    (Sums.sumRationalCong values _ _
      (λ state → ℚRing.solve-∀
        (left state) (middle state) (right state)))
    (Sums.sumRationalAdd values
      (λ state → left state * right state)
      (λ state → middle state * right state))

finiteQuotientNormZeroPointwise :
  ∀ {N} {{nz : NonZero N}}
    {group : Transport.GroupStructure}
    {base : Cube4 N}
    {paths : DASHI.Physics.YangMills.BalabanBasedPathGaugeSectionExact.RootedPathSystem base}
    (ensemble : FiniteRootedQuotientEnsemble group base paths)
    observable →
  finiteQuotientNormSq ensemble observable ≡ 0ℚ →
  ∀ state → observable state ≡ 0ℚ
finiteQuotientNormZeroPointwise ensemble observable normZero =
  Definite.finiteSelectorNormZeroPointwise
    (selector ensemble) observable
    (trans
      (sym (finiteQuotientNormIsExistingSelectorNorm ensemble observable))
      normZero)
  where
    open import Relation.Binary.PropositionalEquality using (sym)

finiteRootedGaugeQuotientL2PairingRound197Level : ProofLevel
finiteRootedGaugeQuotientL2PairingRound197Level = machineChecked

finiteRootedGaugeQuotientL2DefinitenessRound197Level : ProofLevel
finiteRootedGaugeQuotientL2DefinitenessRound197Level = machineChecked

-- Exact remaining analytic seam: replace the selected finite ensemble/counting
-- pairing by the physical invariant Haar/Gibbs measure on the same quotient
-- carrier, then complete the resulting L2 space.  R197 does not claim that step.
literalPhysicalGaugeQuotientInvariantMeasureRound197Level : ProofLevel
literalPhysicalGaugeQuotientInvariantMeasureRound197Level = conditional

literalPhysicalGaugeQuotientL2CompletionRound197Level : ProofLevel
literalPhysicalGaugeQuotientL2CompletionRound197Level = conditional
