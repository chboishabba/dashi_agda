module DASHI.Core.RelationalRoleGrammarExact where

------------------------------------------------------------------------
-- RELATIONAL ROLE / DEPENDENCY / OBSERVER GEOMETRY
--
-- INTERNAL THEOREM-PATTERN PROVENANCE
--
-- This owner extracts a common seam already visible across draft PRs #603,
-- #617, #620, #621 and #622:
--
--   same carrier/cardinality != same role semantics
--   same role labels          != same dependency grammar
--   same grammar              != same observer
--   same observation          != same downstream valuation
--   pair-valued syntax        != genuine relational/nonseparable structure
--
-- No historical author is credited with this record calculus.  Source-specific
-- modules below inhabit it with bounded provenance.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Carrier interpretation and dependency law are separately typed.
------------------------------------------------------------------------

record RoleInterpretation : Set₁ where
  constructor role-interpretation
  field
    Carrier : Set
    Role : Set
    interpretRole : Carrier → Role
    roleReading : String

open RoleInterpretation public

record DependencyGrammar (interpretation : RoleInterpretation) : Set₁ where
  constructor dependency-grammar
  field
    depends : Carrier interpretation → Carrier interpretation → Bool
    grammarReading : String

open DependencyGrammar public

------------------------------------------------------------------------
-- Observer and rank/valuation are not built into the carrier or grammar.
------------------------------------------------------------------------

record ObserverRegime (State : Set) : Set₁ where
  constructor observer-regime
  field
    Observation : Set
    observe : State → Observation
    observerReading : String

open ObserverRegime public

record NormativeRegime (State : Set) : Set₁ where
  constructor normative-regime
  field
    ranksAbove : State → State → Bool
    normativeReading : String

open NormativeRegime public

------------------------------------------------------------------------
-- Exact finite witness that two grammars differ on the same carrier.
------------------------------------------------------------------------

record GrammarDifferenceWitness
    {Carrier : Set}
    (leftGrammar rightGrammar : Carrier → Carrier → Bool) : Set where
  constructor grammar-difference-witness
  field
    source target : Carrier
    grammarEqualityImpossible :
      leftGrammar source target ≡ rightGrammar source target → ⊥

open GrammarDifferenceWitness public

grammarsDifferOnWitness :
  ∀ {Carrier : Set}
    {leftGrammar rightGrammar : Carrier → Carrier → Bool} →
  GrammarDifferenceWitness leftGrammar rightGrammar →
  ((x y : Carrier) → leftGrammar x y ≡ rightGrammar x y) → ⊥
grammarsDifferOnWitness witness claimedEquality =
  grammarEqualityImpossible witness
    (claimedEquality (source witness) (target witness))

------------------------------------------------------------------------
-- An observer collision can coexist with a grammar distinction.
------------------------------------------------------------------------

record ObserverHiddenGrammarDifference
    {State Observation : Set}
    (observe : State → Observation)
    (grammar : State → State → Bool) : Set where
  constructor observer-hidden-grammar-difference
  field
    first second : State
    sameObservation : observe first ≡ observe second
    outgoingDifference :
      grammar first second ≡ grammar second first → ⊥

open ObserverHiddenGrammarDifference public

------------------------------------------------------------------------
-- Generic non-promotion boundary.
------------------------------------------------------------------------

record RelationalRoleGrammarBoundary : Set where
  constructor relational-role-grammar-boundary
  field
    sameCarrierImpliesSameRoleSemantics : Bool
    sameCarrierImpliesSameRoleSemanticsIsFalse :
      sameCarrierImpliesSameRoleSemantics ≡ false
    sameRoleNamesImplySameDependencyLaw : Bool
    sameRoleNamesImplySameDependencyLawIsFalse :
      sameRoleNamesImplySameDependencyLaw ≡ false
    dependencyLawImpliesNormativeRanking : Bool
    dependencyLawImpliesNormativeRankingIsFalse :
      dependencyLawImpliesNormativeRanking ≡ false
    numericCarrierOrderImpliesNormativeRanking : Bool
    numericCarrierOrderImpliesNormativeRankingIsFalse :
      numericCarrierOrderImpliesNormativeRanking ≡ false
    observerZeroImpliesEmptyFineFibre : Bool
    observerZeroImpliesEmptyFineFibreIsFalse :
      observerZeroImpliesEmptyFineFibre ≡ false
    sourceAnalogyImpliesCrossDomainIdentity : Bool
    sourceAnalogyImpliesCrossDomainIdentityIsFalse :
      sourceAnalogyImpliesCrossDomainIdentity ≡ false

canonicalRelationalRoleGrammarBoundary : RelationalRoleGrammarBoundary
canonicalRelationalRoleGrammarBoundary =
  relational-role-grammar-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
