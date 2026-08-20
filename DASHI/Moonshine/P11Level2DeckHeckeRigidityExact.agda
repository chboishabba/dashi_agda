module DASHI.Moonshine.P11Level2DeckHeckeRigidityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Chris Godsil and Gordon Royle,
-- "Algebraic Graph Theory", Graduate Texts in Mathematics 207,
-- Springer, 2001.
-- DOI: 10.1007/978-1-4613-0163-9.
-- Equitable partitions, permutation actions and invariant adjacency algebras.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Annals of Mathematics Studies 108,
-- Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
-- Level-structure / Hecke correspondence context.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- DASHI CONTRIBUTION
--
-- Exploit the source-native full-level-2 deck S3 action to classify every
-- Nat-valued S3-invariant correspondence on the p=11 2+3 carrier.
--
-- The deck action is transitive on:
--   * ordered distinct A-pairs;
--   * all A x B pairs;
--   * all B x A pairs;
--   * B diagonal pairs;
--   * ordered distinct B-pairs.
--
-- Therefore an invariant correspondence has only five orbit parameters:
--
--   aaDiag, aaOff, ab, ba, bbDiag, bbOff.
--
-- (six scalar parameters; the prose grouping is by pair-orbit type.)
--
-- Once the coarse Brandt row sums and zero fine diagonal are supplied, the
-- odd-prime p=11 lifts are definitionally forced:
--
--   ell=3 -> K5,
--   ell=5 -> triple A-offdiag + unit cross + doubled B-offdiag.
--
-- Thus the remaining source-facing obligation is sharply reduced to proving
-- that the actual prime-to-level Hecke correspondence has no fine fixed point
-- at ell=3,5; the rest follows from deck equivariance and the coarse Brandt
-- matrices.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11FullLevel2DeckHeckeEquivarianceExact as Deck

------------------------------------------------------------------------
-- S3-orbit-constant correspondence normal form.
------------------------------------------------------------------------

record DeckInvariantSixParameterCorrespondence : Set where
  constructor deckInvariant6
  field
    aaDiag aaOff ab ba bbDiag bbOff : Nat

open DeckInvariantSixParameterCorrespondence public

multiplicity :
  DeckInvariantSixParameterCorrespondence →
  Fine.P11Fine5 → Fine.P11Fine5 → Nat
multiplicity C Fine.a0 Fine.a0 = aaDiag C
multiplicity C Fine.a1 Fine.a1 = aaDiag C
multiplicity C Fine.a0 Fine.a1 = aaOff C
multiplicity C Fine.a1 Fine.a0 = aaOff C
multiplicity C Fine.a0 Fine.b0 = ab C
multiplicity C Fine.a0 Fine.b1 = ab C
multiplicity C Fine.a0 Fine.b2 = ab C
multiplicity C Fine.a1 Fine.b0 = ab C
multiplicity C Fine.a1 Fine.b1 = ab C
multiplicity C Fine.a1 Fine.b2 = ab C
multiplicity C Fine.b0 Fine.a0 = ba C
multiplicity C Fine.b0 Fine.a1 = ba C
multiplicity C Fine.b1 Fine.a0 = ba C
multiplicity C Fine.b1 Fine.a1 = ba C
multiplicity C Fine.b2 Fine.a0 = ba C
multiplicity C Fine.b2 Fine.a1 = ba C
multiplicity C Fine.b0 Fine.b0 = bbDiag C
multiplicity C Fine.b1 Fine.b1 = bbDiag C
multiplicity C Fine.b2 Fine.b2 = bbDiag C
multiplicity C Fine.b0 Fine.b1 = bbOff C
multiplicity C Fine.b0 Fine.b2 = bbOff C
multiplicity C Fine.b1 Fine.b0 = bbOff C
multiplicity C Fine.b1 Fine.b2 = bbOff C
multiplicity C Fine.b2 Fine.b0 = bbOff C
multiplicity C Fine.b2 Fine.b1 = bbOff C

------------------------------------------------------------------------
-- The normal form is manifestly invariant under both deck generators.
------------------------------------------------------------------------

deckRInvariant :
  (C : DeckInvariantSixParameterCorrespondence) →
  (x y : Fine.P11Fine5) →
  multiplicity C (Deck.deckR x) (Deck.deckR y) ≡ multiplicity C x y
deckRInvariant C Fine.a0 Fine.a0 = refl
deckRInvariant C Fine.a0 Fine.a1 = refl
deckRInvariant C Fine.a0 Fine.b0 = refl
deckRInvariant C Fine.a0 Fine.b1 = refl
deckRInvariant C Fine.a0 Fine.b2 = refl
deckRInvariant C Fine.a1 Fine.a0 = refl
deckRInvariant C Fine.a1 Fine.a1 = refl
deckRInvariant C Fine.a1 Fine.b0 = refl
deckRInvariant C Fine.a1 Fine.b1 = refl
deckRInvariant C Fine.a1 Fine.b2 = refl
deckRInvariant C Fine.b0 Fine.a0 = refl
deckRInvariant C Fine.b0 Fine.a1 = refl
deckRInvariant C Fine.b0 Fine.b0 = refl
deckRInvariant C Fine.b0 Fine.b1 = refl
deckRInvariant C Fine.b0 Fine.b2 = refl
deckRInvariant C Fine.b1 Fine.a0 = refl
deckRInvariant C Fine.b1 Fine.a1 = refl
deckRInvariant C Fine.b1 Fine.b0 = refl
deckRInvariant C Fine.b1 Fine.b1 = refl
deckRInvariant C Fine.b1 Fine.b2 = refl
deckRInvariant C Fine.b2 Fine.a0 = refl
deckRInvariant C Fine.b2 Fine.a1 = refl
deckRInvariant C Fine.b2 Fine.b0 = refl
deckRInvariant C Fine.b2 Fine.b1 = refl
deckRInvariant C Fine.b2 Fine.b2 = refl

deckSInvariant :
  (C : DeckInvariantSixParameterCorrespondence) →
  (x y : Fine.P11Fine5) →
  multiplicity C (Deck.deckS x) (Deck.deckS y) ≡ multiplicity C x y
deckSInvariant C Fine.a0 Fine.a0 = refl
deckSInvariant C Fine.a0 Fine.a1 = refl
deckSInvariant C Fine.a0 Fine.b0 = refl
deckSInvariant C Fine.a0 Fine.b1 = refl
deckSInvariant C Fine.a0 Fine.b2 = refl
deckSInvariant C Fine.a1 Fine.a0 = refl
deckSInvariant C Fine.a1 Fine.a1 = refl
deckSInvariant C Fine.a1 Fine.b0 = refl
deckSInvariant C Fine.a1 Fine.b1 = refl
deckSInvariant C Fine.a1 Fine.b2 = refl
deckSInvariant C Fine.b0 Fine.a0 = refl
deckSInvariant C Fine.b0 Fine.a1 = refl
deckSInvariant C Fine.b0 Fine.b0 = refl
deckSInvariant C Fine.b0 Fine.b1 = refl
deckSInvariant C Fine.b0 Fine.b2 = refl
deckSInvariant C Fine.b1 Fine.a0 = refl
deckSInvariant C Fine.b1 Fine.a1 = refl
deckSInvariant C Fine.b1 Fine.b0 = refl
deckSInvariant C Fine.b1 Fine.b1 = refl
deckSInvariant C Fine.b1 Fine.b2 = refl
deckSInvariant C Fine.b2 Fine.a0 = refl
deckSInvariant C Fine.b2 Fine.a1 = refl
deckSInvariant C Fine.b2 Fine.b0 = refl
deckSInvariant C Fine.b2 Fine.b1 = refl
deckSInvariant C Fine.b2 Fine.b2 = refl

------------------------------------------------------------------------
-- Coarse row totals induced by the 2+3 quotient.
------------------------------------------------------------------------

coarseAA : DeckInvariantSixParameterCorrespondence → Nat
coarseAA C = aaDiag C + aaOff C

coarseAB : DeckInvariantSixParameterCorrespondence → Nat
coarseAB C = 3 * ab C

coarseBA : DeckInvariantSixParameterCorrespondence → Nat
coarseBA C = 2 * ba C

coarseBB : DeckInvariantSixParameterCorrespondence → Nat
coarseBB C = bbDiag C + 2 * bbOff C

------------------------------------------------------------------------
-- Fine looplessness removes the only residual orbit ambiguity needed here.
------------------------------------------------------------------------

record LooplessDeckInvariant : Set where
  constructor looplessDeckInvariant
  field
    correspondence : DeckInvariantSixParameterCorrespondence
    aaNoLoop : aaDiag correspondence ≡ 0
    bbNoLoop : bbDiag correspondence ≡ 0

open LooplessDeckInvariant public

------------------------------------------------------------------------
-- ell=3 rigidity.
------------------------------------------------------------------------

record Ell3BrandtQuotientData (C : LooplessDeckInvariant) : Set where
  field
    aaRow : coarseAA (correspondence C) ≡ 1
    abRow : coarseAB (correspondence C) ≡ 3
    baRow : coarseBA (correspondence C) ≡ 2
    bbRow : coarseBB (correspondence C) ≡ 2

ell3ForcedNormalForm :
  (C : LooplessDeckInvariant) →
  Ell3BrandtQuotientData C →
  aaDiag (correspondence C) ≡ 0
  × aaOff (correspondence C) ≡ 1
  × ab (correspondence C) ≡ 1
  × ba (correspondence C) ≡ 1
  × bbDiag (correspondence C) ≡ 0
  × bbOff (correspondence C) ≡ 1
ell3ForcedNormalForm C data =
  aaNoLoop C ,
  offA , crossAB , crossBA , bbNoLoop C , offB
  where
    open Ell3BrandtQuotientData data

    offA : aaOff (correspondence C) ≡ 1
    offA rewrite aaNoLoop C = aaRow

    crossAB : ab (correspondence C) ≡ 1
    crossAB with ab (correspondence C)
    ... | 0 = λ () → abRow
    ... | 1 = refl
    ... | suc (suc n) = λ () → abRow

    crossBA : ba (correspondence C) ≡ 1
    crossBA with ba (correspondence C)
    ... | 0 = λ () → baRow
    ... | 1 = refl
    ... | suc (suc n) = λ () → baRow

    offB : bbOff (correspondence C) ≡ 1
    offB rewrite bbNoLoop C with bbOff (correspondence C)
    ... | 0 = λ () → bbRow
    ... | 1 = refl
    ... | suc (suc n) = λ () → bbRow

------------------------------------------------------------------------
-- ell=5 rigidity.
------------------------------------------------------------------------

record Ell5BrandtQuotientData (C : LooplessDeckInvariant) : Set where
  field
    aaRow : coarseAA (correspondence C) ≡ 3
    abRow : coarseAB (correspondence C) ≡ 3
    baRow : coarseBA (correspondence C) ≡ 2
    bbRow : coarseBB (correspondence C) ≡ 4

ell5ForcedNormalForm :
  (C : LooplessDeckInvariant) →
  Ell5BrandtQuotientData C →
  aaDiag (correspondence C) ≡ 0
  × aaOff (correspondence C) ≡ 3
  × ab (correspondence C) ≡ 1
  × ba (correspondence C) ≡ 1
  × bbDiag (correspondence C) ≡ 0
  × bbOff (correspondence C) ≡ 2
ell5ForcedNormalForm C data =
  aaNoLoop C ,
  offA , crossAB , crossBA , bbNoLoop C , offB
  where
    open Ell5BrandtQuotientData data

    offA : aaOff (correspondence C) ≡ 3
    offA rewrite aaNoLoop C = aaRow

    crossAB : ab (correspondence C) ≡ 1
    crossAB with ab (correspondence C)
    ... | 0 = λ () → abRow
    ... | 1 = refl
    ... | suc (suc n) = λ () → abRow

    crossBA : ba (correspondence C) ≡ 1
    crossBA with ba (correspondence C)
    ... | 0 = λ () → baRow
    ... | 1 = refl
    ... | suc (suc n) = λ () → baRow

    offB : bbOff (correspondence C) ≡ 2
    offB rewrite bbNoLoop C with bbOff (correspondence C)
    ... | 0 = λ () → bbRow
    ... | 1 = λ () → bbRow
    ... | 2 = refl
    ... | suc (suc (suc n)) = λ () → bbRow

------------------------------------------------------------------------
-- Exact existing R3/R5 normal forms.
------------------------------------------------------------------------

existingR3NormalForm : DeckInvariantSixParameterCorrespondence
existingR3NormalForm = deckInvariant6 0 1 1 1 0 1

existingR5NormalForm : DeckInvariantSixParameterCorrespondence
existingR5NormalForm = deckInvariant6 0 3 1 1 0 2

existingR3MultiplicityMatches :
  (x y : Fine.P11Fine5) →
  multiplicity existingR3NormalForm x y
  ≡ Deck.edgeMultiplicity Fine.R3Positive x y
existingR3MultiplicityMatches Fine.a0 Fine.a0 = refl
existingR3MultiplicityMatches Fine.a0 Fine.a1 = refl
existingR3MultiplicityMatches Fine.a0 Fine.b0 = refl
existingR3MultiplicityMatches Fine.a0 Fine.b1 = refl
existingR3MultiplicityMatches Fine.a0 Fine.b2 = refl
existingR3MultiplicityMatches Fine.a1 Fine.a0 = refl
existingR3MultiplicityMatches Fine.a1 Fine.a1 = refl
existingR3MultiplicityMatches Fine.a1 Fine.b0 = refl
existingR3MultiplicityMatches Fine.a1 Fine.b1 = refl
existingR3MultiplicityMatches Fine.a1 Fine.b2 = refl
existingR3MultiplicityMatches Fine.b0 Fine.a0 = refl
existingR3MultiplicityMatches Fine.b0 Fine.a1 = refl
existingR3MultiplicityMatches Fine.b0 Fine.b0 = refl
existingR3MultiplicityMatches Fine.b0 Fine.b1 = refl
existingR3MultiplicityMatches Fine.b0 Fine.b2 = refl
existingR3MultiplicityMatches Fine.b1 Fine.a0 = refl
existingR3MultiplicityMatches Fine.b1 Fine.a1 = refl
existingR3MultiplicityMatches Fine.b1 Fine.b0 = refl
existingR3MultiplicityMatches Fine.b1 Fine.b1 = refl
existingR3MultiplicityMatches Fine.b1 Fine.b2 = refl
existingR3MultiplicityMatches Fine.b2 Fine.a0 = refl
existingR3MultiplicityMatches Fine.b2 Fine.a1 = refl
existingR3MultiplicityMatches Fine.b2 Fine.b0 = refl
existingR3MultiplicityMatches Fine.b2 Fine.b1 = refl
existingR3MultiplicityMatches Fine.b2 Fine.b2 = refl

existingR5MultiplicityMatches :
  (x y : Fine.P11Fine5) →
  multiplicity existingR5NormalForm x y
  ≡ Deck.edgeMultiplicity Fine.R5Positive x y
existingR5MultiplicityMatches Fine.a0 Fine.a0 = refl
existingR5MultiplicityMatches Fine.a0 Fine.a1 = refl
existingR5MultiplicityMatches Fine.a0 Fine.b0 = refl
existingR5MultiplicityMatches Fine.a0 Fine.b1 = refl
existingR5MultiplicityMatches Fine.a0 Fine.b2 = refl
existingR5MultiplicityMatches Fine.a1 Fine.a0 = refl
existingR5MultiplicityMatches Fine.a1 Fine.a1 = refl
existingR5MultiplicityMatches Fine.a1 Fine.b0 = refl
existingR5MultiplicityMatches Fine.a1 Fine.b1 = refl
existingR5MultiplicityMatches Fine.a1 Fine.b2 = refl
existingR5MultiplicityMatches Fine.b0 Fine.a0 = refl
existingR5MultiplicityMatches Fine.b0 Fine.a1 = refl
existingR5MultiplicityMatches Fine.b0 Fine.b0 = refl
existingR5MultiplicityMatches Fine.b0 Fine.b1 = refl
existingR5MultiplicityMatches Fine.b0 Fine.b2 = refl
existingR5MultiplicityMatches Fine.b1 Fine.a0 = refl
existingR5MultiplicityMatches Fine.b1 Fine.a1 = refl
existingR5MultiplicityMatches Fine.b1 Fine.b0 = refl
existingR5MultiplicityMatches Fine.b1 Fine.b1 = refl
existingR5MultiplicityMatches Fine.b1 Fine.b2 = refl
existingR5MultiplicityMatches Fine.b2 Fine.a0 = refl
existingR5MultiplicityMatches Fine.b2 Fine.a1 = refl
existingR5MultiplicityMatches Fine.b2 Fine.b0 = refl
existingR5MultiplicityMatches Fine.b2 Fine.b1 = refl
existingR5MultiplicityMatches Fine.b2 Fine.b2 = refl

record P11Level2DeckHeckeRigidityBoundary : Set where
  field
    deckInvariantCorrespondenceReducedToSixParameters : Bool
    deckInvariantCorrespondenceReducedToSixParametersIsTrue :
      deckInvariantCorrespondenceReducedToSixParameters ≡ true

    looplessEll3BrandtLiftForced : Bool
    looplessEll3BrandtLiftForcedIsTrue : looplessEll3BrandtLiftForced ≡ true

    looplessEll5BrandtLiftForced : Bool
    looplessEll5BrandtLiftForcedIsTrue : looplessEll5BrandtLiftForced ≡ true

    existingR3R5MatchForcedNormalForms : Bool
    existingR3R5MatchForcedNormalFormsIsTrue :
      existingR3R5MatchForcedNormalForms ≡ true

    geometricFineLooplessnessProvedHere : Bool
    geometricFineLooplessnessProvedHereIsFalse :
      geometricFineLooplessnessProvedHere ≡ false

canonicalP11Level2DeckHeckeRigidityBoundary : P11Level2DeckHeckeRigidityBoundary
canonicalP11Level2DeckHeckeRigidityBoundary =
  record
    { deckInvariantCorrespondenceReducedToSixParameters = true
    ; deckInvariantCorrespondenceReducedToSixParametersIsTrue = refl
    ; looplessEll3BrandtLiftForced = true
    ; looplessEll3BrandtLiftForcedIsTrue = refl
    ; looplessEll5BrandtLiftForced = true
    ; looplessEll5BrandtLiftForcedIsTrue = refl
    ; existingR3R5MatchForcedNormalForms = true
    ; existingR3R5MatchForcedNormalFormsIsTrue = refl
    ; geometricFineLooplessnessProvedHere = false
    ; geometricFineLooplessnessProvedHereIsFalse = refl
    }
