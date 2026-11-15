module DASHI.Biology.Levin.MitopolaritonTwoModeSpectrumExact where

-- Finite two-mode *frequency* matrix, rational THz coordinates.
-- Source hypothesis: Yang, Gu, Song 2026 bioRxiv 10.64898/2026.09.10.750628.
-- The symmetric 71/87/103 spectrum is an exact arithmetic fit, not a
-- measurement of coherent strong coupling, linewidth or ATP causation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _-_)
open import Relation.Binary.PropositionalEquality using (cong)

record SymmetricTwoMode : Set where
  constructor two-mode
  field
    centre : ℚ
    coupling : ℚ
open SymmetricTwoMode public

lower upper : SymmetricTwoMode → ℚ
lower h = centre h - coupling h
upper h = centre h + coupling h

-- Integer THz coordinate; not an invariant under changes of unit.
record IntegerTHzTriple : Set where
  constructor thz-triple
  field
    low middle high : ℚ
open IntegerTHzTriple public

reportedPattern : IntegerTHzTriple
reportedPattern = thz-triple 71 87 103

reportedMidpoint : 71 + 103 ≡ 87 + 87
reportedMidpoint = refl

reportedLower : 87 - 16 ≡ 71
reportedLower = refl

reportedUpper : 87 + 16 ≡ 103
reportedUpper = refl

model71to103 : SymmetricTwoMode
model71to103 = two-mode 87 16

fitLower : lower model71to103 ≡ 71
fitLower = refl

fitUpper : upper model71to103 ≡ 103
fitUpper = refl

-- Spectral parameter equality does not entail an empirical mode assignment.
data EvidenceStatus : Set where
  exactArithmetic : EvidenceStatus
  empiricalResonanceAssignmentOpen : EvidenceStatus
  coherenceAndLinewidthOpen : EvidenceStatus
  ATPMechanismOpen : EvidenceStatus
