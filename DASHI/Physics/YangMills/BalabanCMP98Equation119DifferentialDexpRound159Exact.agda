{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119DifferentialDexpRound159Exact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4SU2DexpInverseClosedFormExact as Dexp
import DASHI.Physics.YangMills.BalabanCMP109LeftRightInverseDexpCancellationExact as LR
import DASHI.Physics.YangMills.BalabanCMP98Equation119YIndexedDexpRound154Exact as R154

-- CMP98 Eq. (119), T. Balaban, Commun. Math. Phys. 98 (1985), 17--51,
-- DOI 10.1007/BF01211042.  BIDI reduction: one existing exp/log differential
-- calculus generates the whole Y-indexed left/right dexp family.
record UniformAdjointDifferentialCalculus (Lie : Set) : Set₁ where
  field
    differential : Dexp.SU2ExpLogDifferentialData Lie
    adjointExp : Lie → Dexp.Endomorphism Lie
    adjointExpInverse : Lie → Dexp.Endomorphism Lie
    adjointInverseAfterExp : ∀ y vector →
      adjointExpInverse y (adjointExp y vector) ≡ vector
open UniformAdjointDifferentialCalculus public

dexpMinusAt : ∀ {Lie} → UniformAdjointDifferentialCalculus Lie → Lie → Dexp.Endomorphism Lie
dexpMinusAt calculus y = Dexp.dexp (differential calculus) y

jMinusAt : ∀ {Lie} → UniformAdjointDifferentialCalculus Lie → Lie → Dexp.Endomorphism Lie
jMinusAt calculus y = Dexp.derivativeLogAtExp (differential calculus) y

dexpPlusAt : ∀ {Lie} → UniformAdjointDifferentialCalculus Lie → Lie → Dexp.Endomorphism Lie
dexpPlusAt calculus y vector = adjointExp calculus y (dexpMinusAt calculus y vector)

jPlusAt : ∀ {Lie} → UniformAdjointDifferentialCalculus Lie → Lie → Dexp.Endomorphism Lie
jPlusAt calculus y vector = jMinusAt calculus y (adjointExpInverse calculus y vector)

jPlusAfterDexpPlus : ∀ {Lie} (calculus : UniformAdjointDifferentialCalculus Lie) y vector →
  jPlusAt calculus y (dexpPlusAt calculus y vector) ≡ vector
jPlusAfterDexpPlus calculus y vector =
  trans
    (cong (jMinusAt calculus y)
      (adjointInverseAfterExp calculus y (dexpMinusAt calculus y vector)))
    (Dexp.derivativeLogAfterDexp (differential calculus) y vector)

dexpMinusAfterJminus : ∀ {Lie} (calculus : UniformAdjointDifferentialCalculus Lie) y vector →
  dexpMinusAt calculus y (jMinusAt calculus y vector) ≡ vector
dexpMinusAfterJminus calculus y = Dexp.dexpAfterDerivativeLog (differential calculus) y

asLeftRightAtY : ∀ {Lie} → UniformAdjointDifferentialCalculus Lie → Lie → LR.LeftRightDexpCancellationData Lie
asLeftRightAtY calculus y = record
  { LR.LeftRightDexpCancellationData.dexpPlus = dexpPlusAt calculus y
  ; LR.LeftRightDexpCancellationData.dexpMinus = dexpMinusAt calculus y
  ; LR.LeftRightDexpCancellationData.Jplus = jPlusAt calculus y
  ; LR.LeftRightDexpCancellationData.Jminus = jMinusAt calculus y
  ; LR.LeftRightDexpCancellationData.adjointExp = adjointExp calculus y
  ; LR.LeftRightDexpCancellationData.plusIsAdjointOfMinus = λ vector → refl
  ; LR.LeftRightDexpCancellationData.JplusAfterDexpPlus = jPlusAfterDexpPlus calculus y
  ; LR.LeftRightDexpCancellationData.dexpMinusAfterJminus = dexpMinusAfterJminus calculus y
  }

asUniformLeftRightDexpFamily : ∀ {Lie} → UniformAdjointDifferentialCalculus Lie → R154.UniformLeftRightDexpFamily Lie
asUniformLeftRightDexpFamily calculus = record
  { R154.UniformLeftRightDexpFamily.atY = asLeftRightAtY calculus }

uniformJminusIsExistingDlog : ∀ {Lie} (calculus : UniformAdjointDifferentialCalculus Lie) y vector →
  LR.Jminus (R154.atY (asUniformLeftRightDexpFamily calculus) y) vector
  ≡ Dexp.derivativeLogAtExp (differential calculus) y vector
uniformJminusIsExistingDlog calculus y vector = refl

uniformPrintedInverseTransport : ∀ {Lie} (calculus : UniformAdjointDifferentialCalculus Lie) y vector →
  LR.Jplus (R154.atY (asUniformLeftRightDexpFamily calculus) y)
    (LR.adjointExp (R154.atY (asUniformLeftRightDexpFamily calculus) y) vector)
  ≡ LR.Jminus (R154.atY (asUniformLeftRightDexpFamily calculus) y) vector
uniformPrintedInverseTransport calculus y = LR.leftRightInverseDexpCancellation (asLeftRightAtY calculus y)

cmp98Equation119DifferentialDexpRound159Level : ProofLevel
cmp98Equation119DifferentialDexpRound159Level = machineChecked

literalCMP98ExpLogDifferentialNormalizationRound159Level : ProofLevel
literalCMP98ExpLogDifferentialNormalizationRound159Level = conditional
