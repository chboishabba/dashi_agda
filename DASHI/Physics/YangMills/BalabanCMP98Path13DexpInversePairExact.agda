{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13DexpInversePairExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): MINIMAL DEXP / J- SEMANTICS
--
-- The Path13 Eq.(119) source consumes only the minus-trivialized differential
-- and its inverse J-.  R159's `SU2ExpLogDifferentialData` repeats that inverse
-- under both `derivativeLogAtExp` and `closedDexpInverse` and stores four inverse
-- laws.  For this consumer the minimal semantic object is one two-sided inverse
-- pair.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4SU2DexpInverseClosedFormExact as Dexp

record DexpJminusInversePair (Lie : Set) : Set₁ where
  field
    dexpMinus : Lie → Dexp.Endomorphism Lie
    jMinus : Lie → Dexp.Endomorphism Lie

    dexpMinusAfterJminus : ∀ y vector →
      dexpMinus y (jMinus y vector) ≡ vector

    jMinusAfterDexpMinus : ∀ y vector →
      jMinus y (dexpMinus y vector) ≡ vector
open DexpJminusInversePair public

asExpLogDifferentialData :
  ∀ {Lie} → DexpJminusInversePair Lie →
  Dexp.SU2ExpLogDifferentialData Lie
asExpLogDifferentialData pair = record
  { Dexp.SU2ExpLogDifferentialData.dexp = dexpMinus pair
  ; Dexp.SU2ExpLogDifferentialData.derivativeLogAtExp = jMinus pair
  ; Dexp.SU2ExpLogDifferentialData.closedDexpInverse = jMinus pair
  ; Dexp.SU2ExpLogDifferentialData.dexpAfterDerivativeLog =
      dexpMinusAfterJminus pair
  ; Dexp.SU2ExpLogDifferentialData.derivativeLogAfterDexp =
      jMinusAfterDexpMinus pair
  ; Dexp.SU2ExpLogDifferentialData.dexpAfterClosedInverse =
      dexpMinusAfterJminus pair
  ; Dexp.SU2ExpLogDifferentialData.closedInverseAfterDexp =
      jMinusAfterDexpMinus pair
  }

fromExpLogDifferentialData :
  ∀ {Lie} → Dexp.SU2ExpLogDifferentialData Lie →
  DexpJminusInversePair Lie
fromExpLogDifferentialData data = record
  { DexpJminusInversePair.dexpMinus = Dexp.dexp data
  ; DexpJminusInversePair.jMinus = Dexp.derivativeLogAtExp data
  ; DexpJminusInversePair.dexpMinusAfterJminus =
      Dexp.dexpAfterDerivativeLog data
  ; DexpJminusInversePair.jMinusAfterDexpMinus =
      Dexp.derivativeLogAfterDexp data
  }

cmp98Path13DexpJminusInversePairCompilerLevel : ProofLevel
cmp98Path13DexpJminusInversePairCompilerLevel = machineChecked

-- Physical identification of the pair with the selected SU(2) exp/log chart
-- remains a source theorem; this owner only removes redundant interface fields.
literalCMP98Path13DexpJminusIdentificationLevel : ProofLevel
literalCMP98Path13DexpJminusIdentificationLevel = conditional
