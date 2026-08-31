{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119FederbushCalculusReuseRound175Exact where

------------------------------------------------------------------------
-- ROUND175 A1 BIDI: R159'S CALCULUS IS ALREADY IN THE FEDERBUSH LANE
--
-- Primary sources:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I", Commun. Math. Phys. 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
-- Brian C. Hall, "Lie Groups, Lie Algebras, and Representations", 2nd ed.
-- Springer (2015). DOI: 10.1007/978-3-319-13467-3.
--
-- R159 still accepted a uniform exp/log differential calculus plus an explicit
-- inverse for Ad_exp.  The older physical Federbush lane already owns, at each
-- Y, the source-relevant reduced operators
--
--   D_+(Y), D_-(Y), J_+(Y), J_-(Y), Ad_exp(Y)
--
-- together with
--
--   D_- Ad = D_+,   J_+ D_+ = I,   J_- D_- = I.
--
-- Because all reduced-adjoint operators commute, these data already generate:
--
--   * both-sided inverse laws for D_- and J_-;
--   * an inverse of Ad, namely J_+ D_-;
--   * therefore the complete R159 `UniformAdjointDifferentialCalculus`.
--
-- No new analytic inverse, no new J+/J- cancellation receipt, and no separate
-- transport convention is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier using
  (SU2LieAlgebra)
import DASHI.Physics.YangMills.BalabanSU2ReducedAdjointCalculus as R
import DASHI.Physics.YangMills.BalabanSU2AdjointAnalyticFunctionalCalculus as Analytic
import DASHI.Physics.YangMills.BalabanClayGate4SU2DexpInverseClosedFormExact as Dexp
import DASHI.Physics.YangMills.BalabanCMP109PhysicalFederbushConventionCancellationExact as Federbush
import DASHI.Physics.YangMills.BalabanCMP109LeftRightInverseDexpCancellationExact as LR
import DASHI.Physics.YangMills.BalabanCMP98Equation119YIndexedDexpRound154Exact as R154
import DASHI.Physics.YangMills.BalabanCMP98Equation119DifferentialDexpRound159Exact as R159

record ExistingFederbushConventionFamily : Set₁ where
  field
    atY : (Y : SU2LieAlgebra) → Federbush.LiteralCMP109FederbushConvention Y

open ExistingFederbushConventionFamily public

adjointInverseOperator :
  (Y : SU2LieAlgebra) →
  Federbush.LiteralCMP109FederbushConvention Y →
  R.ReducedAdjointOperator
adjointInverseOperator Y convention =
  R.composeReducedAdjoint Y
    (Federbush.inversePlus convention)
    (Federbush.dexpMinus convention)

minusAfterInverseMinusIsIdentity :
  ∀ Y (convention : Federbush.LiteralCMP109FederbushConvention Y) →
  R.composeReducedAdjoint Y
    (Federbush.dexpMinus convention)
    (Federbush.inverseMinus convention)
  ≡ R.identityReducedAdjoint
minusAfterInverseMinusIsIdentity Y convention =
  trans
    (R.composeReducedCommutative Y
      (Federbush.dexpMinus convention)
      (Federbush.inverseMinus convention))
    (Federbush.inverseMinusAfterMinusIsIdentity convention)

adjointInverseAfterAdjointIsIdentity :
  ∀ Y (convention : Federbush.LiteralCMP109FederbushConvention Y) →
  R.composeReducedAdjoint Y
    (adjointInverseOperator Y convention)
    (Federbush.adjointTransport convention)
  ≡ R.identityReducedAdjoint
adjointInverseAfterAdjointIsIdentity Y convention =
  trans
    (R.composeReducedAssociative Y
      (Federbush.inversePlus convention)
      (Federbush.dexpMinus convention)
      (Federbush.adjointTransport convention))
    (trans
      (cong
        (R.composeReducedAdjoint Y (Federbush.inversePlus convention))
        (Federbush.dexpMinusAfterAdjointIsPlus convention))
      (Federbush.inversePlusAfterPlusIsIdentity convention))

asExpLogDifferentialData :
  ExistingFederbushConventionFamily →
  Dexp.SU2ExpLogDifferentialData SU2LieAlgebra
asExpLogDifferentialData family = record
  { Dexp.SU2ExpLogDifferentialData.dexp =
      λ Y X → R.applyReducedAdjoint Y
        (Federbush.dexpMinus (atY family Y)) X
  ; Dexp.SU2ExpLogDifferentialData.derivativeLogAtExp =
      λ Y X → R.applyReducedAdjoint Y
        (Federbush.inverseMinus (atY family Y)) X
  ; Dexp.SU2ExpLogDifferentialData.closedDexpInverse =
      λ Y X → R.applyReducedAdjoint Y
        (Federbush.inverseMinus (atY family Y)) X
  ; Dexp.SU2ExpLogDifferentialData.dexpAfterDerivativeLog =
      λ Y X →
        Analytic.inverseDexpActsRight Y
          (Federbush.dexpMinus (atY family Y))
          (Federbush.inverseMinus (atY family Y))
          (minusAfterInverseMinusIsIdentity Y (atY family Y)) X
  ; Dexp.SU2ExpLogDifferentialData.derivativeLogAfterDexp =
      λ Y X →
        Analytic.inverseDexpActsLeft Y
          (Federbush.dexpMinus (atY family Y))
          (Federbush.inverseMinus (atY family Y))
          (Federbush.inverseMinusAfterMinusIsIdentity (atY family Y)) X
  ; Dexp.SU2ExpLogDifferentialData.dexpAfterClosedInverse =
      λ Y X →
        Analytic.inverseDexpActsRight Y
          (Federbush.dexpMinus (atY family Y))
          (Federbush.inverseMinus (atY family Y))
          (minusAfterInverseMinusIsIdentity Y (atY family Y)) X
  ; Dexp.SU2ExpLogDifferentialData.closedInverseAfterDexp =
      λ Y X →
        Analytic.inverseDexpActsLeft Y
          (Federbush.dexpMinus (atY family Y))
          (Federbush.inverseMinus (atY family Y))
          (Federbush.inverseMinusAfterMinusIsIdentity (atY family Y)) X
  }

asUniformAdjointDifferentialCalculus :
  ExistingFederbushConventionFamily →
  R159.UniformAdjointDifferentialCalculus SU2LieAlgebra
asUniformAdjointDifferentialCalculus family = record
  { R159.UniformAdjointDifferentialCalculus.differential =
      asExpLogDifferentialData family
  ; R159.UniformAdjointDifferentialCalculus.adjointExp =
      λ Y X → R.applyReducedAdjoint Y
        (Federbush.adjointTransport (atY family Y)) X
  ; R159.UniformAdjointDifferentialCalculus.adjointExpInverse =
      λ Y X → R.applyReducedAdjoint Y
        (adjointInverseOperator Y (atY family Y)) X
  ; R159.UniformAdjointDifferentialCalculus.adjointInverseAfterExp =
      λ Y X →
        trans
          (R.applyReducedComposition Y
            (adjointInverseOperator Y (atY family Y))
            (Federbush.adjointTransport (atY family Y)) X)
          (trans
            (cong (λ operator → R.applyReducedAdjoint Y operator X)
              (adjointInverseAfterAdjointIsIdentity Y (atY family Y)))
            (R.applyIdentityReducedAdjoint Y X))
  }

r159JminusIsExistingFederbushInverseMinus :
  (family : ExistingFederbushConventionFamily) →
  ∀ Y X →
  R159.jMinusAt (asUniformAdjointDifferentialCalculus family) Y X
  ≡ R.applyReducedAdjoint Y
      (Federbush.inverseMinus (atY family Y)) X
r159JminusIsExistingFederbushInverseMinus family Y X = refl

r159AdjointIsExistingFederbushTransport :
  (family : ExistingFederbushConventionFamily) →
  ∀ Y X →
  R159.adjointExp (asUniformAdjointDifferentialCalculus family) Y X
  ≡ R.applyReducedAdjoint Y
      (Federbush.adjointTransport (atY family Y)) X
r159AdjointIsExistingFederbushTransport family Y X = refl

r159PrintedInverseTransportFromExistingFederbush :
  (family : ExistingFederbushConventionFamily) →
  ∀ Y X →
  LR.Jplus
    (R154.atY
      (R159.asUniformLeftRightDexpFamily
        (asUniformAdjointDifferentialCalculus family)) Y)
    (R159.adjointExp (asUniformAdjointDifferentialCalculus family) Y X)
  ≡ R.applyReducedAdjoint Y
      (Federbush.inverseMinus (atY family Y)) X
r159PrintedInverseTransportFromExistingFederbush family Y X =
  trans
    (R159.uniformPrintedInverseTransport
      (asUniformAdjointDifferentialCalculus family) Y X)
    (r159JminusIsExistingFederbushInverseMinus family Y X)

cmp98Equation119FederbushCalculusReuseRound175Level : ProofLevel
cmp98Equation119FederbushCalculusReuseRound175Level = machineChecked

cmp98Equation119GeneratedAdjointInverseRound175Level : ProofLevel
cmp98Equation119GeneratedAdjointInverseRound175Level = machineChecked

literalCMP98PrincipalCoordinateIsFederbushConventionRound175Level : ProofLevel
literalCMP98PrincipalCoordinateIsFederbushConventionRound175Level = conditional
