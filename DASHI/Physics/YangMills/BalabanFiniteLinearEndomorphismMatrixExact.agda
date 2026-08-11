module DASHI.Physics.YangMills.BalabanFiniteLinearEndomorphismMatrixExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Upgrade the repository's exact finite linear-functional coordinate theorem
-- to finite linear endomorphisms.  Every proof-bearing linear endomorphism on
-- a concrete finite rational carrier is represented by the literal matrix
--
--     M(i,j) = (T e_j)(i),
--
-- and matrix application is proved pointwise equal to T.  Consequently a
-- pointwise-injective endomorphism yields the exact PointwiseInjective matrix
-- premise consumed by BalabanFiniteRationalInjectiveInverseExact.  This is the
-- finite algebra bridge used by the reduced/padded normal equation; it adds no
-- Yang--Mills analytic assumption and uses no function extensionality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteLinearFunctionalCoordinatesExact as Linear
import DASHI.Physics.YangMills.BalabanFiniteRationalInjectiveInverseExact as Inverse

Vector : Set → Set
Vector = Linear.Vector

record FiniteLinearEndomorphism {Index : Set}
    (carrier : Matrix.FiniteRationalCoordinates Index) : Set₁ where
  field
    operator : Vector Index → Vector Index
    zeroExact : ∀ row → operator Linear.zeroVector row ≡ Linear.zeroVector row
    addExact : ∀ left right row →
      operator (Linear.addVector left right) row
      ≡ Linear.addVector (operator left) (operator right) row
    scaleExact : ∀ coefficient vector row →
      operator (Linear.scaleVector coefficient vector) row
      ≡ Linear.scaleVector coefficient (operator vector) row
    pointwiseCong : ∀ left right →
      (∀ index → left index ≡ right index) →
      ∀ row → operator left row ≡ operator right row

open FiniteLinearEndomorphism public

rowFunctional :
  ∀ {Index}
    {carrier : Matrix.FiniteRationalCoordinates Index} →
  FiniteLinearEndomorphism carrier → Index →
  Linear.FiniteLinearFunctional carrier
rowFunctional endomorphism row = record
  { Linear.FiniteLinearFunctional.functional =
      λ vector → operator endomorphism vector row
  ; Linear.FiniteLinearFunctional.zeroExact = zeroExact endomorphism row
  ; Linear.FiniteLinearFunctional.addExact =
      λ left right → addExact endomorphism left right row
  ; Linear.FiniteLinearFunctional.scaleExact =
      λ coefficient vector → scaleExact endomorphism coefficient vector row
  ; Linear.FiniteLinearFunctional.pointwiseCong =
      λ left right pointwise → pointwiseCong endomorphism left right pointwise row
  }

endomorphismMatrix :
  ∀ {Index}
    {carrier : Matrix.FiniteRationalCoordinates Index} →
  FiniteLinearEndomorphism carrier → Matrix.RationalMatrix Index
endomorphismMatrix {carrier = carrier} endomorphism row column =
  operator endomorphism (Linear.basisVector carrier column) row

endomorphismMatrixActsExactly :
  ∀ {Index}
    {carrier : Matrix.FiniteRationalCoordinates Index}
    (endomorphism : FiniteLinearEndomorphism carrier)
    vector row →
  Matrix.applyMatrix carrier (endomorphismMatrix endomorphism) vector row
  ≡ operator endomorphism vector row
endomorphismMatrixActsExactly endomorphism vector row =
  Linear.finiteLinearFunctionalCoordinateExpansion
    (rowFunctional endomorphism row) vector

PointwiseInjectiveEndomorphism :
  ∀ {Index}
    {carrier : Matrix.FiniteRationalCoordinates Index} →
  FiniteLinearEndomorphism carrier → Set
PointwiseInjectiveEndomorphism endomorphism =
  ∀ left right →
  (∀ row → operator endomorphism left row ≡ operator endomorphism right row) →
  ∀ row → left row ≡ right row

endomorphismInjectiveImpliesMatrixInjective :
  ∀ {Index}
    {carrier : Matrix.FiniteRationalCoordinates Index}
    (endomorphism : FiniteLinearEndomorphism carrier) →
  PointwiseInjectiveEndomorphism endomorphism →
  Inverse.PointwiseInjective carrier (endomorphismMatrix endomorphism)
endomorphismInjectiveImpliesMatrixInjective endomorphism injective left right equal row =
  injective left right
    (λ coordinate →
      trans
        (sym (endomorphismMatrixActsExactly endomorphism left coordinate))
        (trans
          (equal coordinate)
          (endomorphismMatrixActsExactly endomorphism right coordinate)))
    row

finiteLinearEndomorphismMatrixLevel : ProofLevel
finiteLinearEndomorphismMatrixLevel = machineChecked

finiteLinearEndomorphismInjectivityBridgeLevel : ProofLevel
finiteLinearEndomorphismInjectivityBridgeLevel = machineChecked
