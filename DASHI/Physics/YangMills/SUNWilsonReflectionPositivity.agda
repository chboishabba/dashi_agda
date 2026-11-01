module DASHI.Physics.YangMills.SUNWilsonReflectionPositivity where

------------------------------------------------------------------------
-- Concrete SU(N) Wilson reflection-positivity socket.
--
-- Peter--Weyl/Haar factorization across a time-reflection interface is
-- standard imported representation theory. Once supplied as finite square
-- terms, the OS inequality is inherited from FiniteReflectionPositivity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.FiniteReflectionPositivity
open import DASHI.Physics.YangMills.SUNMatrixCarrier
open import DASHI.Physics.YangMills.SUNWilsonClassFunction

record SUNWilsonReflectionFactorization
    {N : Nat}
    {Matrix Complex Observable Interface Scalar : Set}
    (theory : CertifiedSUNMatrixTheory N Matrix Complex)
    (scalar : PositiveAdditiveScalar Scalar) : Set₁ where
  field
    traceAuthority : SUNWilsonTraceAuthority {Scalar = Scalar} theory
    interfaceIndices : List Interface
    squareTerm : Observable → Interface → Scalar
    squareTermNonnegative : ∀ observable index →
      Nonnegative scalar (squareTerm observable index)
    wilsonOSForm : Observable → Scalar
    peterWeylFactorization : ∀ observable →
      wilsonOSForm observable ≡
      sumTerms scalar (squareTerm observable) interfaceIndices

open SUNWilsonReflectionFactorization public

toReflectionSquareFactorization :
  ∀ {N : Nat}
    {Matrix Complex Observable Interface Scalar : Set}
    {theory : CertifiedSUNMatrixTheory N Matrix Complex}
    {scalar : PositiveAdditiveScalar Scalar} →
  SUNWilsonReflectionFactorization
    {Observable = Observable} {Interface = Interface}
    theory scalar →
  ReflectionSquareFactorization Observable Interface Scalar scalar
toReflectionSquareFactorization factorizationData = record
  { indices = interfaceIndices factorizationData
  ; squareTerm = squareTerm factorizationData
  ; squareTermNonnegative = squareTermNonnegative factorizationData
  ; osForm = wilsonOSForm factorizationData
  ; factorization = peterWeylFactorization factorizationData
  }

sunWilsonReflectionPositive :
  ∀ {N : Nat}
    {Matrix Complex Observable Interface Scalar : Set}
    {theory : CertifiedSUNMatrixTheory N Matrix Complex}
    {scalar : PositiveAdditiveScalar Scalar} →
  SUNWilsonReflectionFactorization
    {Observable = Observable} {Interface = Interface}
    theory scalar →
  FiniteReflectionPositive Observable Scalar scalar
sunWilsonReflectionPositive factorizationData =
  factorizationToReflectionPositive
    (toReflectionSquareFactorization factorizationData)

sunWilsonReflectionPositivityLevel : ProofLevel
sunWilsonReflectionPositivityLevel = machineChecked

sunWilsonPeterWeylFactorizationLevel : ProofLevel
sunWilsonPeterWeylFactorizationLevel = standardImported
