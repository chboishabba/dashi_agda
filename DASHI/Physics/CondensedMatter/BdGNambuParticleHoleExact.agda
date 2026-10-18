module DASHI.Physics.CondensedMatter.BdGNambuParticleHoleExact where

open import Agda.Builtin.Equality using (_≡_; refl)

record AdditiveCarrier : Set₁ where
  field
    A : Set
    negate : A → A

open AdditiveCarrier public

record BdGAlgebra (carrier : AdditiveCarrier) : Set₁ where
  field
    transpose conjugate : A carrier → A carrier
    transposeInvolutive :
      (a : A carrier) → transpose (transpose a) ≡ a
    conjugateInvolutive :
      (a : A carrier) → conjugate (conjugate a) ≡ a
    transposeNegate :
      (a : A carrier) →
      transpose (negate carrier a)
      ≡ negate carrier (transpose a)
    conjugateNegate :
      (a : A carrier) →
      conjugate (negate carrier a)
      ≡ negate carrier (conjugate a)

open BdGAlgebra public

record BdGBlock (carrier : AdditiveCarrier) : Set where
  constructor bdgBlock
  field
    pp ph hp hh : A carrier

open BdGBlock public

negateBlock :
  (carrier : AdditiveCarrier) →
  BdGBlock carrier →
  BdGBlock carrier
negateBlock carrier H =
  bdgBlock
    (negate carrier (pp H))
    (negate carrier (ph H))
    (negate carrier (hp H))
    (negate carrier (hh H))

particleHoleBlock :
  (carrier : AdditiveCarrier) →
  BdGAlgebra carrier →
  BdGBlock carrier →
  BdGBlock carrier
particleHoleBlock carrier alg H =
  bdgBlock
    (conjugate alg (hh H))
    (conjugate alg (hp H))
    (conjugate alg (ph H))
    (conjugate alg (pp H))

record BdGModel
    (carrier : AdditiveCarrier)
    (alg : BdGAlgebra carrier) : Set₁ where
  field
    K : Set
    negK : K → K
    h delta deltaDag : K → A carrier

    negKInvolutive :
      (k : K) →
      negK (negK k) ≡ k

    normalConjugate :
      (k : K) →
      conjugate alg (h k)
      ≡ transpose alg (h k)

    pairingPH :
      (k : K) →
      conjugate alg (deltaDag k)
      ≡ negate carrier (delta (negK k))

    pairingHP :
      (k : K) →
      conjugate alg (delta k)
      ≡ negate carrier (deltaDag (negK k))

    holeConjugate :
      (k : K) →
      conjugate alg
        (negate carrier (transpose alg (h (negK k))))
      ≡ negate carrier (h k)

open BdGModel public

canonicalBdG :
  ∀ {carrier alg} →
  (M : BdGModel carrier alg) →
  K M →
  BdGBlock carrier
canonicalBdG {carrier} {alg} M k =
  bdgBlock
    (h M k)
    (delta M k)
    (deltaDag M k)
    (negate carrier (transpose alg (h M (negK M k))))

canonicalBdGParticleHole :
  ∀ {carrier alg} →
  (M : BdGModel carrier alg) →
  (k : K M) →
  particleHoleBlock carrier alg (canonicalBdG M k)
  ≡ negateBlock carrier (canonicalBdG M (negK M k))
canonicalBdGParticleHole {carrier} {alg} M k
  rewrite holeConjugate M k
        | pairingPH M k
        | pairingHP M k
        | normalConjugate M k
        | negKInvolutive M k =
  refl
