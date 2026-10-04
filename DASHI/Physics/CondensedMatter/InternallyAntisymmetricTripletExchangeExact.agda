module DASHI.Physics.CondensedMatter.InternallyAntisymmetricTripletExchangeExact where

open import Agda.Builtin.Equality using (_≡_; refl)

data ExchangeParity : Set where
  even odd : ExchangeParity

_*p_ : ExchangeParity → ExchangeParity → ExchangeParity
even *p p = p
odd *p even = odd
odd *p odd = even

parityAssociative :
  (a b c : ExchangeParity) →
  (a *p b) *p c ≡ a *p (b *p c)
parityAssociative even even even = refl
parityAssociative even even odd = refl
parityAssociative even odd even = refl
parityAssociative even odd odd = refl
parityAssociative odd even even = refl
parityAssociative odd even odd = refl
parityAssociative odd odd even = refl
parityAssociative odd odd odd = refl

record PairExchangeSector : Set where
  constructor pairSector
  field
    spatial spin orbital : ExchangeParity

open PairExchangeSector public

totalExchangeParity : PairExchangeSector → ExchangeParity
totalExchangeParity P =
  (spatial P *p spin P) *p orbital P

onsiteTripletOrbitalAntisymmetric : PairExchangeSector
onsiteTripletOrbitalAntisymmetric =
  pairSector even even odd

intPairingIsFermionic :
  totalExchangeParity onsiteTripletOrbitalAntisymmetric ≡ odd
intPairingIsFermionic = refl

onsiteTripletOrbitalSymmetric : PairExchangeSector
onsiteTripletOrbitalSymmetric =
  pairSector even even even

orbitalAntisymmetryEssentialInThisSector :
  totalExchangeParity onsiteTripletOrbitalSymmetric ≡ even
orbitalAntisymmetryEssentialInThisSector = refl
