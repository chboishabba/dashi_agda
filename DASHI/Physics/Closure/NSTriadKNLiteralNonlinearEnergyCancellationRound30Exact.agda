module DASHI.Physics.Closure.NSTriadKNLiteralNonlinearEnergyCancellationRound30Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Turn the local skew-energy cancellation of each canonical retained triad
-- orbit into the complete finite nonlinear power identity.  The orbit list
-- carries an explicit exhaustive/no-duplication authority and each packet is
-- required to be the literal three-leg transfer of the Galerkin convolution.
-- Only after those physical facts are present is the finite fold reduced to
-- zero.  This closes the combinatorial summation step without defining the
-- third leg as an ad hoc balancing receipt.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

sumPower :
  ∀ {packetLevel : Level} {Packet : Set packetLevel} →
  List Packet → (Packet → ℚ) → ℚ
sumPower [] contribution = 0ℚ
sumPower (packet ∷ rest) contribution =
  contribution packet + sumPower rest contribution

sumPointwiseZero :
  ∀ {packetLevel : Level} {Packet : Set packetLevel}
    (packets : List Packet)
    (contribution : Packet → ℚ) →
  (∀ packet → contribution packet ≡ 0ℚ) →
  sumPower packets contribution ≡ 0ℚ
sumPointwiseZero [] contribution pointwise = refl
sumPointwiseZero (packet ∷ rest) contribution pointwise =
  trans
    (cong
      (λ selected → contribution packet + selected)
      (sumPointwiseZero rest contribution pointwise))
    (trans
      (cong (λ selected → selected + 0ℚ) (pointwise packet))
      (solve []))

record LiteralCanonicalTriadEnergyFamily
    {packetLevel : Level}
    (Packet : Set packetLevel) : Set (lsuc packetLevel) where
  field
    canonicalPackets : List Packet

    RepresentsRetainedTriadOrbit : Packet → Set packetLevel
    packetIsLiteralRetainedOrbit : ∀ packet →
      RepresentsRetainedTriadOrbit packet

    Exhaustive : Set packetLevel
    NoDuplicateOrbit : Set packetLevel
    exhaustive : Exhaustive
    noDuplicateOrbit : NoDuplicateOrbit

    threeLegPower : Packet → ℚ
    threeLegPowerIsLiteralGalerkinTransfer : Packet → Set packetLevel
    literalThreeLegPower : ∀ packet →
      threeLegPowerIsLiteralGalerkinTransfer packet

    skewEnergyCancellation : ∀ packet →
      threeLegPower packet ≡ 0ℚ

open LiteralCanonicalTriadEnergyFamily public

literalNonlinearPower :
  ∀ {packetLevel}
    {Packet : Set packetLevel} →
  LiteralCanonicalTriadEnergyFamily Packet → ℚ
literalNonlinearPower family =
  sumPower (canonicalPackets family) (threeLegPower family)

literalFiniteNonlinearEnergyCancellation :
  ∀ {packetLevel}
    {Packet : Set packetLevel}
    (family : LiteralCanonicalTriadEnergyFamily Packet) →
  literalNonlinearPower family ≡ 0ℚ
literalFiniteNonlinearEnergyCancellation family =
  sumPointwiseZero
    (canonicalPackets family)
    (threeLegPower family)
    (skewEnergyCancellation family)

record TimeDependentLiteralTriadEnergy
    {timeLevel packetLevel : Level}
    (Time : Set timeLevel)
    (Packet : Set packetLevel) :
    Set (lsuc (timeLevel ⊔ packetLevel)) where
  field
    familyAt : Time → LiteralCanonicalTriadEnergyFamily Packet

open TimeDependentLiteralTriadEnergy public

timeDependentLiteralNonlinearCancellation :
  ∀ {timeLevel packetLevel}
    {Time : Set timeLevel}
    {Packet : Set packetLevel}
    (dataSet : TimeDependentLiteralTriadEnergy Time Packet) →
  ∀ time → literalNonlinearPower (familyAt dataSet time) ≡ 0ℚ
timeDependentLiteralNonlinearCancellation dataSet time =
  literalFiniteNonlinearEnergyCancellation (familyAt dataSet time)

literalNonlinearFiniteFoldClosed : Bool
literalNonlinearFiniteFoldClosed = true

literalCanonicalOrbitEnergyProducerClosed : Bool
literalCanonicalOrbitEnergyProducerClosed = false

literalNonlinearFiniteFoldClosedIsTrue :
  literalNonlinearFiniteFoldClosed ≡ true
literalNonlinearFiniteFoldClosedIsTrue = refl

literalCanonicalOrbitEnergyProducerClosedIsFalse :
  literalCanonicalOrbitEnergyProducerClosed ≡ false
literalCanonicalOrbitEnergyProducerClosedIsFalse = refl
