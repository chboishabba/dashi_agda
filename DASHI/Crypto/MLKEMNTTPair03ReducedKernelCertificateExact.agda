module DASHI.Crypto.MLKEMNTTPair03ReducedKernelCertificateExact where

------------------------------------------------------------------------
-- ML-KEM / FIPS-203: COMPACT 81^2 PAIR-(0,3) BOUNDED-KERNEL CERTIFICATE
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- This is the finite half of the compact pair-(0,3) injectivity proof.  It does
-- NOT enumerate the 5^8 = 390625 CBD2 source carrier.
--
-- For two CBD2 candidates each coordinate difference lies in [-4,4].  The
-- pair-(0,3) fourth-power identity compresses coordinates j and j+4 to
--
--   e_j = d_j + 296 d_(j+4) mod 3329.
--
-- There are only 9*9 = 81 possible compressed residues.  The cubic root-factor
-- reduction in `MLKEMNTTPair03CubicRootFactorReductionExact` says a kernel cubic
-- must satisfy, with p = e2 + 585 e3,
--
--   e0 = -331 p,
--   e1 = -585 p - 331 e3                 (mod 3329).
--
-- The closed checker below ranges over only (e2,e3) in S^2, i.e. 81^2 = 6561
-- reduced states.  It proves every state for which both predicted e0 and e1 are
-- also in S has e2=e3=0.  A second 81-state checker proves compressed residue 0
-- has the unique digit pair (0,0).  Together they yield a semantic bounded-
-- kernel theorem from the two reduced coefficient equations.
--
-- The companion Python producer
--   scripts/crypto_ntt_pair03_compact_injectivity_certificate.py
-- independently reports 161 states after the e0-membership filter and exactly
-- one after the e1-membership filter: zero.
--
-- BLUE-TEAM BOUNDARY
-- ------------------
-- This theorem is about the raw bounded difference kernel.  It does not assert
-- that a physical trace exposes the pair, does not recover a complete ML-KEM
-- key, and does not establish a runtime bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _==_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)
open import DASHI.Foundations.Base369Nat using (_%_)

q : Nat
q = 3329

data D9 : Set where
  n4 n3 n2 n1 z p1 p2 p3 p4 : D9

residue : D9 → Nat
residue n4 = 3325
residue n3 = 3326
residue n2 = 3327
residue n1 = 3328
residue z  = 0
residue p1 = 1
residue p2 = 2
residue p3 = 3
residue p4 = 4

allD9 : List D9
allD9 = n4 ∷ n3 ∷ n2 ∷ n1 ∷ z ∷ p1 ∷ p2 ∷ p3 ∷ p4 ∷ []

------------------------------------------------------------------------
-- Tiny Boolean/list proof kit, kept local so the certificate has no extra
-- finite-set dependency.
------------------------------------------------------------------------

and : Bool → Bool → Bool
and true true = true
and _ _ = false

implies : Bool → Bool → Bool
implies true consequence = consequence
implies false consequence = true

andTrue : ∀ {a b} → a ≡ true → b ≡ true → and a b ≡ true
andTrue refl refl = refl

andLeftTrue : ∀ {a b} → and a b ≡ true → a ≡ true
andLeftTrue {true} {true} refl = refl
andLeftTrue {true} {false} ()
andLeftTrue {false} {true} ()
andLeftTrue {false} {false} ()

andRightTrue : ∀ {a b} → and a b ≡ true → b ≡ true
andRightTrue {true} {true} refl = refl
andRightTrue {true} {false} ()
andRightTrue {false} {true} ()
andRightTrue {false} {false} ()

impliesTrueElim :
  ∀ {antecedent consequence} →
  implies antecedent consequence ≡ true →
  antecedent ≡ true →
  consequence ≡ true
impliesTrueElim implication refl = implication

natEqSelf : (n : Nat) → (n == n) ≡ true
natEqSelf zero = refl
natEqSelf (suc n) = natEqSelf n

data _∈D9_ (x : D9) : List D9 → Set where
  here : ∀ {xs} → x ∈D9 (x ∷ xs)
  there : ∀ {y xs} → x ∈D9 xs → x ∈D9 (y ∷ xs)

d9Complete : (x : D9) → x ∈D9 allD9
d9Complete n4 = here
d9Complete n3 = there here
d9Complete n2 = there (there here)
d9Complete n1 = there (there (there here))
d9Complete z  = there (there (there (there here)))
d9Complete p1 = there (there (there (there (there here))))
d9Complete p2 = there (there (there (there (there (there here)))))
d9Complete p3 = there (there (there (there (there (there (there here))))))
d9Complete p4 = there (there (there (there (there (there (there (there here)))))))

any : (D9 → Bool) → List D9 → Bool
any f [] = false
any f (x ∷ xs) with f x
... | true = true
... | false = any f xs

all : (D9 → Bool) → List D9 → Bool
all f [] = true
all f (x ∷ xs) = and (f x) (all f xs)

anyTrueIfMember :
  (f : D9 → Bool) →
  ∀ {x xs} →
  x ∈D9 xs →
  f x ≡ true →
  any f xs ≡ true
anyTrueIfMember f here fx rewrite fx = refl
anyTrueIfMember f (there {y = y} member) fx with f y
... | true = refl
... | false = anyTrueIfMember f member fx

allTrueAt :
  (f : D9 → Bool) →
  ∀ {x xs} →
  x ∈D9 xs →
  all f xs ≡ true →
  f x ≡ true
allTrueAt f here allTrue = andLeftTrue allTrue
allTrueAt f (there member) allTrue =
  allTrueAt f member (andRightTrue allTrue)

------------------------------------------------------------------------
-- 4+4 compression and the reduced pair-(0,3) equations.
------------------------------------------------------------------------

compressed : D9 → D9 → Nat
compressed low high = (residue low + 296 * residue high) % q

pFrom : D9 → D9 → D9 → D9 → Nat
pFrom e2Low e2High e3Low e3High =
  (compressed e2Low e2High + 585 * compressed e3Low e3High) % q

predictedE0 : D9 → D9 → D9 → D9 → Nat
predictedE0 e2Low e2High e3Low e3High =
  (2998 * pFrom e2Low e2High e3Low e3High) % q

predictedE1 : D9 → D9 → D9 → D9 → Nat
predictedE1 e2Low e2High e3Low e3High =
  (2744 * pFrom e2Low e2High e3Low e3High
   + 2998 * compressed e3Low e3High) % q

-- 2998 = -331 mod 3329 and 2744 = -585 mod 3329.
minus331Residue : (3329 + 0) % q ≡ 0
minus331Residue = refl

------------------------------------------------------------------------
-- Membership in the 81-element compressed coefficient support.
------------------------------------------------------------------------

residueMember : Nat → Bool
residueMember target =
  any
    (λ low →
      any
        (λ high → compressed low high == target)
        allD9)
    allD9

residueMemberSelf :
  (low high : D9) →
  residueMember (compressed low high) ≡ true
residueMemberSelf low high =
  anyTrueIfMember
    (λ candidateLow →
      any
        (λ candidateHigh → compressed candidateLow candidateHigh == compressed low high)
        allD9)
    (d9Complete low)
    (anyTrueIfMember
      (λ candidateHigh → compressed low candidateHigh == compressed low high)
      (d9Complete high)
      (natEqSelf (compressed low high)))

------------------------------------------------------------------------
-- Closed reduced checker: only 9^4 = 6561 source clauses are normalized, and
-- each clause represents one S^2 coefficient pair, not one original secret.
------------------------------------------------------------------------

isZero : D9 → Bool
isZero z = true
isZero _ = false

allZero4 : D9 → D9 → D9 → D9 → Bool
allZero4 e2Low e2High e3Low e3High =
  and (and (isZero e2Low) (isZero e2High))
      (and (isZero e3Low) (isZero e3High))

survivesReducedKernel : D9 → D9 → D9 → D9 → Bool
survivesReducedKernel e2Low e2High e3Low e3High =
  and
    (residueMember (predictedE0 e2Low e2High e3Low e3High))
    (residueMember (predictedE1 e2Low e2High e3Low e3High))

reducedClause : D9 → D9 → D9 → D9 → Bool
reducedClause e2Low e2High e3Low e3High =
  implies
    (survivesReducedKernel e2Low e2High e3Low e3High)
    (allZero4 e2Low e2High e3Low e3High)

all4 : (D9 → D9 → D9 → D9 → Bool) → Bool
all4 predicate =
  all
    (λ a →
      all
        (λ b →
          all
            (λ c →
              all (λ d → predicate a b c d) allD9)
            allD9)
        allD9)
    allD9

all4TrueAt :
  (predicate : D9 → D9 → D9 → D9 → Bool) →
  all4 predicate ≡ true →
  (a b c d : D9) →
  predicate a b c d ≡ true
all4TrueAt predicate global a b c d =
  allTrueAt
    (λ d′ → predicate a b c d′)
    (d9Complete d)
    level3
  where
  level1 :
    all
      (λ b′ →
        all
          (λ c′ → all (λ d′ → predicate a b′ c′ d′) allD9)
          allD9)
      allD9
    ≡ true
  level1 =
    allTrueAt
      (λ a′ →
        all
          (λ b′ →
            all
              (λ c′ → all (λ d′ → predicate a′ b′ c′ d′) allD9)
              allD9)
          allD9)
      (d9Complete a)
      global

  level2 :
    all
      (λ c′ → all (λ d′ → predicate a b c′ d′) allD9)
      allD9
    ≡ true
  level2 =
    allTrueAt
      (λ b′ →
        all
          (λ c′ → all (λ d′ → predicate a b′ c′ d′) allD9)
          allD9)
      (d9Complete b)
      level1

  level3 : all (λ d′ → predicate a b c d′) allD9 ≡ true
  level3 =
    allTrueAt
      (λ c′ → all (λ d′ → predicate a b c′ d′) allD9)
      (d9Complete c)
      level2

pair03ReducedKernelCheck : Bool
pair03ReducedKernelCheck = all4 reducedClause

pair03ReducedKernelCheckIsTrue : pair03ReducedKernelCheck ≡ true
pair03ReducedKernelCheckIsTrue = refl

------------------------------------------------------------------------
-- The separate 81-state fact: compressed residue zero has only the zero pair.
------------------------------------------------------------------------

compressionZeroClause : D9 → D9 → Bool
compressionZeroClause low high =
  implies
    (compressed low high == 0)
    (and (isZero low) (isZero high))

all2 : (D9 → D9 → Bool) → Bool
all2 predicate =
  all (λ low → all (λ high → predicate low high) allD9) allD9

all2TrueAt :
  (predicate : D9 → D9 → Bool) →
  all2 predicate ≡ true →
  (low high : D9) →
  predicate low high ≡ true
all2TrueAt predicate global low high =
  allTrueAt
    (λ high′ → predicate low high′)
    (d9Complete high)
    (allTrueAt
      (λ low′ → all (λ high′ → predicate low′ high′) allD9)
      (d9Complete low)
      global)

compressionZeroCheck : Bool
compressionZeroCheck = all2 compressionZeroClause

compressionZeroCheckIsTrue : compressionZeroCheck ≡ true
compressionZeroCheckIsTrue = refl

isZeroReflects : ∀ x → isZero x ≡ true → x ≡ z
isZeroReflects n4 ()
isZeroReflects n3 ()
isZeroReflects n2 ()
isZeroReflects n1 ()
isZeroReflects z refl = refl
isZeroReflects p1 ()
isZeroReflects p2 ()
isZeroReflects p3 ()
isZeroReflects p4 ()

compressedZeroOnlyZero :
  (low high : D9) →
  compressed low high ≡ 0 →
  (low ≡ z) × (high ≡ z)
compressedZeroOnlyZero low high compressedZero =
  isZeroReflects low (andLeftTrue zeroPair) ,
  isZeroReflects high (andRightTrue zeroPair)
  where
  eqBool : (compressed low high == 0) ≡ true
  eqBool = subst (λ value → (value == 0) ≡ true) (sym compressedZero) refl

  zeroPair : and (isZero low) (isZero high) ≡ true
  zeroPair =
    impliesTrueElim
      (all2TrueAt compressionZeroClause compressionZeroCheckIsTrue low high)
      eqBool

------------------------------------------------------------------------
-- Semantic reduced-kernel theorem.
------------------------------------------------------------------------

reducedSurvivorOnlyZero :
  (e2Low e2High e3Low e3High : D9) →
  survivesReducedKernel e2Low e2High e3Low e3High ≡ true →
  ((e2Low ≡ z) × (e2High ≡ z)) ×
  ((e3Low ≡ z) × (e3High ≡ z))
reducedSurvivorOnlyZero e2Low e2High e3Low e3High survivor =
  ( isZeroReflects e2Low (andLeftTrue leftZero)
  , isZeroReflects e2High (andRightTrue leftZero)
  ) ,
  ( isZeroReflects e3Low (andLeftTrue rightZero)
  , isZeroReflects e3High (andRightTrue rightZero)
  )
  where
  clauseTrue : reducedClause e2Low e2High e3Low e3High ≡ true
  clauseTrue =
    all4TrueAt
      reducedClause
      pair03ReducedKernelCheckIsTrue
      e2Low e2High e3Low e3High

  zero4 : allZero4 e2Low e2High e3Low e3High ≡ true
  zero4 = impliesTrueElim clauseTrue survivor

  leftZero : and (isZero e2Low) (isZero e2High) ≡ true
  leftZero = andLeftTrue zero4

  rightZero : and (isZero e3Low) (isZero e3High) ≡ true
  rightZero = andRightTrue zero4

------------------------------------------------------------------------
-- Full eight-difference theorem once the cubic root-factor equations have been
-- supplied by the preceding algebraic module / F_3329 instantiation.
------------------------------------------------------------------------

compactPair03BoundedKernelOnlyZero :
  (d0 d1 d2 d3 d4 d5 d6 d7 : D9) →
  compressed d0 d4 ≡ predictedE0 d2 d6 d3 d7 →
  compressed d1 d5 ≡ predictedE1 d2 d6 d3 d7 →
  (((d0 ≡ z) × (d4 ≡ z)) ×
   ((d1 ≡ z) × (d5 ≡ z))) ×
  (((d2 ≡ z) × (d6 ≡ z)) ×
   ((d3 ≡ z) × (d7 ≡ z)))
compactPair03BoundedKernelOnlyZero
  d0 d1 d2 d3 d4 d5 d6 d7 e0Equation e1Equation =
  ((d0Zero , d4Zero) , (d1Zero , d5Zero)) , reducedZero
  where
  e0Member : residueMember (predictedE0 d2 d6 d3 d7) ≡ true
  e0Member =
    subst
      (λ target → residueMember target ≡ true)
      e0Equation
      (residueMemberSelf d0 d4)

  e1Member : residueMember (predictedE1 d2 d6 d3 d7) ≡ true
  e1Member =
    subst
      (λ target → residueMember target ≡ true)
      e1Equation
      (residueMemberSelf d1 d5)

  survivor : survivesReducedKernel d2 d6 d3 d7 ≡ true
  survivor = andTrue e0Member e1Member

  reducedZero :
    ((d2 ≡ z) × (d6 ≡ z)) × ((d3 ≡ z) × (d7 ≡ z))
  reducedZero = reducedSurvivorOnlyZero d2 d6 d3 d7 survivor

  d2Zero : d2 ≡ z
  d2Zero = Data.Product.proj₁ (Data.Product.proj₁ reducedZero)

  d6Zero : d6 ≡ z
  d6Zero = Data.Product.proj₂ (Data.Product.proj₁ reducedZero)

  d3Zero : d3 ≡ z
  d3Zero = Data.Product.proj₁ (Data.Product.proj₂ reducedZero)

  d7Zero : d7 ≡ z
  d7Zero = Data.Product.proj₂ (Data.Product.proj₂ reducedZero)

  predictedE0Zero : predictedE0 d2 d6 d3 d7 ≡ 0
  predictedE0Zero rewrite d2Zero | d6Zero | d3Zero | d7Zero = refl

  predictedE1Zero : predictedE1 d2 d6 d3 d7 ≡ 0
  predictedE1Zero rewrite d2Zero | d6Zero | d3Zero | d7Zero = refl

  compressedD0D4Zero : compressed d0 d4 ≡ 0
  compressedD0D4Zero =
    Relation.Binary.PropositionalEquality.trans e0Equation predictedE0Zero

  compressedD1D5Zero : compressed d1 d5 ≡ 0
  compressedD1D5Zero =
    Relation.Binary.PropositionalEquality.trans e1Equation predictedE1Zero

  d0d4Zero : (d0 ≡ z) × (d4 ≡ z)
  d0d4Zero = compressedZeroOnlyZero d0 d4 compressedD0D4Zero

  d1d5Zero : (d1 ≡ z) × (d5 ≡ z)
  d1d5Zero = compressedZeroOnlyZero d1 d5 compressedD1D5Zero

  d0Zero : d0 ≡ z
  d0Zero = Data.Product.proj₁ d0d4Zero

  d4Zero : d4 ≡ z
  d4Zero = Data.Product.proj₂ d0d4Zero

  d1Zero : d1 ≡ z
  d1Zero = Data.Product.proj₁ d1d5Zero

  d5Zero : d5 ≡ z
  d5Zero = Data.Product.proj₂ d1d5Zero

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- This file closes the bounded finite kernel after cubic root-factor reduction
-- using 6561 reduced states rather than 390625 source candidates.  The remaining
-- same-object bridge is source arithmetic: instantiate the generic cubic theorem
-- over F_3329 and derive the two reduced equations from equality of the actual
-- pair-(0,3) raw signatures.  Physical observation coarsening remains separate.
------------------------------------------------------------------------
