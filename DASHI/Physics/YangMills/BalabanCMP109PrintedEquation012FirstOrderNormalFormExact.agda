module DASHI.Physics.YangMills.BalabanCMP109PrintedEquation012FirstOrderNormalFormExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Gate I does not need three independent endpoint claims
--
--   Frechet derivative = printed DAG,
--   printed DAG       = L13 matrix,
--   remainder         = little-o.
--
-- The consumer needs one source-faithful normal form for the same printed
-- equation-(0.12) object.  This module proves the equality-collapse step once:
-- if the literal printed increment is exactly base + semantic derivative +
-- remainder and the semantic derivative action is exactly the already-owned
-- L13 action, then the literal increment is exactly
--
--   base + L13-action + remainder.
--
-- The theorem deliberately acts on VALUES, not on equality of abstract
-- derivative records, so the matrix whose Schur bound is used cannot be
-- silently replaced after the Frechet proof.
--
-- Round-46 authority tightening: the little-o witness is now bundled with the
-- same-object equality.  Downstream Gate-I geometry can therefore consume one
-- object carrying BOTH
--
--   Q_print(A+h) = Q_print(A) + M_A h + r_A(h)
--
-- and the assertion that this very same r_A is little-o.  The L13 action is
-- not separately re-selectable after the authority object is formed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record FirstOrderSameObjectData
    (Output Direction : Set) : Set₁ where
  field
    add : Output → Output → Output
    printedBase : Output
    printedPerturbed : Direction → Output
    semanticDerivativeAction : Direction → Output
    l13DerivativeAction : Direction → Output
    remainder : Direction → Output

    printedFrechetExpansionExact : ∀ h →
      printedPerturbed h
      ≡ add (add printedBase (semanticDerivativeAction h)) (remainder h)

    semanticDerivativeIsL13Action : ∀ h →
      semanticDerivativeAction h ≡ l13DerivativeAction h

open FirstOrderSameObjectData public

printedEquation012FirstOrderNormalFormExact :
  ∀ {Output Direction}
    (data : FirstOrderSameObjectData Output Direction)
    (h : Direction) →
  printedPerturbed data h
  ≡ add data
      (add data (printedBase data) (l13DerivativeAction data h))
      (remainder data h)
printedEquation012FirstOrderNormalFormExact data h
  with printedFrechetExpansionExact data h
     | semanticDerivativeIsL13Action data h
... | refl | refl = refl

------------------------------------------------------------------------
-- Single downstream authority.
------------------------------------------------------------------------

record PrintedEquation012NormalFormAuthority
    (Output Direction : Set) : Set₂ where
  field
    sameObject : FirstOrderSameObjectData Output Direction

    -- Kept abstract on purpose: concrete consumers instantiate the ordinary
    -- finite-dimensional little-o predicate in their selected norm.  What is
    -- important here is ownership: the predicate applies to `remainder` from
    -- the SAME object whose derivative action is the literal L13 action.
    LittleOAtZero : (Direction → Output) → Set
    remainderLittleO : LittleOAtZero (remainder sameObject)

open PrintedEquation012NormalFormAuthority public

authoritativePrintedEquation012NormalForm :
  ∀ {Output Direction}
    (authority : PrintedEquation012NormalFormAuthority Output Direction)
    (h : Direction) →
  printedPerturbed (sameObject authority) h
  ≡ add (sameObject authority)
      (add (sameObject authority)
        (printedBase (sameObject authority))
        (l13DerivativeAction (sameObject authority) h))
      (remainder (sameObject authority) h)
authoritativePrintedEquation012NormalForm authority h =
  printedEquation012FirstOrderNormalFormExact (sameObject authority) h

authoritativePrintedEquation012RemainderLittleO :
  ∀ {Output Direction}
    (authority : PrintedEquation012NormalFormAuthority Output Direction) →
  LittleOAtZero authority (remainder (sameObject authority))
authoritativePrintedEquation012RemainderLittleO authority =
  remainderLittleO authority

-- This projection exists only to make the provenance explicit in theorem
-- statements: the numerical derivative consumed downstream is definitionally
-- the L13 action owned by the authority object.
authoritativeL13DerivativeAction :
  ∀ {Output Direction} →
  PrintedEquation012NormalFormAuthority Output Direction →
  Direction → Output
authoritativeL13DerivativeAction authority =
  l13DerivativeAction (sameObject authority)

------------------------------------------------------------------------
-- Identity-point regression seam.
--
-- At the identity, a correct principal-log trivialization has derivative the
-- identity action.  Any local Frechet expansion through that derivative can
-- therefore be collapsed to `xi + remainder xi` without touching Federbush.
-- This is intentionally kept independent of equation (0.12): failure here
-- isolates a branch/trivialization error before the implicit average enters.
------------------------------------------------------------------------

record IdentityPointLogRegression (Lie Output : Set) : Set₁ where
  field
    add : Output → Output → Output
    zero : Output
    embed : Lie → Output
    principalLogAfterExp : Lie → Output
    logDerivativeAtIdentity : Lie → Output
    remainder : Lie → Output

    frechetExpansion : ∀ xi →
      principalLogAfterExp xi
      ≡ add (add zero (logDerivativeAtIdentity xi)) (remainder xi)

    derivativeIsIdentity : ∀ xi →
      logDerivativeAtIdentity xi ≡ embed xi

    zeroLeft : ∀ x → add zero x ≡ x

open IdentityPointLogRegression public

principalLogExpIdentityFirstOrderRegression :
  ∀ {Lie Output}
    (data : IdentityPointLogRegression Lie Output)
    (xi : Lie) →
  principalLogAfterExp data xi
  ≡ add data (embed data xi) (remainder data xi)
principalLogExpIdentityFirstOrderRegression data xi
  with frechetExpansion data xi
     | derivativeIsIdentity data xi
     | zeroLeft data (embed data xi)
... | refl | refl | refl = refl

cmp109PrintedEquation012FirstOrderNormalFormLevel : ProofLevel
cmp109PrintedEquation012FirstOrderNormalFormLevel = machineChecked

cmp109PrintedEquation012AuthorityBoundaryLevel : ProofLevel
cmp109PrintedEquation012AuthorityBoundaryLevel = machineChecked

cmp109PrincipalLogIdentityRegressionLevel : ProofLevel
cmp109PrincipalLogIdentityRegressionLevel = machineChecked
