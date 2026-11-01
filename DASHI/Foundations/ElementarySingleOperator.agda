module DASHI.Foundations.ElementarySingleOperator where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- The source language is deliberately the exact exp/log/sub/1 kernel.
-- A scientific-calculator front end may lower into this language, while the
-- theorem below proves that the remaining backend uses one repeated binary
-- node only.

Var : Set
Var = Nat

data ExpLogSubExpr : Set where
  oneE : ExpLogSubExpr
  varE : Var → ExpLogSubExpr
  expE : ExpLogSubExpr → ExpLogSubExpr
  logE : ExpLogSubExpr → ExpLogSubExpr
  subE : ExpLogSubExpr → ExpLogSubExpr → ExpLogSubExpr

data EMLExpr : Set where
  oneM : EMLExpr
  varM : Var → EMLExpr
  emlM : EMLExpr → EMLExpr → EMLExpr

record ExpLogSubModel : Set₁ where
  field
    Carrier : Set
    one : Carrier
    exp : Carrier → Carrier
    log : Carrier → Carrier
    sub : Carrier → Carrier → Carrier

open ExpLogSubModel public

Env : ExpLogSubModel → Set
Env M = Var → Carrier M

evalSource :
  (M : ExpLogSubModel) →
  Env M →
  ExpLogSubExpr →
  Carrier M
evalSource M ρ oneE = one M
evalSource M ρ (varE x) = ρ x
evalSource M ρ (expE t) = exp M (evalSource M ρ t)
evalSource M ρ (logE t) = log M (evalSource M ρ t)
evalSource M ρ (subE s t) = sub M (evalSource M ρ s) (evalSource M ρ t)

eml :
  (M : ExpLogSubModel) →
  Carrier M →
  Carrier M →
  Carrier M
eml M x y = sub M (exp M x) (log M y)

evalEML :
  (M : ExpLogSubModel) →
  Env M →
  EMLExpr →
  Carrier M
evalEML M ρ oneM = one M
evalEML M ρ (varM x) = ρ x
evalEML M ρ (emlM s t) = eml M (evalEML M ρ s) (evalEML M ρ t)

------------------------------------------------------------------------
-- Canonical EML encodings from arXiv:2603.21852v2.

emlExp : EMLExpr → EMLExpr
emlExp t = emlM t oneM

emlLog : EMLExpr → EMLExpr
emlLog t = emlM oneM (emlM (emlM oneM t) oneM)

emlSub : EMLExpr → EMLExpr → EMLExpr
emlSub s t = emlM (emlLog s) (emlExp t)

compileEML : ExpLogSubExpr → EMLExpr
compileEML oneE = oneM
compileEML (varE x) = varM x
compileEML (expE t) = emlExp (compileEML t)
compileEML (logE t) = emlLog (compileEML t)
compileEML (subE s t) = emlSub (compileEML s) (compileEML t)

------------------------------------------------------------------------
-- The branch-sensitive analytic content is isolated here.  These are not
-- global identities of an arbitrary logarithm; an implementation must supply
-- them on its chosen admissible domain and branch.

record EMLCompilerLaws (M : ExpLogSubModel) : Set₁ where
  field
    expEncoding :
      ∀ x →
      eml M x (one M) ≡ exp M x

    logEncoding :
      ∀ x →
      eml M (one M)
        (eml M (eml M (one M) x) (one M))
      ≡ log M x

    subEncoding :
      ∀ x y →
      eml M
        (eml M (one M)
          (eml M (eml M (one M) x) (one M)))
        (eml M y (one M))
      ≡ sub M x y

open EMLCompilerLaws public

compileEML-correct :
  ∀ (M : ExpLogSubModel) →
  EMLCompilerLaws M →
  (ρ : Env M) →
  (t : ExpLogSubExpr) →
  evalEML M ρ (compileEML t) ≡ evalSource M ρ t
compileEML-correct M laws ρ oneE = refl
compileEML-correct M laws ρ (varE x) = refl
compileEML-correct M laws ρ (expE t)
  rewrite compileEML-correct M laws ρ t =
  expEncoding laws (evalSource M ρ t)
compileEML-correct M laws ρ (logE t)
  rewrite compileEML-correct M laws ρ t =
  logEncoding laws (evalSource M ρ t)
compileEML-correct M laws ρ (subE s t)
  rewrite compileEML-correct M laws ρ s
        | compileEML-correct M laws ρ t =
  subEncoding laws (evalSource M ρ s) (evalSource M ρ t)

------------------------------------------------------------------------
-- Generic scientific-language lowering seam.  This prevents the repository
-- from claiming more than has actually been supplied: universality for a
-- concrete front end follows from an explicit, semantics-preserving lowering.

record ElementaryFrontEnd (M : ExpLogSubModel) : Set₁ where
  field
    Syntax : Set
    eval : Env M → Syntax → Carrier M
    lower : Syntax → ExpLogSubExpr
    lower-correct :
      ∀ ρ t →
      evalSource M ρ (lower t) ≡ eval ρ t

open ElementaryFrontEnd public

compileElementary :
  ∀ {M : ExpLogSubModel} →
  (F : ElementaryFrontEnd M) →
  Syntax F →
  EMLExpr
compileElementary F t = compileEML (lower F t)

compileElementary-correct :
  ∀ {M : ExpLogSubModel} →
  (laws : EMLCompilerLaws M) →
  (F : ElementaryFrontEnd M) →
  (ρ : Env M) →
  (t : Syntax F) →
  evalEML M ρ (compileElementary F t) ≡ eval F ρ t
compileElementary-correct laws F ρ t
  rewrite compileEML-correct _ laws ρ (lower F t) =
  lower-correct F ρ t
