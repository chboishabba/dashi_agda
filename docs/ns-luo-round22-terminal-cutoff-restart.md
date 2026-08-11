# Round 22 terminal cutoff and restart bridge

Round 22 also closes the exact order-theoretic parts of C3 and C4, while keeping their analytic inputs explicit.

## Nested shell and Galerkin limit

`NSTriadKNLuoNestedGalerkinShellLimitExact.agda` starts from a finite two-cutoff family

```text
A(N,Q) <= U.
```

For every fixed Galerkin cutoff `N`, a selected shell sequence approximates the Galerkin critical quantity:

```text
G(N) <= A(N,Q_N(k)) + e_shell(N,k),
e_shell(N,k) -> 0.
```

A selected Galerkin sequence approximates the physical critical quantity:

```text
P <= G(N(k)) + e_galerkin(k),
e_galerkin(k) -> 0.
```

With separate positive margins `m_shell` and `m_galerkin`, the module selects the Galerkin stage first and the shell stage for that chosen Galerkin cutoff, proving

```text
P <= U + m_shell + m_galerkin.
```

An explicit hypothesis

```text
U + m_shell + m_galerkin <= continuationThreshold
```

then gives the exact physical threshold.

This is the correct order of quantifiers for the nested limit.  It does not create compactness, convergence, lower semicontinuity or control of a cubic weak limit.

## Critical restart contradiction

`NSTriadKNLuoCriticalRestartContradictionExact.agda` records a critical restart interface:

```text
criticalNorm(u(t0)) <= M
  -> solution exists through t0 + tau(M,nu).
```

For a purported finite maximal time `T*`, an approach time satisfying

```text
T* < t0 + tau(M,nu)
```

and the critical bound produces a solution beyond `T*`.  The module proves that this contradicts the maximality predicate.

The local Fujita--Kato theorem, time continuity, bounded approach sequence and physical critical estimate remain analytic producers.  The logical contradiction itself is complete.

Primary metadata is recorded for Tosio Kato, *Strong Lp-Solutions of the Navier-Stokes Equation in Rm, with Applications to Weak Solutions*, DOI `10.1007/BF01174182`, and Roger Temam, *Navier-Stokes Equations: Theory and Numerical Analysis*, DOI `10.1090/chel/343`.
