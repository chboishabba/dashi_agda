# Exact amplitude decoration of Mathieu divisor paths

`DASHI.Moonshine.MathieuDivisorPathInterferenceExact` upgrades the Round-6 divisor-lattice confluence skeleton with explicit exact amplitudes.

The divisor module already supplies two distinct prime-coloured histories

```text
1 --x2--> 2 --x3--> 6
1 --x3--> 3 --x2--> 6.
```

The path-interference module packages them as a `ConfluentHistoryPair`, assigns each history an independent Eisenstein amplitude, and defines

```text
node amplitude = left amplitude + right amplitude
node intensity = norm(node amplitude).
```

Using the exact Eisenstein polarization theorem, it proves

```text
node intensity
  = norm(left amplitude)
  + norm(right amplitude)
  + cross(left amplitude, right amplitude).
```

For the canonical decoration

```text
left amplitude  = 1
right amplitude = omega,
```

it proves

```text
diagonal intensity = 2
cross term          = -1
node intensity      = 1.
```

This is now an actual finite coherent-amplitude model rather than only an analogy from convergent factor histories. The amplitudes remain additional data: divisor incidence does not determine them, and no physical quantum dynamics is claimed.

Primary source for the Eisenstein carrier:

- Serge Lang, *Algebraic Number Theory*, second edition, Springer, 1994. DOI `10.1007/978-1-4612-0853-2`.
