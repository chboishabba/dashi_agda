"""Linear weight coordinates on the original action; right-action convention.
No numerical Monster action or source authentication is manufactured here.
The backend must supply exact scalar and vector operations and genuine words.
"""
from itertools import product


class WeightFrame:
    def __init__(self, act, add, scale, zeta, one, z, translations, modulations):
        if len(translations) != len(modulations):
            raise ValueError('unpaired source axes')
        if zeta**3 != one or zeta == one:
            raise ValueError('invalid marked root')
        self.act, self.add, self.scale = act, add, scale
        self.zeta, self.one, self.z = zeta, one, z
        self.T, self.B = tuple(translations), tuple(modulations)
        self.points = tuple(product(range(3), repeat=len(self.T)))
        self.inv3 = one / (3*one)

    def phase(self, v, s):
        if s not in (0, 1, 2):
            raise ValueError('invalid phase')
        a = self.scale(self.zeta**(-s), self.act(v, self.z))
        b = self.scale(self.zeta**(-2*s), self.act(v, self.z**2))
        return self.scale(self.inv3, self.add(v, self.add(a, b)))

    def vacuum(self, v, s):
        if s not in (1, 2):
            raise ValueError('centre-trivial sector has no Schr frame')
        v = self.phase(v, s)
        for b in self.B:
            v = self.scale(self.inv3, self.add(v, self.add(self.act(v, b), self.act(v, b**2))))
        return v

    def translate(self, v, x, reverse=False):
        if len(x) != len(self.T) or any(t not in (0, 1, 2) for t in x):
            raise ValueError('invalid weight')
        pairs = list(zip(self.T, x))
        if reverse:
            pairs.reverse()
        for t, a in pairs:
            if a:
                v = self.act(v, t**(-a if reverse else a))
        return v

    def recover_weight(self, v, s, x):
        return self.vacuum(self.translate(v, x, True), s)

    def recover(self, v):
        return self.phase(v, 0), {s: tuple(self.recover_weight(v, s, x) for x in self.points) for s in (1, 2)}

    def evaluate(self, zero, phases):
        if set(phases) != {1, 2} or any(len(phases[s]) != len(self.points) for s in (1, 2)):
            raise ValueError('complete signed coordinate family required')
        v = zero
        for s in (1, 2):
            for x, u in zip(self.points, phases[s]):
                v = self.add(v, self.translate(u, x))
        return v

    def hom(self, v, s, target, word, k):
        if s not in (1, 2) or target not in (1, 2) or k == self.one-self.one:
            raise ValueError('invalid signed vacuum coefficient')
        return self.scale(self.one/k, self.vacuum(self.act(v, word), target))

    def split(self, v, s, c_squared):
        # Canonical Weil parity fixes e_0, so the C² vacuum scalar is 1.
        j = self.hom(v, s, s, c_squared, self.one)
        half = self.one/(2*self.one)
        return self.scale(half, self.add(v, self.scale(-self.one, j))), self.scale(half, self.add(v, j))
