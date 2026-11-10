"""DASHI independent circuit/netlist reference. No vendor CAD or circuit claims.

Topology and path search only; not KCL/KVL, physical simulation or efficiency.
"""
from dataclasses import dataclass
from heapq import heappop, heappush
from math import inf
import json

@dataclass(frozen=True)
class Part:
    id: str
    kind: str
    pins: tuple[str, ...]
    value: float | None = None
    unit: str | None = None

@dataclass(frozen=True)
class Wire:
    src: str
    dst: str
    weight: int = 1

@dataclass
class Netlist:
    parts: list[Part]
    wires: list[Wire]
    attribution: str
    revision: str

    def validate(self):
        names = [p.id for p in self.parts]
        assert len(set(names)) == len(names), "duplicate part id"
        endpoints = {f"{p.id}.{pin}" for p in self.parts for pin in p.pins}
        for w in self.wires:
            assert w.src in endpoints and w.dst in endpoints, (w.src, w.dst)
            assert w.weight >= 0, "negative path cost unsupported by Dijkstra/A*"
        for p in self.parts:
            assert p.value is None or (p.unit is not None and p.value >= 0)

    def graph(self):
        self.validate()
        g = {f"{p.id}.{pin}": [] for p in self.parts for pin in p.pins}
        for w in self.wires:
            g[w.src].append((w.dst, w.weight))
        return g

    def diagram(self):
        self.validate()
        # Explicit wire edges only; no unproved internal conduction.
        out = ["digraph wiring {", "  rankdir=LR;"]
        for p in self.parts:
            val = f"\\n{p.value} {p.unit}" if p.value is not None else ""
            out.append(f'  "{p.id}" [label="{p.id}: {p.kind}{val}"];')
        for w in self.wires:
            a, b = w.src.split(".")[0], w.dst.split(".")[0]
            out.append(f'  "{a}" -> "{b}" [label="{w.src} to {w.dst}"];')
        return "\n".join(out + ["}"])

def shortest_path(g, source, target, heuristic=lambda _n: 0):
    """A* on nonnegative edge weights; zero heuristic gives Dijkstra.

    Nonzero heuristics require an external admissibility proof for optimality.
    """
    best = {source: 0}
    heap = [(heuristic(source), 0, source)]
    parent = {}
    while heap:
        _f, dist, node = heappop(heap)
        if dist != best[node]:
            continue
        if node == target:
            path = [node]
            while node in parent:
                node = parent[node]
                path.append(node)
            return dist, path[::-1]
        for nxt, weight in g[node]:
            new = dist + weight
            if new < best.get(nxt, inf):
                best[nxt] = new
                parent[nxt] = node
                heappush(heap, (new + heuristic(nxt), new, nxt))
    return None

def sector_3_9_27(k: int):
    """Finite phase hierarchy: no intrinsic physical 27-phase assertion."""
    assert 0 <= k < 27
    return {"C27": k, "C9": k // 3, "C3": k // 9}

def illustrative_rc():
    return Netlist(
        [Part("V1", "source", ("+", "-"), 12, "V"),
         Part("R1", "resistor", ("a","b"), 1000, "ohm"),
         Part("C1", "capacitor", ("a","b"), 3.3, "uF")],
        [Wire("V1.+","R1.a"), Wire("R1.b","C1.a"),
         Wire("C1.b","V1.-")],
        "DASHI illustrative circuit, not Resonate369 vendor wiring",
        "example-1")

def self_test():
    n = illustrative_rc()
    n.validate()
    g = n.graph()
    assert shortest_path(g, "V1.+", "R1.a") == (1, ["V1.+","R1.a"])
    assert shortest_path(g, "V1.+", "C1.a") is None
    assert sector_3_9_27(0) == {"C27":0,"C9":0,"C3":0}
    assert sector_3_9_27(26) == {"C27":26,"C9":8,"C3":2}
    toy = {"s":[("a",2),("b",5)], "a":[("t",2)],
           "b":[("t",1)], "t":[]}
    h = {"s":3,"a":2,"b":1,"t":0}
    assert all(h[u] <= w + h[v]
               for u,edges in toy.items() for v,w in edges)
    assert shortest_path(toy,"s","t",lambda k:h[k]) == (4,["s","a","t"])
    assert shortest_path(toy,"s","t") == (4,["s","a","t"])
    return {"status":"passed", "checks":9}

if __name__ == "__main__":
    print(json.dumps(self_test(),indent=2))
    print(illustrative_rc().diagram())
