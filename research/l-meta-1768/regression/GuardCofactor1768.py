"""Build guard-aware constant-folding windows and count net gates and all lost edges."""

from collections import Counter
from functools import lru_cache
from itertools import combinations

from BatchExceptions1768 import build_exceptions
from SharedBirth1768 import build
from SharedStop1768 import evaluate, graph_output, indicators


def guarded_window(gates, output, tops, anchor, independent_group=None):
    """Pin to one inside its own guard, and to zero in the selected other terms.

    An independent group keeps every term outside the group intact. With no
    group, all other terms are specialized. The output OR tree is rebuilt once.
    """
    definitions = {name: (op, left, right) for name, op, left, right in gates}
    built = []
    versions = {}

    def emit(origin, op, left, right):
        if left is False or right is False:
            return False if op == "and" else (right if left is False else left)
        if left is True or right is True:
            return True if op == "or" else (right if left is True else left)
        key = (origin, op, *sorted((left, right)))
        if key not in versions:
            name = f"cofactor.{len(built)}"
            versions[key] = name
            built.append((name, op, left, right, origin))
        return versions[key]

    @lru_cache(None)
    def specialize(name, pinned):
        if pinned is not None and name == anchor:
            return pinned
        if name not in definitions:
            return name
        op, left, right = definitions[name]
        return emit(name, op, specialize(left, pinned), specialize(right, pinned))

    @lru_cache(None)
    def rebuild_output(name):
        op, left, right = definitions[name]
        if name in tops:
            assert op == "and"
            if anchor in (left, right):
                other = right if left == anchor else left
                return emit(name, op, anchor, specialize(other, True))
            if independent_group is None or left in independent_group or right in independent_group:
                return specialize(name, False)
            return specialize(name, None)
        assert op == "or"
        return emit(name, op, rebuild_output(left), rebuild_output(right))

    out = rebuild_output(output)
    live = {out}
    kept = []
    origins = Counter()
    for name, op, left, right, origin in reversed(built):
        if name in live:
            kept.append((name, op, left, right))
            live.update((left, right))
            origins[origin] += 1
    dead = set(definitions) - origins.keys()
    copies = sum(n - 1 for n in origins.values())
    assert len(gates) - len(kept) == len(dead) - copies
    return list(reversed(kept)), out, dead, copies


def verify_windows(inputs, gates, all_edges, tops, root, anchors, *, independent_group=None):
    if independent_group is not None:
        assert all(not e <= independent_group for e in all_edges)
    samples = sorted(all_edges, key=lambda e: tuple(sorted(e)))
    signals = indicators(inputs, samples)
    values = evaluate(gates, signals)
    full = (1 << len(samples)) - 1
    assert values[root] == full
    by_guard = {u: [] for u in anchors}
    for name, _, left, right in gates:
        if name not in tops:
            continue
        for u in {left, right} & by_guard.keys():
            by_guard[u].append(name)
    inc = {u: sum(1 << i for i, e in enumerate(samples) if u in e) for u in anchors}

    savings, lost, copied, killed, grew, nonincreasing = 0, 0, 0, 0, 0, 0
    for u in anchors:
        out_gates, out, dead, copies = guarded_window(gates, root, tops, u, independent_group)
        assert out is not True
        after = evaluate(out_gates, signals).get(out, 0)
        protected = 0
        for t in by_guard[u]:
            protected |= values[t]
        expected_lost = inc[u] & ~protected if independent_group is None else 0
        assert after == full ^ expected_lost
        net = len(gates) - len(out_gates)
        if net < 0:
            grew += 1
            continue
        nonincreasing += 1
        killed += len(dead)
        copied += copies
        savings += net
        lost += expected_lost.bit_count()

    assert savings == killed - copied
    return nonincreasing, grew, killed, copied, savings, lost


def affine_examples():
    for p in (5, 7, 11):
        inputs, gates, E, ns, _, _, tops, out = build(p)
        A = set(ns)
        B = {v for partners in ns.values() for v in partners}
        line = verify_windows(inputs, gates, E, tops, out, sorted(A))
        point = verify_windows(inputs, gates, E, tops, out, sorted(B))
        restricted = verify_windows(inputs, gates, E, tops, out, sorted(A), independent_group=A)
        print(f"affine p={p}: m={len(gates)}, core={p ** 3}")
        print(f"  line all-other-zero={line}; point all-other-zero={point}; line group={restricted}")

    inputs, gates, E, tops, core, _, _, _, _, _, _, out = build_exceptions(5, 3, True)
    A = set(build(5)[3])
    line = verify_windows(inputs, gates, E, tops, out, sorted(A))
    group = verify_windows(inputs, gates, E, tops, out, sorted(A), independent_group=A)
    print(f"exceptions p=5: m={len(gates)}, core={len(core)}")
    print(f"  line all-other-zero={line}; line group={group}")


def copy_growth_example():
    inputs = ["u", "v", "x", "a", "b"]
    edges = {frozenset(("u", "x")), frozenset(("v", "x"))}
    gates = [("r", "or", "u", "a"), ("s", "and", "r", "x"), ("h0", "or", "s", "x")]
    for i in range(1, 4):
        child = f"h{i - 1}"
        gates.extend([(f"t{i}", "and", child, "b"), (f"h{i}", "or", child, f"t{i}")])
    gates.extend([("tu", "and", "u", "h3"), ("tv", "and", "v", "h3"),
                  ("out", "or", "tu", "tv")])
    after, out, dead, copies = guarded_window(gates, "out", {"tu", "tv"}, "u")
    samples = [frozenset(s) for i in range(len(inputs) + 1) for s in combinations(inputs, i)]
    signals = indicators(inputs, samples)
    assert evaluate(gates, signals)["out"] == evaluate(after, signals)[out]
    assert evaluate(after, signals)[out] == graph_output(edges, samples)
    assert len(after) > len(gates)
    print(f"copy growth: {len(gates)} -> {len(after)} gates, {len(dead)} dead, "
          f"{copies} copies, zero lost edges on all {len(samples)} assignments")


if __name__ == "__main__":
    print("fields=(nonincreasing, grew, dead, copies, net_saved, all_graph_losses)")
    affine_examples()
    copy_growth_example()
