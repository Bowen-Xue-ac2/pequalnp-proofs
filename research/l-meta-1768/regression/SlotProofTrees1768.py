"""Slot proof trees for true-edge assignments.

For one true edge assignment, the DP returns the OR input slots that every proof
tree must use:

* input: empty set
* AND: union of the two children
* OR: intersect over the true children of (child set + this gate's slot)

A second pass explicitly chooses one tree (first true child at each OR) and
records its slots.  Merge the chosen trees of all graph edges, then set every
other OR input slot to False.  This is a pointwise down-change: AND/OR are
monotone, so a zeroed circuit is <= the original on every assignment.  Each
edge keeps its own chosen tree, so every edge assignment remains true.  Thus no
independent-set false positive can be created.

The report prints actually retained-gate counts (not a sum of per-slot
deletability), plus pruned/constant-false gates, new repair gates, and any
graph edge missed before/after repair.

Reused helpers (not modified): ../BatchExceptions1768.rewrite and
../SharedStop1768.evaluate/indicators.  The second rerun uses SharedBirth
p=5; no 8848-gate affine builder is constructed here.
"""

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
TOOLS = HERE.parent
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from BatchExceptions1768 import rewrite
from SharedBirth1768 import build
from SharedStop1768 import evaluate, indicators


def slot_bits(gates):
    """Assign one bit to each OR input slot (name, 0/1)."""
    slot_bit, bit_slot = {}, {}
    for name, op, _, _ in gates:
        if op == "or":
            for index in (0, 1):
                bit = 1 << len(slot_bit)
                slot_bit[(name, index)] = bit
                bit_slot[bit] = (name, index)
    return slot_bit, bit_slot


def eval_point(inputs, gates, true_names):
    """Boolean values for one assignment."""
    values = {name: name in true_names for name in inputs}
    for name, op, left, right in gates:
        lv = False if left is False else values[left]
        rv = False if right is False else values[right]
        values[name] = (lv and rv) if op == "and" else (lv or rv)
    return values


def proof_sets(inputs, gates, values, slot_bit, root):
    """Return (need, tree) as bitmasks of OR input slots.

    need is the intersection over all proof trees; tree is one explicit tree.
    """
    need = {name: 0 for name in inputs}
    tree = {name: 0 for name in inputs}
    for name, op, left, right in gates:
        lv = False if left is False else values[left]
        rv = False if right is False else values[right]
        if op == "and":
            if lv and rv:
                need[name] = need[left] | need[right]
                tree[name] = tree[left] | tree[right]
            else:
                need[name] = tree[name] = 0
            continue

        true_children = []
        if lv:
            true_children.append((0, left))
        if rv:
            true_children.append((1, right))
        if not true_children:
            need[name] = tree[name] = 0
            continue

        common = None
        for index, child in true_children:
            part = need[child] | slot_bit[(name, index)]
            common = part if common is None else (common & part)
        need[name] = common
        index, child = true_children[0]
        tree[name] = tree[child] | slot_bit[(name, index)]
    return need[root], tree[root]


def edge_records(inputs, gates, edges, root, slot_bit):
    """One DP record per edge assignment."""
    records = []
    for edge in sorted(edges, key=lambda e: tuple(sorted(e))):
        true_names = set(edge)
        values = eval_point(inputs, gates, true_names)
        if not values.get(root, False):
            records.append((edge, 0, 0, False))
            continue
        need, tree = proof_sets(inputs, gates, values, slot_bit, root)
        records.append((edge, need, tree, True))
    return records


def zero_unselected(gates, output, keep, slot_bit):
    """Set every OR input slot not in keep to False, then simplify/prune."""
    edits = {}
    for name, op, left, right in gates:
        if op != "or":
            continue
        lkeep = bool(keep & slot_bit[(name, 0)])
        rkeep = bool(keep & slot_bit[(name, 1)])
        if lkeep and rkeep:
            continue
        if not lkeep and not rkeep:
            edits[name] = False
        elif not lkeep:
            edits[name] = (op, False, right)
        else:
            edits[name] = (op, left, False)
    return rewrite(gates, output, edits)


def repair_missed(gates, output, missed, old_len):
    """Add one AND per missed edge and OR it into the output."""
    if not missed:
        return gates, output, 0
    gates = list(gates)
    out = None if output is False else output
    for i, edge in enumerate(sorted(missed, key=lambda e: tuple(sorted(e)))):
        a, b = sorted(edge)
        ename = f"slotproof.repair.edge{i}"
        gates.append((ename, "and", a, b))
        if out is None:
            out = ename
        else:
            oname = f"slotproof.repair.out{i}"
            gates.append((oname, "or", out, ename))
            out = oname
    return gates, out, len(gates) - old_len


def possible_true(gates, inputs):
    """Structural constant-false check for a monotone AND/OR circuit."""
    can = {name: True for name in inputs}
    for name, op, left, right in gates:
        lv = can[left] if left is not False else False
        rv = can[right] if right is not False else False
        can[name] = (lv and rv) if op == "and" else (lv or rv)
    return can


def value_mask(values, name):
    return 0 if name is False else values[name]


def missed_edges(assignments, values, output):
    mask = value_mask(values, output)
    return [edge for i, edge in enumerate(assignments) if not (mask >> i) & 1]


def slots_in(mask, bit_slot):
    return [bit_slot[bit] for bit in bit_slot if mask & bit]


def run_case(label, inputs, gates, edges, root):
    """Run the DP, batch zero, repair if needed, and print the four counts."""
    slot_bit, bit_slot = slot_bits(gates)
    records = edge_records(inputs, gates, edges, root, slot_bit)
    bad_original = [edge for edge, _, _, ok in records if not ok]
    if bad_original:
        raise AssertionError(f"{label}: original circuit misses {bad_original[:3]}")

    need_by_edge = {edge: need for edge, need, _, _ in records}
    tree_by_edge = {edge: tree for edge, _, tree, _ in records}
    keep = 0
    for tree in tree_by_edge.values():
        keep |= tree

    selected_zeroed, zeroed_out = zero_unselected(gates, root, keep, slot_bit)
    assignments = [edge for edge, _, _, _ in records]
    signals = indicators(inputs, assignments)
    edge_mask = (1 << len(assignments)) - 1
    original_values = evaluate(gates, signals)
    zeroed_values = evaluate(selected_zeroed, signals)

    missed = missed_edges(assignments, zeroed_values, zeroed_out)
    down_on_edges = all(
        (zeroed_values[name] & ~original_values[name]) == 0
        for name, _, _, _ in selected_zeroed
        if name in original_values
    )
    if not down_on_edges:
        raise AssertionError(f"{label}: zeroing is not pointwise down on edge samples")

    pruned = len(gates) - len(selected_zeroed)
    can = possible_true(selected_zeroed, inputs)
    const_false = [name for name, _, _, _ in selected_zeroed if not can[name]]
    edge_dead = [name for name, _, _, _ in selected_zeroed
                 if not (zeroed_values[name] & edge_mask)]

    final_gates, final_out, new_gates = repair_missed(
        selected_zeroed, zeroed_out, missed, len(selected_zeroed))
    final_values = evaluate(final_gates, signals)
    missed_after = missed_edges(assignments, final_values, final_out)
    if missed_after:
        raise AssertionError(f"{label}: repair missed {missed_after[:3]}")

    # Actual net saving is a gate-count delta; do not sum per-slot deletability.
    net = len(gates) - len(final_gates)
    need_counts = [need.bit_count() for need in need_by_edge.values()]

    print(f"[{label}] inputs={len(inputs)} gates={len(gates)} edges={len(edges)} "
          f"slots={len(slot_bit)}")
    if need_counts:
        min_edge = min(need_by_edge, key=lambda e: need_by_edge[e].bit_count())
        max_edge = max(need_by_edge, key=lambda e: need_by_edge[e].bit_count())
        print(f"  forced OR slots per edge: "
              f"min={need_by_edge[min_edge].bit_count()} at {tuple(sorted(min_edge))}, "
              f"max={need_by_edge[max_edge].bit_count()} at {tuple(sorted(max_edge))}")
    print(f"  keep={keep.bit_count()}/{len(slot_bit)} slots; "
          f"zeroed={len(slot_bit) - keep.bit_count()}")
    print(f"  dead: pruned={pruned} retained_const_false={len(const_false)} "
          f"true_dead={pruned + len(const_false)} edge_dead={len(edge_dead)}")
    print(f"  new_gates={new_gates} net_saving={net} "
          f"(actual gate delta, original {len(gates)} -> final {len(final_gates)})")
    print(f"  missed_edges: before_repair={len(missed)} after_repair={len(missed_after)}")
    if missed:
        print(f"  missed sample: {[tuple(sorted(e)) for e in missed[:5]]}")
    print("  safety: only OR inputs outside keep are set False; monotone AND/OR "
          "makes the edit pointwise down, and every edge keeps its chosen tree.")
    return {
        "need": need_by_edge,
        "tree": tree_by_edge,
        "slot_bit": slot_bit,
        "bit_slot": bit_slot,
        "keep": keep,
    }


def star_series(k=3):
    """Minimal star c--l_i, output = c AND (l1 OR (l2 OR (... OR lk)))."""
    leaves = [f"l{i}" for i in range(1, k + 1)]
    inputs = ["c", *leaves]
    gates = []
    prev = leaves[0]
    for i in range(1, k):
        name = f"t{i + 1}"
        gates.append((name, "or", prev, leaves[i]))
        prev = name
    gates.append(("out", "and", "c", prev))
    edges = {frozenset(("c", leaf)) for leaf in leaves}
    return inputs, gates, edges, "out"


def main():
    # Rerun 1: one edge of the star forces several OR slots.
    star = star_series(3)
    star_res = run_case("star_series_k3", *star)
    edge_first = frozenset(("c", "l1"))
    edge_last = frozenset(("c", "l3"))
    first_slots = slots_in(star_res["need"][edge_first], star_res["bit_slot"])
    last_slots = slots_in(star_res["need"][edge_last], star_res["bit_slot"])
    assert len(first_slots) == 2
    assert len(last_slots) == 1
    assert star_res["tree"][edge_first] == star_res["need"][edge_first]
    print(f"  checked single edge {tuple(sorted(edge_first))} forces "
          f"{len(first_slots)} slots: {first_slots}")
    print(f"  opposite edge {tuple(sorted(edge_last))} forces "
          f"{len(last_slots)} slots: {last_slots}")

    # Rerun 2: allowed reusable fallback for the affine critical-gate example.
    inputs, gates, edges, _, _, _, _, root = build(5)
    run_case("shared_birth_p5", inputs, gates, edges, root)


if __name__ == "__main__":
    main()
