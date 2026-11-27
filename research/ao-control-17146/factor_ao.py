"""Synthesize an AND/OR circuit from a rectangular Boolean table by sharing OR gates."""

import argparse
import itertools
import json
import random
from collections import Counter
from pathlib import Path

from reduce_ao import evaluate, input_tables


class Builder:
    def __init__(self, n):
        self.n = n
        self.gates = []
        self.cache = {}

    def gate(self, op, a, b):
        if a == b:
            return a
        key = (op, min(a, b), max(a, b))
        if key not in self.cache:
            self.cache[key] = self.n + len(self.gates)
            self.gates.append(key)
        return self.cache[key]

    def union(self, wires):
        wires = sorted(wires)
        while len(wires) > 1:
            nxt = [self.gate('or', a, b) for a, b in zip(wires[::2], wires[1::2])]
            if len(wires) % 2:
                nxt.append(wires[-1])
            wires = nxt
        return wires[0]


def shared_unions(builder, groups, rng, hints):
    groups = [set(g) for g in groups]
    supports = [1 << i for i in range(builder.n)]
    counts = Counter(pair for g in groups for pair in itertools.combinations(sorted(g), 2))
    while counts:
        best = max(counts.values())
        if best < 2:
            break
        if hints:
            # Reward a proven shared subset, but let one extra use outweigh the tie noise.
            candidates = [pair for pair, count in counts.items() if count >= max(2, best - 3)]
            def rank(pair):
                a, b = pair
                return counts[pair] + hints.get(supports[a] | supports[b], 0) + rng.random()
            a, b = max(candidates, key=rank)
        else:
            cutoff = best - (best > 3 and rng.random() < 0.1)
            a, b = rng.choice([pair for pair, count in counts.items() if count >= cutoff])
        combined = builder.gate('or', a, b)
        if combined == len(supports):
            supports.append(supports[a] | supports[b])
        del counts[a, b]
        for g in groups:
            if a not in g or b not in g:
                continue
            g.difference_update((a, b))
            for c in g:
                for old in (a, b):
                    pair = min(c, old), max(c, old)
                    counts[pair] -= 1
                    if not counts[pair]:
                        del counts[pair]
                counts[min(c, combined), max(c, combined)] += 1
            g.add(combined)
    return [builder.union(g) for g in groups]


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def rectangles(rows, rng, split_count):
    rects = [(1 << i, row) for i, row in enumerate(rows) if row]
    for _ in range(split_count):
        choices = []
        for i, (a, b) in enumerate(rects):
            for j in range(i):
                c, d = rects[j]
                shared = (b & d).bit_count()
                if shared >= 2 and not a & c:
                    choices.append((shared - 0.45 * (a | c).bit_count() + rng.random() * 2, i, j))
        if not choices:
            break
        _, i, j = max(choices)
        a, b = rects.pop(i)
        c, d = rects.pop(j)
        common = b & d
        rects.append((a | c, common))
        if b ^ common:
            rects.append((a, b ^ common))
        if d ^ common:
            rects.append((c, d ^ common))
    return rects


def cross_groups(rects, nrows, rng):
    # On a one-hot pair, disjoint rectangles can share their single AND gate.
    candidates = [(i, j) for i, (a, b) in enumerate(rects) for j, (c, d) in enumerate(rects[:i])
                  if a & c == 0 and b & d == 0]
    rng.shuffle(candidates)
    paired = {}
    for i, j in candidates:
        if i not in paired and j not in paired:
            paired[i], paired[j] = j, i
    groups = []
    for i, (a, b) in enumerate(rects):
        if paired.get(i, i) < i:
            continue
        c, d = rects[paired[i]] if i in paired else (0, 0)
        groups.extend((list(bits(a)) + [nrows + v for v in bits(d)],
                       list(bits(c)) + [nrows + v for v in bits(b)]))
    return groups


def circuit(groups, nrows, ncols, rng, hints=None):
    builder = Builder(nrows + ncols)
    if not groups:
        if max(nrows, ncols) == 1:
            raise ValueError('The empty 1-by-1 graph needs a constant wire')
        first = 0 if nrows > 1 else nrows
        return builder.gates, builder.gate('and', first, first + 1)
    terms = shared_unions(builder, groups, rng, hints)
    output = builder.union([builder.gate('and', a, b) for a, b in zip(terms[::2], terms[1::2])])
    return builder.gates, output


def shared_subsets(gates, inputs):
    supports = [1 << i for i in range(inputs)]
    for op, a, b in gates:
        if op != 'or':
            break
        supports.append(supports[a] | supports[b])
    return supports[inputs:]


def seed_groups(gates, output, inputs):
    supports = [{i} for i in range(inputs)]
    for op, a, b in gates:
        pure_union = op == 'or' and supports[a] is not None and supports[b] is not None
        supports.append(supports[a] | supports[b] if pure_union else None)
    pending, groups, seen = [output], [], set()
    while pending:
        wire = pending.pop()
        if wire in seen:
            continue
        seen.add(wire)
        if wire < inputs:
            return None
        op, a, b = gates[wire - inputs]
        if op == 'or':
            pending.extend((a, b))
        elif supports[a] is not None and supports[b] is not None:
            groups.extend((sorted(supports[a]), sorted(supports[b])))
        else:
            return None
    return groups


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--seed', type=int, default=0)
    parser.add_argument('--rounds', type=int, default=100)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('--rounds must be positive')
    doc = json.loads(args.input.read_text())
    rows = [int(v, 0) if isinstance(v, str) else v for v in doc['rows']]
    cols = doc['columns']
    if not rows or cols < 1 or any(not 0 <= r < 1 << cols for r in rows):
        raise ValueError('Invalid graph dimensions or row masks')
    transpose = [sum(((r >> c) & 1) << i for i, r in enumerate(rows)) for c in range(cols)]
    inputs = input_tables(len(rows), cols)
    target = sum(r << (i * cols) for i, r in enumerate(rows))
    rng = random.Random(args.seed)
    best, best_groups, best_subsets = None, None, []
    if 'gates' in doc:
        if not 0 <= doc['output'] < len(inputs) + len(doc['gates']):
            raise ValueError('Invalid output wire in starting circuit')
        if evaluate(inputs, doc['gates'])[doc['output']] != target:
            raise ValueError('Starting circuit fails the complete table')
        best = len(doc['gates'])
        best_groups = seed_groups(doc['gates'], doc['output'], len(inputs))
        best_subsets = shared_subsets(doc['gates'], len(inputs))
        args.output.write_text(json.dumps(doc, separators=(',', ':')) + '\n')
    for trial in range(args.rounds):
        transposed = trial % 2
        table = transpose if transposed else rows
        splits = 0 if trial % 6 < 2 else rng.randrange(1, max(2, len(table) // 2))
        hints = None
        if best_groups is not None and trial % 3 == 2:
            groups = best_groups
            if trial % 6 == 5:
                hints = {s: rng.uniform(0.3, 3.1) for s in best_subsets if rng.random() < 0.75}
        else:
            rects = rectangles(table, rng, splits)
            if transposed:
                rects = [(b, a) for a, b in rects]
            groups = cross_groups(rects, len(rows), rng)
        gates, out = circuit(groups, len(rows), cols, rng, hints)
        if evaluate(inputs, gates)[out] != target:
            raise RuntimeError('Synthesized circuit fails the full table')
        if best is None or len(gates) < best:
            best = len(gates)
            best_groups = groups
            best_subsets = shared_subsets(gates, len(rows) + cols)
            doc.update(gates=gates, output=out)
            args.output.write_text(json.dumps(doc, separators=(',', ':')) + '\n')
            print(f'trial {trial + 1}: {best} gates', flush=True)


if __name__ == '__main__':
    main()
