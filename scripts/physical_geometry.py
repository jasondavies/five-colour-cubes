"""Audit geometry generated from quarter turns, separate from the search model."""
import itertools


def require(condition, message):
    if not condition:
        raise ValueError(message)


def rotations():
    group = {tuple(range(6))}
    todo = list(group)
    while todo:
        p = todo.pop()
        for g in ((0, 1, 5, 4, 2, 3), (3, 2, 0, 1, 4, 5)):
            q = tuple(p[i] for i in g)
            if q not in group:
                group.add(q)
                todo.append(q)
    require(len(group) == 24, 'Quarter turns did not generate 24 rotations')
    return sorted(group)


ROT = rotations()
SLOTS = list(itertools.product((0, 1), repeat=3))
FACES = [tuple(2 * a + s[a] for a in range(3)) for s in SLOTS]


def canonical(c):
    return min(tuple(c[i] for i in r) for r in ROT)


def corner_types(c):
    result = []
    for signs, faces in zip(SLOTS, FACES):
        k = tuple(c[f] for f in faces)
        if sum(signs) % 2:
            k = (k[0], k[2], k[1])
        result.append(min(k, k[1:] + k[:1], k[2:] + k[:2]))
    return result


def fits(cubes, targets):
    oriented = [[{tuple(c[r[f]] for f in faces) for r in ROT}
                 for faces in FACES] for c in cubes]
    return [[[i for i in range(len(cubes))
              if tuple(t[f] for f in faces) in oriented[i][s]]
             for s, faces in enumerate(FACES)] for t in targets]


def match(slots, counts):
    copies = [i for i, n in enumerate(counts) for _ in range(n)]
    adj = [[j for j, i in enumerate(copies) if i in possible] for possible in slots]
    owner = [-1] * len(copies)

    def augment(s, seen):
        for j in adj[s]:
            if j in seen:
                continue
            seen.add(j)
            if owner[j] < 0 or augment(owner[j], seen):
                owner[j] = s
                return True
        return False
    return all(augment(s, set()) for s in range(8))
