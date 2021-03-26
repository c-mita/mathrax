import collections
import itertools

Puzzle = collections.namedtuple("Puzzle", ["size", "rules", "givens"])
Rule = collections.namedtuple("Rule", ["op", "value"])

EXAMPLE = Puzzle(
    size = 6,
    rules = {
        (0,0) : Rule("/", 2),
        (1,4) : Rule("-", 1),
        (2,3) : Rule("/", 2),
        (3,1) : Rule("+", 8),
        (3,4) : Rule("-", 2),
    },
    givens = {
        (0,3) : 2,
        (3,0) : 4,
        (3,5) : 2,
        (4,0) : 6,
    },
)

EXAMPLE_2 = Puzzle(
    size = 7,
    rules = {
        (0,3) : Rule("-", 3),
        (1,1) : Rule("o", 0),
        (1,3) : Rule("-", 2),
        (2,4) : Rule("+", 5),
        (3,0) : Rule("-", 2),
        (3,2) : Rule("-", 1),
        (4,1) : Rule("-", 1),
        (4,5) : Rule("*", 6),
        (5,0) : Rule("*", 4),
    },
    givens = {},
)

EXAMPLE_3 = Puzzle(
    size = 7,
    rules = {
        (0,2): Rule("o", 0),
        (0,5): Rule("+", 10),
        (1,2): Rule("-", 1),
        (1,4): Rule("/", 1),
        (2,1): Rule("+", 7),
        (3,0): Rule("o", 0),
        (3,1): Rule("-", 1),
        (4,2): Rule("-", 1),
        (4,3): Rule("+", 10),
        (4,5): Rule("-", 2),
        (5,0): Rule("+", 12),
    },
    givens = {},
)


def create_peersets(puzzle):
    """
    Create two maps:
        peers: c -> {cells "visibile" from c}
        units: c -> (units containing c)
    """
    indices = [x for x in range(puzzle.size)]
    cells = list(itertools.product(indices, indices))
    # all units - i.e. rows and columns
    units = [list(itertools.product(indices, [i])) for i in indices]
    units += [list(itertools.product([i], indices)) for i in indices]
    units_map = {c:[u for u in units if c in u] for c in cells}
    units_map = {c:tuple(v) for c,v in units_map.items()}
    peers = {c: set(sum(units_map[c], [])) - {c} for c in cells}
    return peers, units_map


def create_rulesets(puzzle):
    """Create map: c -> (opposite cell affected by rule, rule)"""
    # rule index n is between real index n and n+1
    pair_constraints = collections.defaultdict(list)
    for (x, y), rule in puzzle.rules.items():
        pair_constraints[(x, y)].append((rule, (x+1, y+1)))
        pair_constraints[(x+1, y)].append((rule, (x, y+1)))
        pair_constraints[(x, y+1)].append((rule, (x+1, y)))
        pair_constraints[(x+1, y+1)].append((rule, (x, y)))
    return pair_constraints



def rule_complement(rule, values, maximum):
    """Get complemetary values for a value set for the given rule"""
    vset = set()
    for v in values:
        vset = vset.union(rule_inverse(rule, v, maximum))
    return vset


def rule_inverse(rule, value, maximum):
    """Get inverse values for a given value that satisfy a rule constraint"""
    op, target = rule
    if op == "+":
        values = {target - value}
    elif op == "-":
        values = {target + value, value - target}
    elif op == "*":
        values = {target / value}
    elif op == "/":
        values = {target * value, value / target}
    else:
        raise ValueError("Unhandled rule operation '%s'" % op)
    return {v for v in values if 0 < v <= maximum}



def stringify_grid(grid):
    my, mx = max(grid, key=lambda k:k[0])[0], max(grid, key=lambda k:k[1])[1]
    my, mx = my+1, mx+1
    strings = []
    for y in range(my):
        buff = ["."] * mx
        strings.append(buff)
    for y, x in grid:
        strings[y][x] = str(grid[(y, x)])
    return "\n".join("".join(s) for s in strings)


class Contradiction(Exception): pass


class Solver:
    def __init__(self, puzzle):
        self.puzzle = puzzle
        self.peers, self.units = create_peersets(self.puzzle)
        self.rule_constraints = create_rulesets(self.puzzle)

        indices = [x for x in range(puzzle.size)]
        self.cells = list(itertools.product(indices, indices))


    def solve(self):
        possibles = {c : tuple([n+1 for n in range(self.puzzle.size)]) for c in self.cells}
        for idx, rules in self.rule_constraints.items():
            for rule, partner in rules:
                if rule.op == "e":
                    possibles[idx] = tuple(v for v in possibles[idx] if v % 2 == 0)
                elif rule.op == "o":
                    possibles[idx] = tuple(v for v in possibles[idx] if v % 2 == 1)
                else:
                    allowed = rule_complement(rule, possibles[partner], self.puzzle.size)
                    original = set(possibles[idx])
                    possibles[idx] = tuple(original & allowed)

        for idx, v in self.puzzle.givens.items():
            self.assign_value(possibles, idx, v)

        things = sorted(possibles.items())
        try:
            return self.search(possibles)
        except Contradiction:
            raise ValueError("Failed to find a solution. :(")


    def search(self, possibles):
        # Success check
        if all(len(p) == 1 for p in possibles.values()):
            return {k:v[0] for k,v in possibles.items()}

        remaining = (p for p in possibles if len(possibles[p]) > 1)
        remaining = list(remaining)
        min_idx = min(remaining, key=lambda k: len(possibles[k]))
        for value in possibles[min_idx]:
            next_possibles = dict(possibles)
            try:
                self.assign_value(next_possibles, min_idx, value)
                return self.search(next_possibles)
            except Contradiction:
                pass
        raise Contradiction()


    def assign_value(self, possibles, index, value):
        """
        Try assigning a value to index, and propagate row/column constraints.
        Removes all other values from possibles[index], excepting "value".
        Raises Contradiction if not possible.
        """
        removed = tuple(v for v in possibles[index] if v != value)
        for r in removed:
            self.eliminate_value(possibles, index, r)
        return possibles


    def eliminate_value(self, possibles, index, value):
        """
        Removes a value from possibles[index] and propagates where possible.
        Returns updated possible values, or raises Contradiction.
        """
        if value not in possibles[index]:
            # Already eliminated
            return possibles

        possibles[index] = tuple(v for v in possibles[index] if v != value)
        if len(possibles[index]) == 0:
            raise Contradiction()
        elif len(possibles[index]) == 1:
            # only a single option in index; try removing the value from the peerset
            v2 = possibles[index][0]
            for c in self.peers[index]:
                self.eliminate_value(possibles, c, v2)

        # check to see if there's only one location for the value in a row/column
        for unit in self.units[index]:
            places = [c for c in unit if value in possibles[c]]
            if not places:
                raise Contradiction()
            if len(places) == 1:
                self.assign_value(possibles, places[0], value)

        # handle potential rule constraints:
        if index in self.rule_constraints:
            for rule, idx2 in self.rule_constraints[index]:
                if rule.op == "e" or rule.op == "o":
                    continue
                allowed = rule_complement(rule, possibles[index], self.puzzle.size)
                original = set(possibles[idx2])
                allowed &= original
                if not allowed:
                    raise Contradiction()
                for v2 in original - allowed:
                    self.eliminate_value(possibles, idx2, v2)
        return possibles



solver = Solver(EXAMPLE_2)
solution = solver.solve()
print stringify_grid(solution)
