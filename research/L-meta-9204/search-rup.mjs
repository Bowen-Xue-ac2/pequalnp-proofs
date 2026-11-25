import { argv } from "node:process";

const pigeonCount = 4;
const holeCount = 3;
const variableCount = pigeonCount * holeCount;
const allVariables = (1 << variableCount) - 1;
const bit = (pigeon, hole) => 1 << (pigeon * holeCount + hole);

// Each clause is a pair of 12-bit masks for its positive and negative literals.
const clauseKey = ([positive, negative]) => positive | (negative << variableCount);
const formula = [];
for (let pigeon = 0; pigeon < pigeonCount; pigeon++) {
  let positive = 0;
  for (let hole = 0; hole < holeCount; hole++) positive |= bit(pigeon, hole);
  formula.push([positive, 0]);
}
for (let hole = 0; hole < holeCount; hole++) {
  for (let a = 0; a < pigeonCount; a++) {
    for (let b = a + 1; b < pigeonCount; b++) formula.push([0, bit(a, hole) | bit(b, hole)]);
  }
}

function unitConflict(clauses, trueMask = 0, falseMask = 0) {
  let changed;
  do {
    changed = false;
    for (const [positive, negative] of clauses) {
      if ((positive & trueMask) || (negative & falseMask)) continue;
      const undecided = (positive | negative) & ~(trueMask | falseMask);
      if (undecided === 0) return true;
      if (undecided & (undecided - 1)) continue;
      if (positive & undecided) trueMask |= undecided;
      else falseMask |= undecided;
      changed = true;
    }
  } while (changed);
  return false;
}

function minimalRupClauses(clauses) {
  const result = [];
  const existing = new Set(clauses.map(clauseKey));

  function visit(next, trueMask, falseMask) {
    if (unitConflict(clauses, trueMask, falseMask)) {
      const clause = [falseMask, trueMask];
      if (existing.has(clauseKey(clause))) return;
      let assumed = trueMask | falseMask;
      while (assumed) {
        const literal = assumed & -assumed;
        if (unitConflict(clauses, trueMask & ~literal, falseMask & ~literal)) return;
        assumed ^= literal;
      }
      result.push(clause);
      return;
    }
    for (let variable = next; variable < variableCount; variable++) {
      const literal = 1 << variable;
      visit(variable + 1, trueMask | literal, falseMask);
      visit(variable + 1, trueMask, falseMask | literal);
    }
  }

  visit(0, 0, 0);
  return result;
}

function permutations(values) {
  if (values.length <= 1) return [values];
  return values.flatMap((value, index) =>
    permutations(values.filter((_, i) => i !== index)).map(rest => [value, ...rest]));
}

const renamings = permutations([0, 1, 2, 3]).flatMap(pigeons =>
  permutations([0, 1, 2]).map(holes =>
    Array.from({ length: variableCount }, (_, v) =>
      bit(pigeons[Math.floor(v / holeCount)], holes[v % holeCount]))));

function renameMask(mask, renaming) {
  let renamed = 0;
  for (let variable = 0; variable < variableCount; variable++) {
    if (mask & (1 << variable)) renamed |= renaming[variable];
  }
  return renamed;
}

function firstStepRepresentatives(clauses) {
  const byOrbit = new Map();
  for (const clause of clauses) {
    let orbit = Infinity;
    for (const renaming of renamings) {
      orbit = Math.min(orbit, clauseKey(clause.map(mask => renameMask(mask, renaming))));
    }
    if (!byOrbit.has(orbit)) byOrbit.set(orbit, clause);
  }
  return [...byOrbit.values()];
}

// If one addition makes an otherwise propagation-consistent formula conflict,
// then the final addition can be taken to be a unit. Test both signs at once.
function finishWithAtMostTwo(clauses) {
  if (unitConflict(clauses)) return [[0, 0]];
  for (let literal = 1; literal <= allVariables; literal <<= 1) {
    if (unitConflict(clauses, literal, 0) && unitConflict(clauses, 0, literal)) {
      return [[literal, 0], [0, 0]];
    }
  }
  return null;
}

function assertRun(run) {
  const clauses = [...formula];
  for (const [positive, negative] of run) {
    if (!unitConflict(clauses, negative, positive)) throw new Error("Candidate failed RUP verification");
    clauses.push([positive, negative]);
  }
  if (!run.some(([p, n]) => p === 0 && n === 0)) throw new Error("Candidate did not learn empty clause");
}

function renderClause([positive, negative]) {
  const literals = [];
  for (let variable = 0; variable < variableCount; variable++) {
    const mask = 1 << variable;
    if ((positive | negative) & mask) {
      const pigeon = Math.floor(variable / holeCount);
      const hole = variable % holeCount;
      literals.push((negative & mask ? "~" : "") + "x(" + pigeon + "," + hole + ")");
    }
  }
  return literals;
}

const firstClauses = minimalRupClauses(formula);
const representatives = firstStepRepresentatives(firstClauses);
const findFive = argv.includes("--find-five");
const firstSteps = argv.includes("--no-symmetry") ? firstClauses : representatives;
const stats = { variables: variableCount, initialClauses: formula.length,
  firstMinimalNonredundant: firstClauses.length, firstStepOrbits: representatives.length,
  firstStates: firstSteps.length, secondStates: 0, thirdStates: 0 };
let witness = finishWithAtMostTwo(formula);
for (const first of firstSteps) {
  if (witness) break;
  const formula1 = [...formula, first];
  const short = finishWithAtMostTwo(formula1);
  if (short) {
    witness = [first, ...short];
    break;
  }
  for (const second of minimalRupClauses(formula1)) {
    stats.secondStates++;
    const formula2 = [...formula1, second];
    const tail = finishWithAtMostTwo(formula2);
    if (tail) {
      witness = [first, second, ...tail];
      break;
    }
    if (!findFive) continue;
    for (const third of minimalRupClauses(formula2)) {
      stats.thirdStates++;
      const completion = finishWithAtMostTwo([...formula2, third]);
      if (completion) {
        witness = [first, second, third, ...completion];
        break;
      }
    }
    if (witness) break;
  }
}
if (witness) assertRun(witness);
console.log(JSON.stringify({ bound: findFive ? 5 : 4, ...stats, witness: witness?.map(renderClause) ?? null }, null, 2));
