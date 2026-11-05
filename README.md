# Admissible prime constellations in Lean: wheel checker and exact D(k) for k ≤ 7

Machine-checked finite combinatorial certificates about **admissible prime k-tuples**
(Hardy–Littlewood wheel admissibility), formalized in Lean 4 with Mathlib.
**Standard axioms only** — every theorem depends on at most
`[propext, Classical.choice, Quot.sound]`; all computation goes through the Lean
kernel's `decide`. **`native_decide` is not used anywhere** (grep the sources).

## What is actually proved (vs. only checked)

**Proved in Lean (kernel-checked, axioms audited):**

1. **Full wheel admissibility** (`Adm`: for *every* prime `p`, some residue class mod `p`
   is unused) of seven classical witness tuples:

   | k | witness tuple | theorem |
   |---|---|---|
   | 2 | {0, 2} | `Adm.adm_twin` |
   | 3 | {0, 4, 6} | `Adm.adm_triplet` |
   | 4 | {0, 2, 6, 8} | `Adm.adm_quadruplet` |
   | 5 | {0, 4, 6, 10, 12} | `Adm.adm_quintuplet` |
   | 6 | {0, 4, 6, 10, 12, 16} | `Adm.adm_sextuplet` |
   | 7 | {0, 2, 6, 8, 12, 18, 20} | `Adm.adm_septuplet` |
   | 8 | {0, 2, 6, 8, 12, 18, 20, 26} | `Adm.adm_octuplet` |

2. **Exact minimum diameters D(k) for k = 2 … 7** — *both directions proved*:
   * the witness above is admissible with diameter exactly D(k)
     (`Adm.diam_twin` … `Adm.diam_septuplet`), and
   * **exhaustive minimality** (`Adm.exact_D2` … `Adm.exact_D7`): *every* admissible
     `k`-tuple of distinct naturals has diameter ≥ D(k).  This is a proof-producing
     exhaustive search: a Bool search over all normalized tuples
     `0 = a₁ < a₂ < … < a_k` (`Adm.search`, structural in one argument) is evaluated by
     the kernel (`decide`), and its completeness (`Adm.search_complete`) and soundness
     (`Adm.search_sound`) are theorems, so `noAdm k d = true` yields
     "no admissible k-tuple has diameter ≤ d" (`Adm.noAdm_elim`, `Adm.diam_min`).

   | k | D(k) proved | checked against |
   |---|---|---|
   | 2 | 2 | OEIS A020497: l(2)=3 = D+1 |
   | 3 | 6 | l(3)=7 |
   | 4 | 8 | l(4)=9 |
   | 5 | 12 | l(5)=13 |
   | 6 | 16 | l(6)=17 |
   | 7 | 20 | l(7)=21 |

**NOT proved here (stated honestly):**

* **D(8) = 26 is not a Lean theorem in this repository.**  Only the *admissibility* of
  the k = 8 witness {0, 2, 6, 8, 12, 18, 20, 26} is proved (`Adm.adm_octuplet`).
  The claim "D(8) = 26" rests on the published exhaustive searches (Engelsma 2005,
  Oliveira e Silva) and is *checked*, not machine-proved, here.  (A kernel `decide` of
  the 480 700-candidate k = 8 search is feasible in principle but was not completed.)
* For k ≥ 9 nothing is proved.
* "Admissible" concerns the combinatorial wheel condition only.  Nothing about prime
  gaps or the Hardy–Littlewood conjecture itself is claimed.

Scope note: tuples range over distinct naturals; admissibility is translation- and
order-invariant (proved: `Adm.adm_shift`, `Adm.adm_sub`), and the minimality theorem
covers all admissible k-tuples of distinct naturals, not just normalized ones.

## Layout

* `Submission/Wheel.lean` — reusable framework: `Adm`, decidable bounded checker
  `unusedB`/`admB`, the pigeonhole *wheel tail lemma* (`adm_of_admB`: a size-k tuple
  automatically has an unused residue at every prime p > k, so primes ≤ k suffice),
  translation invariance, exact diameter, normalized tuples, and the proven
  exhaustive search.
* `Submission/Constellations.lean` — the validated table above + minimality runs.
* `Submission/Axioms.lean` — `#print axioms` for all headline theorems.
* `data/axiom_audit.txt` — captured audit output.
* `data/CITATIONS.md` — exact sources.

## Build

```bash
elan install leanprover/lean4:v4.34.1   # or any elan with v4.34.1
git clone <this repo> && cd <repo>
lake build            # fetches mathlib at rev d13f23b7… (cached builds reused automatically)
lake env lean Submission/Axioms.lean   # prints the axiom audit
```

Toolchain: `leanprover/lean4:v4.34.1`; Mathlib rev `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Full build from a cold mathlib cache takes ~30–60 min; with the standard mathlib cache,
seconds.  Runtime of the kernel searches: k ≤ 6 instant; k = 7 ≈ 30 s
(`maxHeartbeats 4000000` set locally on that one declaration).

## Axiom audit (abridged)

```
'Adm.exact_D7' depends on axioms: [propext, Classical.choice, Quot.sound]
'Adm.adm_octuplet' depends on axioms: [propext, Classical.choice, Quot.sound]
'Adm.noAdm7' does not depend on any axioms
'Adm.diam_septuplet' does not depend on any axioms
```
Full list in `data/axiom_audit.txt`.

## Attribution and sources

The mathematical objects and the D(k) values originate with:

* G. H. Hardy & J. E. Littlewood, *Some problems of 'partitio numerorum'; III*,
  Acta Mathematica 44 (1922), 1–70 (admissibility / prime k-tuple conjecture).
* T. J. Engelsma, *k-tuple permissible patterns*,
  http://www.opertech.com/primes/k-tuples.html (February 2005) — exhaustive l(k)
  computations (page unreachable at access time, Nov 2026; cited as in the reference
  below).
* T. Oliveira e Silva, *Admissible prime constellations*,
  https://sweet.ua.pt/tos/apc.html (accessed November 2026) — definitions, l(k)
  computations, and the pointer to OEIS A020497.
* OEIS A020497 — minimal length l(k) = D(k) + 1 (cross-check only; our D(k) for
  k ≤ 7 are independently re-proved here).

The Lean formalization, the checker-completeness argument, and the proof-producing
exhaustive search are original work by MultiAgency (darkhipo), November 2026.
