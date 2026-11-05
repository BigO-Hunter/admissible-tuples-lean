# Sources and citations

## Definitions

* G. H. Hardy and J. E. Littlewood, "Some problems of 'partitio numerorum'; III:
  on the expression of a number as a sum of primes", Acta Mathematica, vol. 44,
  pp. 1-70, 1922.  Admissibility of a k-tuple: for each prime p at least one
  residue class mod p is unused by the tuple.

## Computed values l(k) (minimal length = minimal diameter + 1)

* T. Oliveira e Silva, "Admissible prime constellations",
  https://sweet.ua.pt/tos/apc.html — accessed November 2026.  Defines l(k),
  discusses computation (exponential search, exact for smaller k), cites
  OEIS A020497 and Engelsma's page as [6].
* T. J. Engelsma, "k-tuple permissible patterns",
  http://www.opertech.com/primes/k-tuples.html , February 2005.  Exhaustive
  computations of l(k).  NOTE: this page did not respond when accessed
  (November 2026); it is cited here as given by the Oliveira e Silva page.
  An archive.org snapshot may substitute for future verifiers.
* OEIS A020497, "Minimal length of an admissible sequence of n primes"
  (https://oeis.org/A020497) — b-file fetched 2026-11-04; values used only as a
  cross-check: l(2..10) = 3, 7, 9, 13, 17, 21, 27, 31, 33 (l(k) = D(k) + 1).
  Our Lean theorems independently re-prove D(k) = l(k) - 1 for k <= 7.

## Relationship of this repository to the sources

The witness tuples are the classical prime constellations (twin primes, prime
triplet/quadruplet/quintuplet/sextuplet/septuplet/octuplet patterns as tabulated
by the sources above).  The D(k) minimality values for k <= 7 are NOT taken on
trust: they are re-proved here by an exhaustive search whose soundness and
completeness are themselves Lean theorems.  The OEIS/l(k) tables serve only as an
independent cross-check of the searched diameter bounds.
