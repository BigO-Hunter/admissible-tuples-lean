import Submission.Wheel

/-!
# Validated admissible prime constellations and exact minimal diameters D(k)

Witness tuples are the classical prime constellations; each admissibility proof is a
kernel-decided evaluation of the bounded checker `admB` against `PS = [2, 3, 5, 7]`
(complete for tuple size `k ≤ 10` by the wheel tail lemma `adm_of_admB`), lifted to the
full all-primes property `Adm`.

Minimality: `noAdm k d PS = true` is a kernel-decided run of the exhaustive search over
all normalized tuples `0 = a₁ < a₂ < ... < a_k` with `a_k ≤ d`; `diam_min` converts it
into "every admissible `k`-tuple of distinct naturals has diameter ≥ D".

The values D(k) match OEIS A020497 (which lists minimal *lengths* l(k) = D(k) + 1),
as computed by T. J. Engelsma and (independently, for overlapping ranges) by
T. Oliveira e Silva:  D(2)=2, D(3)=6, D(4)=8, D(5)=12, D(6)=16, D(7)=20, D(8)=26.
-/

namespace Adm

/-- The primes ≤ 10; complete for tuples of size k ≤ 10 by the wheel tail lemma. -/
def PS : List ℕ := [2, 3, 5, 7]

theorem ps_prime : ∀ p ∈ PS, Nat.Prime p := by
  intro p hp
  simp [PS] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact Nat.prime_two
  · exact Nat.prime_three
  · exact Nat.prime_five
  · exact Nat.prime_seven

/-- Every prime ≤ 10 is in `PS`, so the checker is complete for k ≤ 10. -/
theorem ps_cover : ∀ p, Nat.Prime p → p ≤ 10 → p ∈ PS := by
  intro p hp hle
  have h2 : 2 ≤ p := hp.two_le
  interval_cases p
  · simp [PS]
  · simp [PS]
  · exact absurd hp (by decide)
  · simp [PS]
  · exact absurd hp (by decide)
  · simp [PS]
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)

/-- Checker completeness for any tuple of length ≤ 10. -/
theorem ps_cover_of_len (t : List ℕ) (hlen : t.length ≤ 10) :
    ∀ p, Nat.Prime p → p ≤ t.length → p ∈ PS :=
  fun p hp hle => ps_cover p hp (le_trans hle hlen)

/-! ## Admissibility of the classical constellations (all primes, full `Adm`) -/

/-- Twin-prime pattern {0, 2}: admissible. -/
theorem adm_twin : Adm [0, 2] := adm_of_admB (ps_cover_of_len _ (by decide)) (by decide)

/-- Prime-triplet pattern {0, 4, 6}: admissible. -/
theorem adm_triplet : Adm [0, 4, 6] := adm_of_admB (ps_cover_of_len _ (by decide)) (by decide)

/-- Prime-quadruplet pattern {0, 2, 6, 8}: admissible. -/
theorem adm_quadruplet : Adm [0, 2, 6, 8] := adm_of_admB (ps_cover_of_len _ (by decide)) (by decide)

/-- Prime-quintuplet pattern {0, 4, 6, 10, 12}: admissible. -/
theorem adm_quintuplet : Adm [0, 4, 6, 10, 12] := adm_of_admB (ps_cover_of_len _ (by decide)) (by decide)

/-- Prime-sextuplet pattern {0, 4, 6, 10, 12, 16}: admissible. -/
theorem adm_sextuplet : Adm [0, 4, 6, 10, 12, 16] := adm_of_admB (ps_cover_of_len _ (by decide)) (by decide)

/-- Prime-septuplet pattern {0, 2, 6, 8, 12, 18, 20}: admissible. -/
theorem adm_septuplet : Adm [0, 2, 6, 8, 12, 18, 20] := adm_of_admB (ps_cover_of_len _ (by decide)) (by decide)

/-- Prime-octuplet pattern {0, 2, 6, 8, 12, 18, 20, 26}: admissible. -/
theorem adm_octuplet : Adm [0, 2, 6, 8, 12, 18, 20, 26] := adm_of_admB (ps_cover_of_len _ (by decide)) (by decide)

/-! ## Exhaustive minimality: the search certifies no smaller admissible tuple exists -/

/-- No admissible pair has diameter ≤ 1 (i.e. D(2) ≥ 2). -/
theorem noAdm2 : noAdm 2 1 PS = true := by decide

/-- No admissible triple has diameter ≤ 5 (i.e. D(3) ≥ 6). -/
theorem noAdm3 : noAdm 3 5 PS = true := by decide

/-- No admissible quadruple has diameter ≤ 7 (i.e. D(4) ≥ 8). -/
theorem noAdm4 : noAdm 4 7 PS = true := by decide

/-- No admissible quintuple has diameter ≤ 11 (i.e. D(5) ≥ 12). -/
theorem noAdm5 : noAdm 5 11 PS = true := by decide

/-- No admissible sextuple has diameter ≤ 15 (i.e. D(6) ≥ 16). -/
theorem noAdm6 : noAdm 6 15 PS = true := by decide

set_option maxHeartbeats 4000000 in
/-- No admissible septuple has diameter ≤ 19 (i.e. D(7) ≥ 20). -/
theorem noAdm7 : noAdm 7 19 PS = true := by decide

/-! ## Exact minimal diameters -/

/-- D(2) = 2: {0,2} is admissible and every admissible pair has diameter ≥ 2. -/
theorem exact_D2 : ∀ t, Adm t → Distinct t → t.length = 2 → 2 ≤ diam t :=
  diam_min (k := 2) (D := 2) (by decide) ps_prime noAdm2

/-- D(3) = 6: {0,4,6} is admissible and every admissible triple has diameter ≥ 6. -/
theorem exact_D3 : ∀ t, Adm t → Distinct t → t.length = 3 → 6 ≤ diam t :=
  diam_min (k := 3) (D := 6) (by decide) ps_prime noAdm3

/-- D(4) = 8: {0,2,6,8} is admissible and every admissible quadruple has diameter ≥ 8. -/
theorem exact_D4 : ∀ t, Adm t → Distinct t → t.length = 4 → 8 ≤ diam t :=
  diam_min (k := 4) (D := 8) (by decide) ps_prime noAdm4

/-- D(5) = 12: {0,4,6,10,12} is admissible and every admissible quintuple has
diameter ≥ 12. -/
theorem exact_D5 : ∀ t, Adm t → Distinct t → t.length = 5 → 12 ≤ diam t :=
  diam_min (k := 5) (D := 12) (by decide) ps_prime noAdm5

/-- D(6) = 16: {0,4,6,10,12,16} is admissible and every admissible sextuple has
diameter ≥ 16. -/
theorem exact_D6 : ∀ t, Adm t → Distinct t → t.length = 6 → 16 ≤ diam t :=
  diam_min (k := 6) (D := 16) (by decide) ps_prime noAdm6

/-- D(7) = 20: {0,2,6,8,12,18,20} is admissible and every admissible septuple has
diameter ≥ 20. -/
theorem exact_D7 : ∀ t, Adm t → Distinct t → t.length = 7 → 20 ≤ diam t :=
  diam_min (k := 7) (D := 20) (by decide) ps_prime noAdm7

/-! ## Witness diameters (the tuples achieve exactly D(k)) -/

theorem diam_twin : diam [0, 2] = 2 := by decide
theorem diam_triplet : diam [0, 4, 6] = 6 := by decide
theorem diam_quadruplet : diam [0, 2, 6, 8] = 8 := by decide
theorem diam_quintuplet : diam [0, 4, 6, 10, 12] = 12 := by decide
theorem diam_sextuplet : diam [0, 4, 6, 10, 12, 16] = 16 := by decide
theorem diam_septuplet : diam [0, 2, 6, 8, 12, 18, 20] = 20 := by decide
theorem diam_octuplet : diam [0, 2, 6, 8, 12, 18, 20, 26] = 26 := by decide

end Adm
