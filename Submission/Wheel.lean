import Mathlib.Tactic

/-!
# Wheel admissibility for prime constellations — framework

A finite tuple of distinct integers `a₁ < a₂ < ... < a_k` is *admissible* (Hardy–Littlewood
1922) when for every prime `p` at least one residue class mod `p` contains none of the `aᵢ`.
This file provides the reusable framework:

* `Adm` — the property, quantified over all primes;
* `unusedB` / `admB` — a decidable bounded checker against a prime list;
* the pigeonhole "wheel tail" lemma (`adm_of_admB`): a tuple of size `k` automatically
  leaves a residue unused at every prime `p > k`, so primes `≤ k` suffice;
* translation invariance;
* exact diameter `diam` with membership characterizations;
* `Inc` / `Distinct` / `sortInc` — normalized tuples;
* `search` — a Bool exhaustive search over normalized tuples `0 = a₁ < ... < a_k`,
  structural in its first argument (kernel-decidable; no `native_decide`), proven sound
  (`search_sound`) and complete (`search_complete`);
* `noAdm_elim` / `diam_min`: if the search returns `false`, no admissible `k`-tuple of
  distinct naturals has diameter `≤ d`.

References:
* T. Oliveira e Silva, "Admissible prime constellations", https://sweet.ua.pt/tos/apc.html
  (accessed November 2026).
* T. J. Engelsma, "k-tuple permissible patterns",
  http://www.opertech.com/primes/k-tuples.html (February 2005), as cited ibid.
* OEIS A020497: minimal *length* `l(k)`; minimal diameter is `l(k) - 1`.
-/

namespace Adm

/-! ## Definitions and the bounded checker -/

/-- Residue class `r < p` is unused by tuple `t`. -/
def Unused (t : List ℕ) (p : ℕ) : Prop := ∃ r, r < p ∧ ∀ a ∈ t, a % p ≠ r

/-- Full wheel admissibility: every prime leaves some residue class unused. -/
def Adm (t : List ℕ) : Prop := ∀ p, Nat.Prime p → Unused t p

/-- Decidable single-prime check. -/
def unusedB (t : List ℕ) (p : ℕ) : Bool :=
  (List.range p).any fun r => t.all fun a => a % p != r

/-- Decidable bounded checker against a list of primes `ps`. -/
def admB (t : List ℕ) (ps : List ℕ) : Bool := ps.all fun p => unusedB t p

theorem unusedB_sound {t : List ℕ} {p : ℕ} (h : unusedB t p = true) : Unused t p := by
  unfold unusedB at h
  obtain ⟨r, hr, hall⟩ := List.any_eq_true.1 h
  exact ⟨r, List.mem_range.1 hr, fun a ha => by
    have hb := List.all_eq_true.1 hall a ha
    simpa using hb⟩

theorem unusedB_true {t : List ℕ} {p : ℕ} (h : Unused t p) : unusedB t p = true := by
  obtain ⟨r, hr, hall⟩ := h
  unfold unusedB
  refine List.any_eq_true.2 ⟨r, List.mem_range.2 hr, ?_⟩
  refine List.all_eq_true.2 (fun a ha => ?_)
  simp [hall a ha]

theorem admB_sound {t : List ℕ} {ps : List ℕ} (h : admB t ps = true) :
    ∀ p ∈ ps, Unused t p := fun p hp =>
  unusedB_sound (List.all_eq_true.1 h p hp)

theorem admB_of_Adm {t ps : List ℕ} (hprime : ∀ p ∈ ps, Nat.Prime p) (h : Adm t) :
    admB t ps = true := by
  unfold admB
  refine List.all_eq_true.2 (fun p hp => unusedB_true ?_)
  exact h p (hprime p hp)

/-- Admissibility depends only on the set of elements. -/
theorem adm_congr {t t' : List ℕ} (hc : ∀ a, a ∈ t ↔ a ∈ t') : Adm t ↔ Adm t' := by
  constructor
  · intro h p hp
    obtain ⟨r, hr, hall⟩ := h p hp
    exact ⟨r, hr, fun a ha => hall a ((hc a).mpr ha)⟩
  · intro h p hp
    obtain ⟨r, hr, hall⟩ := h p hp
    exact ⟨r, hr, fun a ha => hall a ((hc a).mp ha)⟩

/-! ## Pigeonhole: short tuples cannot fill a wheel -/

theorem exists_unused_of_lt (t : List ℕ) (p : ℕ) (h : t.length < p) : Unused t p := by
  by_contra hcon
  have hcon : ∀ r, r < p → ∃ a ∈ t, a % p = r := by
    intro r hr
    by_contra hmem
    refine hcon ⟨r, hr, ?_⟩
    intro a ha heq
    exact hmem ⟨a, ha, heq⟩
  have hsub : List.range p ⊆ (t.map (· % p)).dedup := by
    intro r hr
    obtain ⟨a, ha, heq⟩ := hcon r (List.mem_range.1 hr)
    exact List.mem_dedup.2 (List.mem_map.2 ⟨a, ha, heq⟩)
  have hsp := List.Nodup.subperm (l₁ := List.range p) List.nodup_range hsub
  obtain ⟨l, hperm, hsubl⟩ := List.subperm_iff.1 hsp
  have h1 : (List.range p).length ≤ l.length := List.Sublist.length_le hsubl
  have h3 : (t.map (· % p)).dedup.length ≤ t.length := by
    have hd := List.Sublist.length_le (List.dedup_sublist (t.map (· % p)))
    rw [List.length_map] at hd
    exact hd
  have h2 : l.length ≤ (t.map (· % p)).dedup.length := by
    have hpeq := List.Perm.length_eq hperm
    omega
  rw [List.length_range] at h1
  omega

/-- **Wheel tail lemma.** A tuple of size `k` is automatically admissible at every prime
`p > k`; only primes `p ≤ k` need to be checked. -/
theorem adm_of_admB {t : List ℕ} {ps : List ℕ}
    (hps : ∀ p, Nat.Prime p → p ≤ t.length → p ∈ ps) (h : admB t ps = true) : Adm t := by
  intro p hp
  by_cases hmem : p ∈ ps
  · exact admB_sound h p hmem
  · apply exists_unused_of_lt
    by_contra hle
    exact hmem (hps p hp (by omega))

/-! ## Translation invariance -/

theorem unused_shift (t : List ℕ) (p c : ℕ) (hp : 0 < p) :
    Unused t p ↔ Unused (t.map (· + c)) p := by
  constructor
  · rintro ⟨r, hr, hall⟩
    refine ⟨(r + c) % p, Nat.mod_lt _ hp, ?_⟩
    rintro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    intro heq
    refine hall b hb ?_
    have h1 : (b % p + c) % p = (r % p + c) % p := by
      rw [Nat.mod_add_mod, Nat.mod_add_mod]
      exact heq
    have hM : (b % p + c) ≡ (r % p + c) [MOD p] := h1
    have h2 : b % p ≡ r % p [MOD p] :=
      Nat.ModEq.add_right_cancel' (a := b % p) (b := r % p) (n := p) (c := c) hM
    rw [Nat.mod_eq_of_lt hr] at h2
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hr] using h2
  · rintro ⟨r, hr, hall⟩
    have hyc : c % p < p := Nat.mod_lt c hp
    have hkey : (r + p - c % p + c) % p = r := by
      have hmod : c % p ≤ c := Nat.mod_le c p
      have hdm := Nat.div_add_mod c p
      have e1 : r + p - c % p + c = r + c - c % p + p := by omega
      have e2 : r + c - c % p = r + p * (c / p) := by omega
      rw [e1, e2, Nat.add_mod_right, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    refine ⟨(r + p - c % p) % p, Nat.mod_lt _ hp, ?_⟩
    rintro a ha hcon
    refine hall (a + c) (List.mem_map.2 ⟨a, ha, rfl⟩) ?_
    have h1 : (a + c) % p = (a % p + c) % p := (Nat.mod_add_mod _ _ _).symm
    rw [hcon] at h1
    rw [Nat.mod_add_mod] at h1
    rw [hkey] at h1
    exact h1

theorem map_sub_add (t : List ℕ) (c : ℕ) (hc : ∀ a ∈ t, c ≤ a) :
    (t.map (· - c)).map (· + c) = t := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    have hac : c ≤ a := hc a (List.mem_cons_self ..)
    have ih' : (t.map (· - c)).map (· + c) = t :=
      ih (fun a ha => hc a (List.mem_cons_of_mem _ ha))
    simp only [List.map_cons, List.cons_append, List.map_append]
    rw [show a - c + c = a from by omega, ih']

theorem unused_sub (t : List ℕ) (p c : ℕ) (hp : 0 < p) (hc : ∀ a ∈ t, c ≤ a) :
    Unused t p ↔ Unused (t.map (· - c)) p := by
  have hmap := map_sub_add t c hc
  constructor
  · intro h
    have h2 : Unused ((t.map (· - c)).map (· + c)) p := by rw [hmap]; exact h
    exact (unused_shift _ p c hp).2 h2
  · intro h
    have h2 := (unused_shift _ p c hp).1 h
    rwa [hmap] at h2

theorem adm_shift (t : List ℕ) (c : ℕ) : Adm t ↔ Adm (t.map (· + c)) := by
  constructor
  · intro h p hp
    exact (unused_shift t p c (lt_of_lt_of_le (show (0:ℕ) < 2 from by decide) hp.two_le)).1 (h p hp)
  · intro h p hp
    exact (unused_shift t p c (lt_of_lt_of_le (show (0:ℕ) < 2 from by decide) hp.two_le)).2 (h p hp)

theorem adm_sub (t : List ℕ) (c : ℕ) (hc : ∀ a ∈ t, c ≤ a) : Adm t ↔ Adm (t.map (· - c)) := by
  have hp0 : ∀ p, Nat.Prime p → 0 < p := fun p hp => lt_of_lt_of_le (show (0:ℕ) < 2 from by decide) hp.two_le
  constructor
  · intro h p hp
    exact (unused_sub t p c (hp0 p hp) hc).1 (h p hp)
  · intro h p hp
    exact (unused_sub t p c (hp0 p hp) hc).2 (h p hp)

/-! ## Diameter -/

private def goMax : ℕ → List ℕ → ℕ
  | m, [] => m
  | m, x :: l => goMax (max m x) l

/-- Maximum of a list (0 for the empty list). -/
def maxOf : List ℕ → ℕ
  | [] => 0
  | b :: l => goMax b l

private def goMin : ℕ → List ℕ → ℕ
  | m, [] => m
  | m, x :: l => goMin (min m x) l

/-- Minimum of a nonempty list (seeded at the head; 0 for the empty list). -/
def minOf : List ℕ → ℕ
  | [] => 0
  | b :: l => goMin b l

/-- Diameter: max minus min. -/
def diam (t : List ℕ) : ℕ := maxOf t - minOf t

theorem goMax_ge : ∀ (l : List ℕ) (m : ℕ), m ≤ goMax m l ∧ ∀ x ∈ l, x ≤ goMax m l := by
  intro l
  induction l with
  | nil => intro m; exact ⟨le_refl _, by simp⟩
  | cons x l ih =>
    intro m
    obtain ⟨h1, h2⟩ := ih (max m x)
    simp only [goMax] at h1 h2 ⊢
    refine ⟨le_trans (le_max_left m x) h1, fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact le_trans (le_max_right m y) h1
    · exact h2 y hy

theorem goMax_le : ∀ (l : List ℕ) (m M : ℕ), m ≤ M → (∀ x ∈ l, x ≤ M) → goMax m l ≤ M := by
  intro l
  induction l with
  | nil => intro m M hm _; exact hm
  | cons x l ih =>
    intro m M hm hx
    simp only [goMax]
    exact ih (max m x) M (max_le hm (hx x (List.mem_cons_self ..)))
      (fun y hy => hx y (List.mem_cons_of_mem _ hy))

theorem goMax_mem : ∀ (l : List ℕ) (m : ℕ), goMax m l ∈ m :: l := by
  intro l
  induction l with
  | nil => intro m; exact List.mem_cons_self ..
  | cons x l ih =>
    intro m
    show goMax (max m x) l ∈ m :: x :: l
    rcases List.mem_cons.1 (ih (max m x)) with h | h
    · rw [h]
      rcases le_total x m with hle | hle
      · rw [max_eq_left hle]
        exact List.mem_cons_self ..
      · rw [max_eq_right hle]
        exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem goMin_le : ∀ (l : List ℕ) (m : ℕ), goMin m l ≤ m ∧ ∀ x ∈ l, goMin m l ≤ x := by
  intro l
  induction l with
  | nil => intro m; exact ⟨le_refl _, by simp⟩
  | cons x l ih =>
    intro m
    obtain ⟨h1, h2⟩ := ih (min m x)
    simp only [goMin] at h1 h2 ⊢
    refine ⟨le_trans h1 (min_le_left m x), fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with rfl | hy
    · exact le_trans h1 (min_le_right m y)
    · exact h2 y hy

theorem goMin_ge : ∀ (l : List ℕ) (m B : ℕ), B ≤ m → (∀ x ∈ l, B ≤ x) → B ≤ goMin m l := by
  intro l
  induction l with
  | nil => intro m B hm _; exact hm
  | cons x l ih =>
    intro m B hm hx
    simp only [goMin]
    exact ih (min m x) B (le_min hm (hx x (List.mem_cons_self ..)))
      (fun y hy => hx y (List.mem_cons_of_mem _ hy))

theorem goMin_mem : ∀ (l : List ℕ) (m : ℕ), goMin m l ∈ m :: l := by
  intro l
  induction l with
  | nil => intro m; exact List.mem_cons_self ..
  | cons x l ih =>
    intro m
    show goMin (min m x) l ∈ m :: x :: l
    rcases List.mem_cons.1 (ih (min m x)) with h | h
    · rw [h]
      rcases le_total m x with hle | hle
      · rw [min_eq_left hle]
        exact List.mem_cons_self ..
      · rw [min_eq_right hle]
        exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem le_maxOf_mem {t : List ℕ} {a : ℕ} (h : a ∈ t) : a ≤ maxOf t := by
  cases t with
  | nil => cases h
  | cons b l =>
    obtain ⟨h1, h2⟩ := goMax_ge l b
    rcases List.mem_cons.1 h with rfl | h
    · exact h1
    · exact h2 a h

theorem maxOf_le_forall {t : List ℕ} {M : ℕ} (h : ∀ a ∈ t, a ≤ M) : maxOf t ≤ M := by
  cases t with
  | nil => exact Nat.zero_le _
  | cons b l =>
    exact goMax_le l b M (h b (List.mem_cons_self ..))
      (fun a ha => h a (List.mem_cons_of_mem _ ha))

theorem maxOf_mem {t : List ℕ} (hne : t ≠ []) : maxOf t ∈ t := by
  cases t with
  | nil => exact absurd rfl hne
  | cons b l =>
    rcases List.mem_cons.1 (goMax_mem l b) with h | h
    · show goMax b l ∈ b :: l
      rw [h]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ h

theorem le_minOf_mem {t : List ℕ} {a : ℕ} (h : a ∈ t) : minOf t ≤ a := by
  cases t with
  | nil => cases h
  | cons b l =>
    obtain ⟨h1, h2⟩ := goMin_le l b
    rcases List.mem_cons.1 h with rfl | h
    · exact h1
    · exact h2 a h

theorem minOf_ge_forall {t : List ℕ} (hne : t ≠ []) {m : ℕ} (h : ∀ a ∈ t, m ≤ a) :
    m ≤ minOf t := by
  cases t with
  | nil => exact absurd rfl hne
  | cons b l =>
    exact goMin_ge l b m (h b (List.mem_cons_self ..))
      (fun a ha => h a (List.mem_cons_of_mem _ ha))

theorem minOf_mem {t : List ℕ} (hne : t ≠ []) : minOf t ∈ t := by
  cases t with
  | nil => exact absurd rfl hne
  | cons b l =>
    rcases List.mem_cons.1 (goMin_mem l b) with h | h
    · show goMin b l ∈ b :: l
      rw [h]
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ h

theorem minOf_congr {t u : List ℕ} (hc : ∀ a, a ∈ t ↔ a ∈ u) : minOf t = minOf u := by
  cases t with
  | nil =>
    cases u with
    | nil => rfl
    | cons b u' =>
      exact absurd ((hc b).mpr (List.mem_cons_self ..)) (by simp)
  | cons b t' =>
    cases u with
    | nil =>
      exact absurd ((hc b).mp (List.mem_cons_self ..)) (by simp)
    | cons c u' =>
      have h1 : minOf (b :: t') ≤ minOf (c :: u') :=
        minOf_ge_forall (t := c :: u') (by simp) (fun a ha => le_minOf_mem ((hc a).mpr ha))
      have h2 : minOf (c :: u') ≤ minOf (b :: t') :=
        minOf_ge_forall (t := b :: t') (by simp) (fun a ha => le_minOf_mem ((hc a).mp ha))
      omega

private theorem goMax_map_add : ∀ (l : List ℕ) (c x : ℕ),
    goMax (x + c) (l.map (· + c)) = goMax x l + c := by
  intro l
  induction l with
  | nil => intro c x; rfl
  | cons y l ih =>
    intro c x
    simp only [List.map_cons, goMax]
    rw [max_add_add_right, ih c (max x y)]

theorem maxOf_map_add {t : List ℕ} (hne : t ≠ []) (c : ℕ) :
    maxOf (t.map (· + c)) = maxOf t + c := by
  cases t with
  | nil => exact absurd rfl hne
  | cons b l => exact goMax_map_add l c b

private theorem goMin_map_add : ∀ (l : List ℕ) (c x : ℕ),
    goMin (x + c) (l.map (· + c)) = goMin x l + c := by
  intro l
  induction l with
  | nil => intro c x; rfl
  | cons y l ih =>
    intro c x
    simp only [List.map_cons, goMin]
    rw [min_add_add_right, ih c (min x y)]

theorem minOf_map_add {t : List ℕ} (hne : t ≠ []) (c : ℕ) :
    minOf (t.map (· + c)) = minOf t + c := by
  cases t with
  | nil => exact absurd rfl hne
  | cons b l => exact goMin_map_add l c b

theorem diam_map_add (t : List ℕ) (c : ℕ) : diam (t.map (· + c)) = diam t := by
  cases t with
  | nil => rfl
  | cons b l =>
    unfold diam
    rw [maxOf_map_add (by simp), minOf_map_add (by simp)]
    omega

theorem diam_map_sub (t : List ℕ) (c : ℕ) (hc : ∀ a ∈ t, c ≤ a) :
    diam (t.map (· - c)) = diam t := by
  have hmap := map_sub_add t c hc
  calc diam (t.map (· - c))
      = diam ((t.map (· - c)).map (· + c)) := (diam_map_add _ c).symm
    _ = diam t := by rw [hmap]

/-! ## Normalized tuples: `Distinct` and `Inc` -/

/-- All elements are pairwise distinct. -/
def Distinct (l : List ℕ) : Prop := ∀ a ∈ l, ∀ b ∈ l, a ≠ b

/-- Strictly increasing lists. -/
inductive Inc : List ℕ → Prop
  | nil : Inc []
  | cons : (a : ℕ) → (l : List ℕ) → (∀ b ∈ l, a < b) → Inc l → Inc (a :: l)

theorem inc_cons {a : ℕ} {l : List ℕ} (h : Inc (a :: l)) : (∀ b ∈ l, a < b) ∧ Inc l := by
  cases h with
  | cons a l h1 h2 => exact ⟨h1, h2⟩

theorem inc_append_lt : ∀ (pre : List ℕ) (a : ℕ) (l' : List ℕ),
    Inc (pre ++ a :: l') → ∀ b ∈ l', a < b := by
  intro pre
  induction pre with
  | nil => intro a l' h b hb; exact (inc_cons h).1 b hb
  | cons z pre ih =>
    intro a l' h b hb
    have hsplit : (z :: pre) ++ a :: l' = z :: (pre ++ a :: l') := rfl
    rw [hsplit] at h
    obtain ⟨_, hinc⟩ := inc_cons h
    exact ih a l' hinc b hb

theorem inc_append_right : ∀ (pre l : List ℕ), Inc (pre ++ l) → Inc l := by
  intro pre
  induction pre with
  | nil => intro l h; exact h
  | cons z pre ih =>
    intro l h
    have hsplit : (z :: pre) ++ l = z :: (pre ++ l) := rfl
    rw [hsplit] at h
    obtain ⟨_, hinc⟩ := inc_cons h
    exact ih l hinc

theorem inc_append_single {l : List ℕ} (h : Inc l) (c : ℕ) (hc : ∀ x ∈ l, x < c) :
    Inc (l ++ [c]) := by
  induction h with
  | nil => exact Inc.cons c [] (by simp) Inc.nil
  | cons a l h1 h2 ih =>
    have hlt : a < c := hc a (List.mem_cons_self ..)
    have hrest : Inc (l ++ [c]) := ih (fun x hx => hc x (List.mem_cons_of_mem _ hx))
    rw [List.cons_append]
    refine Inc.cons a (l ++ [c]) (fun b hb => ?_) hrest
    rcases List.mem_append.1 hb with hb | hb
    · exact h1 b hb
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact hlt
      · exact absurd hb (by simp)

theorem inc_head_min {a : ℕ} {l : List ℕ} (h : Inc (a :: l)) : minOf (a :: l) = a := by
  have h1 : minOf (a :: l) ≤ a := le_minOf_mem (List.mem_cons_self ..)
  have h2 : a ≤ minOf (a :: l) := by
    refine minOf_ge_forall (t := a :: l) (by simp) (fun x hx => ?_)
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_refl _
    · exact Nat.le_of_lt ((inc_cons h).1 x hx)
  omega

theorem distinct_map_sub {t : List ℕ} (m : ℕ) (hm : ∀ a ∈ t, m ≤ a) (hd : Distinct t) :
    Distinct (t.map (· - m)) := by
  intro a ha b hb heq
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
  have h1 : m ≤ x := hm x hx
  have h2 : m ≤ y := hm y hy
  exact hd x hx y hy (by omega)

/-! Hand-rolled insertion sort producing strictly increasing output on distinct input. -/

def ins : ℕ → List ℕ → List ℕ
  | x, [] => [x]
  | x, y :: l => if x < y then x :: y :: l else y :: ins x l

def sortInc : List ℕ → List ℕ
  | [] => []
  | x :: l => ins x (sortInc l)

theorem mem_ins {x a : ℕ} : ∀ (l : List ℕ), a ∈ ins x l ↔ a = x ∨ a ∈ l := by
  intro l
  induction l with
  | nil => simp [ins]
  | cons y l ih =>
    simp only [ins]
    by_cases h : x < y
    · rw [if_pos h]
      simp only [List.mem_cons, ih] <;> tauto
    · rw [if_neg h]
      simp only [List.mem_cons, ih] <;> tauto

theorem mem_sortInc {a : ℕ} {l : List ℕ} : a ∈ sortInc l ↔ a ∈ l := by
  induction l with
  | nil => simp [sortInc]
  | cons x l ih =>
    simp only [sortInc, mem_ins, List.mem_cons, ih] <;> tauto

theorem length_ins (x : ℕ) : ∀ (l : List ℕ), (ins x l).length = l.length + 1 := by
  intro l
  induction l with
  | nil => rfl
  | cons y l ih =>
    simp only [ins]
    by_cases h : x < y
    · rw [if_pos h]; simp only [List.length_cons] <;> omega
    · rw [if_neg h]; simp only [List.length_cons]; rw [ih] <;> omega

theorem length_sortInc : ∀ (l : List ℕ), (sortInc l).length = l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons x l ih =>
    show (ins x (sortInc l)).length = l.length + 1
    rw [length_ins, ih]

theorem ins_inc {l : List ℕ} (hi : Inc l) (x : ℕ) (hx : x ∉ l) : Inc (ins x l) := by
  induction hi with
  | nil => exact Inc.cons x [] (by simp) Inc.nil
  | cons a l h1 h2 ih =>
    have hxa : x ∉ l := fun hmem => hx (List.mem_cons_of_mem _ hmem)
    simp only [ins]
    by_cases hlt : x < a
    · rw [if_pos hlt]
      exact Inc.cons x (a :: l) (fun b hb => by
        rcases List.mem_cons.1 hb with rfl | hb
        · exact hlt
        · exact Nat.lt_of_lt_of_le hlt (Nat.le_of_lt (h1 b hb))) (Inc.cons a l h1 h2)
    · rw [if_neg hlt]
      have hne : a ≠ x := by
        intro he
        subst he
        exact hx (List.mem_cons_self ..)
      have hax : a < x := by omega
      exact Inc.cons a (ins x l) (fun b hb => by
        rcases (mem_ins l).1 hb with rfl | hb
        · exact hax
        · exact h1 b hb) (ih hxa)

theorem sortInc_inc {l : List ℕ} (hd : Distinct l) : Inc (sortInc l) := by
  induction l with
  | nil => exact Inc.nil
  | cons x l ih =>
    have hdx : Distinct l := fun a ha b hb =>
      hd a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
    have hxs : x ∉ sortInc l := by
      intro hx
      exact hd x (List.mem_cons_self ..) x (List.mem_cons_of_mem _ ((mem_sortInc (l := l)).mp hx)) rfl
    exact ins_inc (ih hdx) x hxs

/-! ## Exhaustive search over normalized tuples -/

/-- Exhaustive search: is there a `rest` with `rest.length + acc.length = k`, strictly
increasing continuation of `acc`, all values in `[c, bound]`, with `acc ++ rest` passing
the bounded checker `ps`?  The candidate count is tracked by `room` (structural argument;
both recursive calls shrink it; the caller maintains `c + room = bound + 1`). -/
def search : ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → Bool
  | 0, k, _c, _bound, acc, ps => if k ≤ acc.length then admB acc ps else false
  | room + 1, k, c, bound, acc, ps =>
      if k ≤ acc.length then admB acc ps
      else if search room k (c + 1) bound (acc ++ [c]) ps then true
      else search room k (c + 1) bound acc ps

/-- The search found nothing: no admissible normalized `k`-tuple of diameter `≤ d`. -/
def noAdm (k d : ℕ) (ps : List ℕ) : Bool := !(search d k 1 d [0] ps)

theorem search_sound : ∀ (room : ℕ) (k c bound : ℕ) (acc ps : List ℕ),
    c + room = bound + 1 →
    Inc acc → (∀ x ∈ acc, x ≤ bound) → (∀ x ∈ acc, x < c) → acc.length ≤ k →
    search room k c bound acc ps = true →
    ∃ rest, rest.length + acc.length = k ∧ (∀ x ∈ rest, c ≤ x ∧ x ≤ bound) ∧
      Inc (acc ++ rest) ∧ admB (acc ++ rest) ps = true := by
  intro room
  induction room with
  | zero =>
    intro k c bound acc ps hroom hinc hab hlt hlen h
    simp only [search] at h
    by_cases hkle : k ≤ acc.length
    · rw [if_pos hkle] at h
      refine ⟨[], ?_, ?_, ?_, ?_⟩
      · simp only [List.length_nil]; omega
      · intro x hx; simp at hx
      · simpa using hinc
      · simpa using h
    · rw [if_neg hkle] at h
      exact absurd h (by simp)
  | succ room ih =>
    intro k c bound acc ps hroom hinc hab hlt hlen h
    by_cases hk : k ≤ acc.length
    · simp only [search, if_pos hk] at h
      refine ⟨[], ?_, ?_, ?_, ?_⟩
      · simp only [List.length_nil]; omega
      · intro x hx; simp at hx
      · simpa using hinc
      · simpa using h
    · simp only [search, if_neg hk] at h
      have hcb : c ≤ bound := by omega
      by_cases hguard : search room k (c + 1) bound (acc ++ [c]) ps = true
      · rw [if_pos hguard] at h
        have hlen1 : (acc ++ [c]).length = acc.length + 1 := by simp
        obtain ⟨rest, hlen', hrest, hInc, hadm⟩ :=
          ih k (c + 1) bound (acc ++ [c]) ps (by omega)
            (inc_append_single hinc c hlt)
            (fun x hx => by
              rcases List.mem_append.1 hx with hx | hx
              · exact hab x hx
              · rcases List.mem_cons.1 hx with rfl | hx
                · exact hcb
                · exact absurd hx (by simp))
            (fun x hx => by
              rcases List.mem_append.1 hx with hx | hx
              · exact Nat.lt_succ_of_lt (hlt x hx)
              · rcases List.mem_cons.1 hx with rfl | hx
                · omega
                · exact absurd hx (by simp))
            (by rw [hlen1]; omega) hguard
        refine ⟨c :: rest, ?_, ?_, ?_, ?_⟩
        · have hh := hlen'
          rw [hlen1] at hh
          simp only [List.length_cons]
          omega
        · intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · exact ⟨Nat.le_refl _, hcb⟩
          · have h1 := (hrest x hx).1
            exact ⟨by omega, (hrest x hx).2⟩
        · simpa [List.append_assoc] using hInc
        · simpa using hadm
      · rw [if_neg hguard] at h
        obtain ⟨rest, hlen', hrest, hInc, hadm⟩ :=
          ih k (c + 1) bound acc ps (by omega) hinc hab
            (fun x hx => Nat.lt_succ_of_lt (hlt x hx)) hlen h
        refine ⟨rest, hlen', ?_, hInc, hadm⟩
        intro x hx
        have h1 := (hrest x hx).1
        exact ⟨by omega, (hrest x hx).2⟩

theorem search_complete : ∀ (room : ℕ) (k c bound : ℕ) (acc ps rest : List ℕ),
    c + room = bound + 1 →
    Inc acc → (∀ x ∈ acc, x ≤ bound) → (∀ x ∈ acc, x < c) → acc.length ≤ k →
    (∀ x ∈ rest, c ≤ x ∧ x ≤ bound) → rest.length + acc.length = k →
    Inc (acc ++ rest) → admB (acc ++ rest) ps = true →
    search room k c bound acc ps = true := by
  intro room
  induction room with
  | zero =>
    intro k c bound acc ps rest hroom hinc hab hlt hlen hrest hrlen hInc hadm
    have hcb : bound < c := by omega
    have hrest0 : rest = [] := by
      cases rest with
      | nil => rfl
      | cons x rest' =>
        have h1 := (hrest x (List.mem_cons_self ..)).1
        have h2 := (hrest x (List.mem_cons_self ..)).2
        omega
    subst hrest0
    have hkle : k ≤ acc.length := by simp only [List.length_nil] at hrlen; omega
    simp only [List.append_nil] at hInc hadm
    simp only [search]
    rw [if_pos hkle]
    exact hadm
  | succ room ih =>
    intro k c bound acc ps rest hroom hinc hab hlt hlen hrest hrlen hInc hadm
    simp only [search]
    by_cases hk : k ≤ acc.length
    · have hrest0 : rest = [] := by
        cases rest with
        | nil => rfl
        | cons x rest' =>
          exfalso
          simp only [List.length_cons] at hrlen
          omega
      subst hrest0
      have hkle : k ≤ acc.length := by simp only [List.length_nil] at hrlen; omega
      simp only [List.append_nil] at hInc hadm
      rw [if_pos hkle]
      exact hadm
    · rw [if_neg hk]
      cases rest with
      | nil => exfalso; simp only [List.length_nil] at hrlen; omega
      | cons c0 rest' =>
        have hc0 : c ≤ c0 ∧ c0 ≤ bound := hrest c0 (List.mem_cons_self ..)
        have hmem' : ∀ x ∈ rest', c0 < x := fun x hx =>
          inc_append_lt acc c0 rest' hInc x hx
        have hlen1 : (acc ++ [c]).length = acc.length + 1 := by simp
        by_cases hguard : search room k (c + 1) bound (acc ++ [c]) ps = true
        · rw [if_pos hguard]
        · rw [if_neg hguard]
          have hc0c : c < c0 := by
            rcases Nat.lt_trichotomy c c0 with hlt' | heq | hgt
            · exact hlt'
            · exfalso
              subst heq
              apply hguard
              refine ih k (c + 1) bound (acc ++ [c]) ps rest' (by omega)
                (inc_append_single hinc c hlt)
                (fun x hx => by
                  rcases List.mem_append.1 hx with hx | hx
                  · exact hab x hx
                  · rcases List.mem_cons.1 hx with rfl | hx
                    · exact hc0.2
                    · exact absurd hx (by simp))
                (fun x hx => by
                  rcases List.mem_append.1 hx with hx | hx
                  · exact Nat.lt_succ_of_lt (hlt x hx)
                  · rcases List.mem_cons.1 hx with rfl | hx
                    · omega
                    · exact absurd hx (by simp))
                (by rw [hlen1]; omega)
                (fun x hx => by
                  have h := hmem' x hx
                  exact ⟨by omega, (hrest x (List.mem_cons_of_mem _ hx)).2⟩)
                (by rw [hlen1]; simp only [List.length_cons] at hrlen; omega)
                (by rw [List.append_assoc]; exact hInc)
                (by simpa using hadm)
            · exact absurd hgt (Nat.not_lt.2 hc0.1)
          refine ih k (c + 1) bound acc ps (c0 :: rest') (by omega) hinc hab
            (fun x hx => Nat.lt_succ_of_lt (hlt x hx)) hlen ?_ hrlen hInc hadm
          · intro x hx
            have hx0 : c0 ≤ x := by
              rcases List.mem_cons.1 hx with rfl | hx
              · exact le_refl _
              · exact Nat.le_of_lt (hmem' x hx)
            exact ⟨by omega, (hrest x hx).2⟩

/-- Elimination theorem: if the exhaustive search over normalized tuples with diameter
`≤ d` finds nothing, then no admissible `k`-tuple of distinct naturals has diameter
`≤ d`. -/
theorem noAdm_elim {k d : ℕ} {ps : List ℕ} (hk : 1 ≤ k)
    (hprime : ∀ p ∈ ps, Nat.Prime p) (h : noAdm k d ps = true) :
    ∀ t, Adm t → Distinct t → t.length = k → diam t ≤ d → False := by
  intro t hAdm hdis hlen hdiam
  have hne : t ≠ [] := by
    intro he
    rw [he] at hlen
    simp only [List.length_nil] at hlen
    omega
  set m := minOf t with hmdef
  have hmle : ∀ a ∈ t, m ≤ a := fun a ha => le_minOf_mem ha
  set u := t.map (· - m) with hudef
  have hAdm_u : Adm u := (adm_sub t m hmle).1 hAdm
  have hdis_u : Distinct u := distinct_map_sub m hmle hdis
  have hlen_u : u.length = k := by rw [hudef, List.length_map]; exact hlen
  have hdiam_u : diam u ≤ d := by rw [diam_map_sub t m hmle]; exact hdiam
  have h0u : (0 : ℕ) ∈ u := List.mem_map.2 ⟨m, minOf_mem hne, Nat.sub_self m⟩
  have hmin_u : minOf u = 0 := by
    have hle := le_minOf_mem (t := u) h0u
    omega
  obtain ⟨s, hsdef⟩ : ∃ s, s = sortInc u := ⟨_, rfl⟩
  have hmem_s : ∀ a, a ∈ s ↔ a ∈ u := fun a => by
    rw [hsdef]
    exact mem_sortInc
  have hAdm_s : Adm s := (adm_congr hmem_s).2 hAdm_u
  have hInc_s : Inc s := by
    rw [hsdef]
    exact sortInc_inc hdis_u
  have hlen_s : s.length = k := by rw [hsdef, length_sortInc]; exact hlen_u
  have hsb : ∀ x ∈ s, x ≤ d := by
    intro x hx
    rw [hmem_s x] at hx
    obtain ⟨a2, ha2, rfl⟩ := List.mem_map.1 hx
    have h1 : a2 ≤ maxOf t := le_maxOf_mem ha2
    have h2 : maxOf t - m = diam t := by rw [hmdef]; rfl
    omega
  have hsne : s ≠ [] := by
    intro he
    rw [he] at hlen_s
    simp only [List.length_nil] at hlen_s
    omega
  cases s with
  | nil => exact absurd rfl hsne
  | cons a l =>
    have ha0 : a = 0 := by
      have h1 : minOf (a :: l) = a := inc_head_min hInc_s
      have h2 : minOf (a :: l) = minOf u := minOf_congr hmem_s
      rw [h2, hmin_u] at h1
      omega
    subst ha0
    have hsearch : search d k 1 d [0] ps = true := search_complete d k 1 d [0] ps l
      (by omega)
      (Inc.cons 0 [] (by simp) Inc.nil)
      (by intro x hx; rcases List.mem_cons.1 hx with rfl | hx
          · omega
          · simp at hx)
      (by intro x hx; rcases List.mem_cons.1 hx with rfl | hx
          · exact Nat.zero_lt_one
          · simp at hx)
      (by omega)
      (by intro x hx
          have hx1 : 0 < x := (inc_cons hInc_s).1 x hx
          exact ⟨by omega, hsb x (List.mem_cons.2 (Or.inr hx))⟩)
      (by show l.length + 1 = k
          have hh := hlen_s
          simp only [List.length_cons] at hh
          omega)
      (by rw [List.cons_append]; exact hInc_s)
      (by show admB (0 :: l) ps = true
          rw [hsdef]
          exact admB_of_Adm hprime
            ((adm_congr (fun a => mem_sortInc (l := u))).mpr hAdm_u))
    have hno : noAdm k d ps = false := by
      unfold noAdm
      rw [hsearch]
      rfl
    rw [hno] at h
    exact Bool.noConfusion h
/-- Minimum-diameter theorem: the exhaustive search certifies that every admissible
`k`-tuple of distinct naturals has diameter at least `D`. -/
theorem diam_min {k D : ℕ} {ps : List ℕ} (hk : 1 ≤ k)
    (hprime : ∀ p ∈ ps, Nat.Prime p) (h : noAdm k (D - 1) ps = true) :
    ∀ t, Adm t → Distinct t → t.length = k → D ≤ diam t := by
  intro t hAdm hdis hlen
  by_contra hge
  push_neg at hge
  exact noAdm_elim hk hprime h t hAdm hdis hlen (by omega)

end Adm
