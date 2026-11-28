import OMAStatements.S_mo_466152
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Zify
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Factorization.Basic

/-! Publisher-supplied problem statement in PR #3132. The proof combines the
Proth block enumeration, binary mirroring, and a count of skipped ranks. -/

namespace OMA.S_mo_466152

private theorem even_two_pow {m : ℕ} (hm : 0 < m) : Even ((2 : ℕ) ^ m) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  rw [pow_succ]
  exact ⟨2 ^ j, by omega⟩

private theorem diff_sq_nat {x y : ℕ} (hyx : y ≤ x) :
    x ^ 2 - y ^ 2 = (x - y) * (x + y) := by
  have hsq : y ^ 2 ≤ x ^ 2 := by gcongr
  zify [hyx, hsq]
  ring

theorem rep_of_pair {k m : ℕ} (hk : Odd k) (hm : 0 < m) (hlt : k < 2 ^ m) :
    Rep (4 * (k * 2 ^ m)) (2 ^ m + k) (2 ^ m - k) := by
  obtain ⟨q, hq⟩ := even_two_pow hm
  obtain ⟨r, hr⟩ := hk
  have hp : 0 < (2 : ℕ) ^ m - k := by omega
  have hlt' : (2 : ℕ) ^ m - k < 2 ^ m + k := by omega
  refine ⟨hp, hlt', ?_, ?_, ⟨m + 1, ?_⟩, ?_⟩
  · exact ⟨q + r, by omega⟩
  · exact ⟨q - (r + 1), by omega⟩
  · rw [pow_succ]
    omega
  · rw [diff_sq_nat hlt'.le]
    have h₁ : (2 : ℕ) ^ m + k - (2 ^ m - k) = 2 * k := by omega
    have h₂ : (2 : ℕ) ^ m + k + (2 ^ m - k) = 2 * 2 ^ m := by omega
    rw [h₁, h₂]
    ring

theorem pair_of_rep {v x y : ℕ} (hrep : Rep v x y) :
    ∃ k m : ℕ, Odd k ∧ 0 < m ∧ k < 2 ^ m ∧ v = 4 * (k * 2 ^ m) ∧
      x = 2 ^ m + k ∧ y = 2 ^ m - k := by
  obtain ⟨hy, hyx, ⟨i, hi⟩, ⟨j, hj⟩, ⟨h, hh⟩, hv⟩ := hrep
  have hh₂ : 2 ≤ h := by
    by_contra! hsmall
    interval_cases h <;> norm_num at hh <;> omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  have hm : 0 < m := by omega
  rw [pow_succ] at hh
  obtain ⟨q, hq⟩ := even_two_pow hm
  let k := i - j
  have hx : x = 2 ^ m + k := by dsimp [k]; omega
  have hyy : y = 2 ^ m - k := by dsimp [k]; omega
  have hk : Odd k := by
    exact ⟨i - q, by dsimp [k]; omega⟩
  refine ⟨k, m, hk, hm, by omega, ?_, hx, hyy⟩
  rw [hv, diff_sq_nat hyx.le]
  have hsub : x - y = 2 * k := by dsimp [k]; omega
  rw [hsub, hh]
  ring

private theorem val_two_mul_odd {k m : ℕ} (hk : Odd k) :
    (k * 2 ^ m).factorization 2 = m := by
  have hk₀ : k ≠ 0 := by obtain ⟨i, hi⟩ := hk; omega
  have hk₂ : ¬2 ∣ k := by
    intro hd
    obtain ⟨i, hi⟩ := hd
    obtain ⟨j, hj⟩ := hk
    omega
  rw [Nat.factorization_mul hk₀ (by positivity)]
  simp only [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hk₂,
    Nat.factorization_pow_self Nat.prime_two, zero_add]

theorem rep_unique {v x y x' y' : ℕ} (h : Rep v x y) (h' : Rep v x' y') :
    x = x' ∧ y = y' := by
  obtain ⟨k, m, hk, hm, hlt, hv, hx, hy⟩ := pair_of_rep h
  obtain ⟨k', m', hk', hm', hlt', hv', hx', hy'⟩ := pair_of_rep h'
  have heq : k * 2 ^ m = k' * 2 ^ m' := by omega
  have hmEq : m = m' := by
    simpa only [val_two_mul_odd hk, val_two_mul_odd hk'] using
      congrArg (fun n : ℕ => n.factorization 2) heq
  subst m'
  have hkEq : k = k' := Nat.eq_of_mul_eq_mul_right (by positivity) heq
  subst k'
  exact ⟨hx.trans hx'.symm, hy.trans hy'.symm⟩

theorem rep_iff_proth (v : ℕ) :
    (∃ x y, Rep v x y) ↔ ∃ z, ProthTerm z ∧ v = 4 * (z - 1) := by
  constructor
  · rintro ⟨x, y, hr⟩
    obtain ⟨k, m, hk, hm, hlt, hv, _, _⟩ := pair_of_rep hr
    exact ⟨k * 2 ^ m + 1, ⟨k, m, hk, hm, hlt, rfl⟩, by simpa using hv⟩
  · rintro ⟨z, ⟨k, m, hk, hm, hlt, rfl⟩, hv⟩
    exact ⟨2 ^ m + k, 2 ^ m - k, by simpa [hv] using rep_of_pair hk hm hlt⟩


private theorem nth_eq_of_range {p : ℕ → Prop} {f : ℕ → ℕ} (hf : StrictMono f)
    (hrange : Set.range f = Set.ofPred p) (i : ℕ) : Nat.nth p i = f i := by
  have hinf : (Set.ofPred p).Infinite :=
    hrange ▸ Set.infinite_range_of_injective hf.injective
  induction i using Nat.strong_induction_on with
  | h i ih =>
    apply (Nat.isLeast_nth_of_infinite hinf i).unique
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change f i ∈ Set.ofPred p
      rw [← hrange]
      exact Set.mem_range_self i
    · intro j hj
      rw [ih j hj]
      exact hf hj
    · intro x hx
      have hpx : p x := hx.1
      have hmem : x ∈ Set.range f := by rw [hrange]; exact hpx
      obtain ⟨j, rfl⟩ := hmem
      apply hf.monotone
      by_contra! hj
      exact (Nat.lt_irrefl (f j)) (by simpa only [ih j hj] using hx.2 j hj)

private theorem proth_infinite : (Set.ofPred ProthTerm).Infinite := by
  refine (Set.infinite_range_of_injective (f := fun n : ℕ => 2 ^ (n + 1) + 1) ?_).mono ?_
  · intro m n h
    dsimp only at h
    have hp : (2 : ℕ) ^ (m + 1) = 2 ^ (n + 1) := by omega
    have heq := (Nat.pow_right_inj (by decide : 1 < (2 : ℕ))).mp hp
    omega
  · rintro _ ⟨i, rfl⟩
    refine ⟨1, i + 1, ⟨0, by decide⟩, by omega, ?_, by simp⟩
    have h : (1 : ℕ) < 2 ^ (i + 1) := by
      rw [pow_succ]
      have hp : 0 < (2 : ℕ) ^ i := by positivity
      omega
    exact h

private theorem proth_pos {z : ℕ} (hz : ProthTerm z) : 0 < z := by
  obtain ⟨k, m, _, _, _, rfl⟩ := hz
  omega

theorem a_eq_four_mul_proth_sub_one (n : ℕ) : a n = 4 * (proth n - 1) := by
  let f := fun i => 4 * (Nat.nth ProthTerm i - 1)
  have hinf := proth_infinite
  apply nth_eq_of_range (f := f)
  · intro i j hij
    have hlt := Nat.nth_strictMono hinf hij
    have hp := proth_pos (Nat.nth_mem_of_infinite hinf i)
    dsimp [f]
    omega
  · ext v
    change (∃ i, f i = v) ↔ ∃ x y, Rep v x y
    rw [rep_iff_proth]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Nat.nth ProthTerm i, Nat.nth_mem_of_infinite hinf i, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨i, _, hi⟩ := Nat.exists_lt_card_nth_eq hz
      exact ⟨i, by simp [f, hi]⟩


/-- In the j-th quadratic-sized block, a predecessor of a Proth number is
    precisely a multiple of the single step size 2^j. -/
theorem proth_iff_dvd_in_block {w j : ℕ} (hj : 0 < j) (hw : 0 < w)
    (hlo : 2 ^ (2 * (j - 1)) ≤ w) (hhi : w < 2 ^ (2 * j)) :
    ProthTerm (w + 1) ↔ 2 ^ j ∣ w := by
  have powMono : Monotone (fun n : ℕ => (2 : ℕ) ^ n) :=
    fun _ _ h => Nat.pow_le_pow_right (by decide) h
  constructor
  · rintro ⟨k, m, hk, hm, hlt, heq⟩
    have hwEq : w = k * 2 ^ m := by omega
    have hbound : w < 2 ^ (2 * m) := by
      rw [hwEq, show 2 * m = m + m by omega, pow_add]
      exact Nat.mul_lt_mul_of_pos_right hlt (by positivity)
    have hjm : j ≤ m := by
      by_contra! hn
      exact (not_lt_of_ge ((powMono (show 2 * m ≤ 2 * (j - 1) by omega)).trans hlo)) hbound
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hjm
    refine ⟨k * 2 ^ r, ?_⟩
    rw [hwEq, hr, pow_add]
    ring
  · intro hd
    obtain ⟨m, k, hk, hwEq⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt hw)
    have hv : w.factorization 2 = m := by
      rw [hwEq, mul_comm, val_two_mul_odd hk]
    have hjm : j ≤ m := by
      rw [← hv]
      exact (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.ne_of_gt hw)).mp hd
    have hbound : w < 2 ^ (2 * m) := hhi.trans_le (powMono (by omega))
    have hlt : k < 2 ^ m := by
      rw [hwEq, show 2 * m = m + m by omega, pow_add] at hbound
      exact Nat.lt_of_mul_lt_mul_left hbound
    exact ⟨k, m, hk, by omega, hlt, by rw [hwEq, mul_comm]⟩


private def block (i : ℕ) : ℕ := Nat.log2 (2 * (i + 2) / 3)
private def base (i : ℕ) : ℕ := 2 ^ block i
private def form (i : ℕ) : ℕ := (i + 2 - base i) * (2 * base i)

private theorem base_bounds (i : ℕ) : 3 * base i ≤ 2 * (i + 2) ∧ 2 * (i + 2) < 6 * base i := by
  have h : 2 * (i + 2) / 3 ≠ 0 := by omega
  have hlo := (Nat.le_log2 h).mp (le_refl (block i))
  have hhi := (Nat.log2_lt h).mp (Nat.lt_succ_self (block i))
  change base i ≤ 2 * (i + 2) / 3 at hlo
  rw [pow_succ] at hhi
  change 2 * (i + 2) / 3 < base i * 2 at hhi
  omega

private theorem base_pos (i : ℕ) : 0 < base i := by
  unfold base
  positivity

private theorem form_bounds (i : ℕ) :
    base i ^ 2 ≤ form i ∧ form i < (2 * base i) ^ 2 := by
  obtain ⟨hlo, hhi⟩ := base_bounds i
  have hp := base_pos i
  have hc₁ : base i ≤ 2 * (i + 2 - base i) := by omega
  have hc₂ : i + 2 - base i < 2 * base i := by omega
  constructor
  · calc
      base i ^ 2 = base i * base i := by ring
      _ ≤ (2 * (i + 2 - base i)) * base i := Nat.mul_le_mul_right _ hc₁
      _ = form i := by unfold form; ring
  · rw [form, pow_two]
    exact Nat.mul_lt_mul_of_pos_right hc₂ (by omega)

private theorem form_increasing : StrictMono form := by
  intro i j hij
  have hpos : 2 * (j + 2) / 3 ≠ 0 := by omega
  have hblocks : block i ≤ block j := by
    apply (Nat.le_log2 hpos).mpr
    have hbound := (Nat.le_log2 (by omega : 2 * (i + 2) / 3 ≠ 0)).mp (le_refl (block i))
    omega
  rcases lt_or_eq_of_le hblocks with hlt | heq
  · have hpow := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show block i + 1 ≤ block j by omega)
    rw [pow_succ] at hpow
    have hbase : 2 * base i ≤ base j := by simpa [base, mul_comm] using hpow
    exact (form_bounds i).2.trans_le ((by gcongr : (2 * base i) ^ 2 ≤ base j ^ 2).trans (form_bounds j).1)
  · have hb : base i = base j := by simp [base, heq]
    have hmin := (base_bounds i).1
    have hp := base_pos i
    have hsub : i + 2 - base i < j + 2 - base i := by omega
    unfold form
    rw [← hb]
    exact Nat.mul_lt_mul_of_pos_right hsub (by omega)

private theorem form_is_proth (i : ℕ) : ProthTerm (form i + 1) := by
  have hp := base_pos i
  have hw : 0 < form i := by
    have hlo := (form_bounds i).1
    have hs : 0 < base i ^ 2 := by positivity
    omega
  have h := form_bounds i
  rw [show base i ^ 2 = 2 ^ (2 * block i) by rw [base, ← pow_mul, mul_comm],
    show (2 * base i) ^ 2 = 2 ^ (2 * (block i + 1)) by
      calc
        (2 * base i) ^ 2 = ((2 : ℕ) ^ (block i + 1)) ^ 2 := congrArg (fun a : ℕ => a ^ 2) (pow_succ' 2 (block i)).symm
        _ = 2 ^ (2 * (block i + 1)) := by rw [← pow_mul, Nat.mul_comm _ 2]] at h
  apply (proth_iff_dvd_in_block (j := block i + 1) (by omega) hw (by simpa using h.1) h.2).mpr
  rw [pow_succ', form, ← base]
  exact dvd_mul_left _ _

private theorem form_covers_proth {z : ℕ} (hz : ProthTerm z) : ∃ i, form i + 1 = z := by
  have htwo : 2 ≤ z := by
    obtain ⟨k, m, ⟨a, ha⟩, _, _, hz⟩ := hz
    have hp : 0 < (2 : ℕ) ^ m := by positivity
    have hmul : 0 < k * 2 ^ m := Nat.mul_pos (by omega) hp
    omega
  let w := z - 1
  have hw : 0 < w := by dsimp [w]; omega
  have hwz : w + 1 = z := by dsimp [w]; omega
  let s := w.log2 / 2
  let P : ℕ := 2 ^ s
  have hP : 0 < P := by dsimp [P]; positivity
  have hlo : 2 ^ (2 * s) ≤ w := (Nat.le_log2 (Nat.ne_of_gt hw)).mp (by dsimp [s]; omega)
  have hhi : w < 2 ^ (2 * (s + 1)) := (Nat.log2_lt (Nat.ne_of_gt hw)).mp (by dsimp [s]; omega)
  obtain ⟨c, hc⟩ := (proth_iff_dvd_in_block (j := s + 1) (by omega) hw
    (by simpa using hlo) hhi).mp (hwz.symm ▸ hz)
  rw [pow_succ', ← show P = (2 : ℕ) ^ s from rfl] at hc
  have hc₀ : 0 < c := by
    by_contra! h
    have hc' : c = 0 := by omega
    simp [hc'] at hc
    omega
  have hc₁ : P ≤ 2 * c := by
    rw [Nat.mul_comm 2 s, pow_mul, ← show P = (2 : ℕ) ^ s from rfl, pow_two, hc, mul_right_comm 2 P c] at hlo
    exact Nat.le_of_mul_le_mul_right hlo hP
  have hc₂ : c < 2 * P := by
    rw [Nat.mul_comm 2 (s + 1), pow_mul, pow_succ' 2 s, ← show P = (2 : ℕ) ^ s from rfl, pow_two, hc] at hhi
    exact Nat.lt_of_mul_lt_mul_left hhi
  let i := c + P - 2
  have hi : i + 2 = c + P := by dsimp [i]; omega
  have hb : block i = s := by
    change Nat.log2 (2 * (i + 2) / 3) = s
    apply (Nat.log2_eq_iff (by omega : 2 * (i + 2) / 3 ≠ 0)).mpr
    constructor
    · change P ≤ 2 * (i + 2) / 3
      omega
    · rw [pow_succ', ← show P = (2 : ℕ) ^ s from rfl]
      omega
  have hb' : base i = P := by simp [base, hb, P]
  refine ⟨i, ?_⟩
  rw [form, hi, hb', Nat.add_sub_cancel, mul_comm c, ← hc, hwz]

theorem proth_closed_form (i : ℕ) : Nat.nth ProthTerm i = form i + 1 := by
  apply nth_eq_of_range (f := fun i => form i + 1)
  · intro i j h
    exact Nat.add_lt_add_right (form_increasing h) 1
  · ext z
    change (∃ i, form i + 1 = z) ↔ ProthTerm z
    exact ⟨by rintro ⟨i, rfl⟩; exact form_is_proth i, form_covers_proth⟩


/-- The Proth roots give a representation for every indexed value, and
    no competing representation exists. -/
theorem canonical_rep (n : ℕ) :
    let xₙ := 2 ^ b₂ n + b₁ n
    let yₙ := 2 ^ b₂ n - b₁ n
    Rep (a n) xₙ yₙ ∧ (∀ x y, Rep (a n) x y → xₙ = x ∧ yₙ = y) := by
  dsimp only
  have hz := Nat.nth_mem_of_infinite proth_infinite (n - 1)
  change ProthTerm (proth n) at hz
  obtain ⟨k, m, hk, hm, hlt, hproth⟩ := hz
  have hw : proth n - 1 = k * 2 ^ m := by omega
  have h₂ : b₂ n = m := by unfold b₂ tr; rw [hw, val_two_mul_odd hk]
  have h₁ : b₁ n = k := by
    unfold b₁
    rw [hw, h₂, Nat.mul_div_cancel _ (by positivity)]
  have hrep : Rep (a n) (2 ^ b₂ n + b₁ n) (2 ^ b₂ n - b₁ n) := by
    rw [a_eq_four_mul_proth_sub_one, hw, h₂, h₁]
    exact rep_of_pair hk hm hlt
  exact ⟨hrep, fun _ _ h => rep_unique hrep h⟩

private theorem index_formula {n : ℕ} (hn : 0 < n) :
    let L := Nat.log2 (n + 1)
    let t := 2 ^ (L - 1)
    block (n - 1) + 1 = L + (if 3 * t ≤ n + 1 then 1 else 0) ∧
    n + 1 - base (n - 1) = t + (n + 1) % t := by
  dsimp only
  let N := n + 1
  let L := Nat.log2 N
  let t : ℕ := 2 ^ (L - 1)
  change block (n - 1) + 1 = L + (if 3 * t ≤ N then 1 else 0) ∧
    N - base (n - 1) = t + N % t
  have hN : 0 < N := by dsimp [N]; omega
  have hidx : (n - 1) + 2 = N := by dsimp [N]; omega
  have htwoN : 2 ≤ N := by dsimp [N]; omega
  have hL : 1 ≤ L := (Nat.le_log2 (Nat.ne_of_gt hN)).mpr htwoN
  have hL' : L = (L - 1) + 1 := by omega
  have hp : 0 < t := by dsimp [t]; positivity
  have hpow : (2 : ℕ) ^ L = 2 * t := by rw [show 2 ^ L = 2 ^ ((L - 1) + 1) from congrArg (fun k : ℕ => (2 : ℕ) ^ k) hL', pow_succ', ← show t = (2 : ℕ) ^ (L - 1) from rfl]
  have hlo : 2 * t ≤ N := hpow ▸ (Nat.le_log2 (Nat.ne_of_gt hN)).mp (le_refl L)
  have hhi : N < 4 * t := by
    have h := (Nat.log2_lt (Nat.ne_of_gt hN)).mp (Nat.lt_succ_self L)
    rw [pow_succ', hpow] at h
    omega
  have hq : 2 * N / 3 ≠ 0 := by omega
  have hb : block (n - 1) = Nat.log2 (2 * N / 3) := by simp only [block, hidx]
  by_cases H : 3 * t ≤ N
  · have hbl : Nat.log2 (2 * N / 3) = L := by
      apply (Nat.log2_eq_iff hq).mpr
      rw [pow_succ', hpow]
      omega
    have hbase : base (n - 1) = 2 * t := by rw [base, hb, hbl, hpow]
    have hrem : N % t = N - 3 * t := by
      have H' : N = t * 3 + (N - 3 * t) := by omega
      conv_lhs => rw [H']
      rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [hb, hbl, hbase, hrem, if_pos H]
    omega
  · have hbl : Nat.log2 (2 * N / 3) = L - 1 := by
      apply (Nat.log2_eq_iff hq).mpr
      rw [← hL']
      change t ≤ 2 * N / 3 ∧ 2 * N / 3 < 2 ^ L
      rw [hpow]
      omega
    have hbase : base (n - 1) = t := by rw [base, hb, hbl]
    have hrem : N % t = N - 2 * t := by
      have H' : N = t * 2 + (N - 2 * t) := by omega
      conv_lhs => rw [H']
      rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [hb, hbl, hbase, hrem, if_neg H]
    omega

/-- Once the palindrome-prefix count is supplied, the three numerical
    formulas in #3132 follow. -/
theorem numeric_formulas_of_prefix (n : ℕ) (hn : 0 < n)
    (hc : c n = (2 : ℕ) ^ (Nat.log2 (n + 1) - 1) +
      (n + 1) % ((2 : ℕ) ^ (Nat.log2 (n + 1) - 1))) :
    let L := Nat.log2 (n + 1)
    let t := 2 ^ (L - 1)
    b₁ n = c n / 2 ^ tr (c n) ∧
    b₂ n = L + tr (c n) + (if 3 * t ≤ n + 1 then 1 else 0) ∧
    a n = c n * 2 ^ (Nat.log2 (2 * (n + 1) / 3) + 3) := by
  dsimp only
  let i := n - 1
  have hidx : i + 2 = n + 1 := by dsimp [i]; omega
  have hb : block i = Nat.log2 (2 * (n + 1) / 3) := by simp only [block, hidx]
  have hc' : c n = n + 1 - base i := by
    have hh := (index_formula hn).2
    rw [hh, hc]
  have hcnz : c n ≠ 0 := by
    rw [hc]
    positivity
  have hproth : proth n - 1 = c n * 2 ^ (block i + 1) := by
    change Nat.nth ProthTerm i - 1 = c n * 2 ^ (block i + 1)
    rw [proth_closed_form, Nat.add_sub_cancel, form, hidx, ← hc', pow_succ', ← base]
  have hb₂ : b₂ n = tr (c n) + (block i + 1) := by
    unfold b₂ tr
    rw [hproth, Nat.factorization_mul hcnz (by positivity)]
    simp only [Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two]
  have hb₁ : b₁ n = c n / 2 ^ tr (c n) := by
    unfold b₁
    rw [hproth, hb₂, pow_add 2 (tr (c n)) (block i + 1)]
    exact Nat.mul_div_mul_right _ _ (by positivity)
  refine ⟨hb₁, ?_, ?_⟩
  · have hh := (index_formula hn).1
    change block i + 1 = _ at hh
    omega
  · rw [a_eq_four_mul_proth_sub_one, hproth, ← hb]
    rw [show block i + 3 = (block i + 1) + 2 by omega, pow_add]
    ring

private def Pal (p : ℕ) : Prop := 0 < p ∧ (Nat.digits 2 p).reverse = Nat.digits 2 p
private def bitMirror (h d : ℕ) : ℕ :=
  let U := Nat.digits 2 h
  Nat.ofDigits 2 ((U.drop d).reverse ++ U)

private theorem bitMirror_spec {h d : ℕ} (hh : 0 < h) (hd : d ≤ 1)
    (hu : d ≤ (Nat.digits 2 h).length) :
    Pal (bitMirror h d) ∧
    (Nat.digits 2 (bitMirror h d)).length = 2 * (Nat.digits 2 h).length - d ∧
    bitMirror h d / 2 ^ ((Nat.digits 2 h).length - d) = h := by
  let U := Nat.digits 2 h
  let W := (U.drop d).reverse ++ U
  have hU : U ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.ne_of_gt hh)
  have hW : W ≠ [] := by
    dsimp only [W]
    simp [hU]
  have hdigits : Nat.digits 2 (bitMirror h d) = W := by
    apply Nat.digits_ofDigits 2 (by decide)
    · intro a ha
      change a ∈ (U.drop d).reverse ++ U at ha
      rw [List.mem_append, List.mem_reverse] at ha
      apply Nat.digits_lt_base (by decide : 1 < (2 : ℕ))
      exact ha.elim (List.mem_of_mem_drop) id
    · intro hin
      rw [show W.getLast hin = U.getLast hU from List.getLast_append_of_ne_nil hin hU]
      exact Nat.getLast_digit_ne_zero 2 (Nat.ne_of_gt hh)
  have hsym : W.reverse = W := by
    have hd' : d = 0 ∨ d = 1 := by omega
    rcases hd' with rfl | rfl
    · simp [W]
    · cases hUeq : U with
      | nil => exact False.elim (hU hUeq)
      | cons a T => simp [W, hUeq, List.append_assoc]
  have hp : 0 < bitMirror h d := by
    by_contra! hz
    have hz' : bitMirror h d = 0 := by omega
    rw [hz', Nat.digits_zero] at hdigits
    exact hW hdigits.symm
  have hlen : W.length = 2 * U.length - d := by
    change d ≤ U.length at hu
    simp only [W, List.length_append, List.length_reverse, List.length_drop]
    omega
  have hloLen : (U.drop d).reverse.length = U.length - d := by simp
  have hlo : Nat.ofDigits 2 (U.drop d).reverse < 2 ^ (U.length - d) := by
    rw [← hloLen]
    apply Nat.ofDigits_lt_base_pow_length (by decide : 1 < (2 : ℕ))
    intro a ha
    rw [List.mem_reverse] at ha
    exact Nat.digits_lt_base (by decide : 1 < (2 : ℕ)) (List.mem_of_mem_drop ha)
  refine ⟨⟨hp, by rw [hdigits, hsym]⟩, by rw [hdigits, hlen], ?_⟩
  change Nat.ofDigits 2 W / 2 ^ (U.length - d) = h
  rw [show W = (U.drop d).reverse ++ U from rfl, Nat.ofDigits_append, hloLen, show Nat.ofDigits 2 U = h from Nat.ofDigits_digits 2 h]
  calc
    _ = Nat.ofDigits 2 (U.drop d).reverse / 2 ^ (U.length - d) + h := Nat.add_mul_div_left _ _ (by positivity)
    _ = h := by simp [Nat.div_eq_of_lt hlo]

private theorem bitMirror_recovers {p : ℕ} (hp : Pal p) :
    let w := (Nat.digits 2 p).length
    let d := w % 2
    let k := w / 2
    let h := p / 2 ^ k
    bitMirror h d = p ∧ (Nat.digits 2 h).length = w - k := by
  dsimp only
  let D := Nat.digits 2 p
  let w := D.length
  let k := w / 2
  let d := w % 2
  let U := D.drop k
  let A := D.take k
  let h := p / 2 ^ k
  have hd : d ≤ 1 := by dsimp [d]; omega
  have hD : D ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.ne_of_gt hp.1)
  have hw : 0 < w := List.length_pos_iff.mpr hD
  have hk : k ≤ w := by dsimp [k]; omega
  have hsplit : A ++ U = D := List.take_append_drop _ _
  have hkA : A.length = k := by
    change (D.take k).length = k
    rw [List.length_take]
    exact Nat.min_eq_left hk
  have hkU : U.length = w - k := by simp [U, w]
  have hU : U ≠ [] := by
    intro hU'
    have hz : U.length = 0 := by simp [hU']
    have hk' : 2 * k ≤ w := by dsimp [k]; omega
    omega
  have hLast : U.getLast hU ≠ 0 := by
    have hi : A ++ U ≠ [] := by simp [hU]
    have hh : (A ++ U).getLast? = D.getLast? := congrArg List.getLast? hsplit
    rw [List.getLast?_eq_some_getLast hi, List.getLast?_eq_some_getLast hD,
      List.getLast_append_of_ne_nil hi hU, Option.some.injEq] at hh
    rw [hh]
    exact Nat.getLast_digit_ne_zero 2 (Nat.ne_of_gt hp.1)
  have hDigits : ∀ a ∈ U, a < 2 :=
    fun a ha => Nat.digits_lt_base (by decide : 1 < (2 : ℕ)) (List.mem_of_mem_drop ha)
  have hlow : Nat.ofDigits 2 A < 2 ^ k := by
    rw [← hkA]
    exact Nat.ofDigits_lt_base_pow_length (by decide)
      (fun a ha => Nat.digits_lt_base (by decide : 1 < (2 : ℕ)) (List.mem_of_mem_take ha))
  have hh : h = Nat.ofDigits 2 U := by
    have hsum : p = Nat.ofDigits 2 A + 2 ^ k * Nat.ofDigits 2 U := by
      rw [← hkA, ← Nat.ofDigits_append, hsplit, Nat.ofDigits_digits]
    change p / 2 ^ k = Nat.ofDigits 2 U
    rw [hsum, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlow, zero_add]
  have hDU : Nat.digits 2 h = U := by
    rw [hh, Nat.digits_ofDigits 2 (by decide) U hDigits]
    exact fun _ => hLast
  have hsym : D.reverse = D := hp.2
  have htake : A = (U.drop d).reverse := by
    change D.take k = ((D.drop k).drop d).reverse
    rw [List.drop_drop]
    have heq : k + d = w - k := by dsimp [d, k]; omega
    rw [heq, ← List.take_reverse, hsym]
  change bitMirror h d = p ∧ (Nat.digits 2 h).length = w - k
  refine ⟨?_, by rw [hDU, hkU]⟩
  change Nat.ofDigits 2 (((Nat.digits 2 h).drop d).reverse ++ Nat.digits 2 h) = p
  rw [hDU, ← htake, hsplit, Nat.ofDigits_digits]

private def preBits (i : ℕ) := Nat.log2 (i + 2)
private def floorP (i : ℕ) : ℕ := 2 ^ (preBits i - 1)
private def shortP (i : ℕ) : ℕ := if i + 2 < 3 * floorP i then 1 else 0
private def leadP (i : ℕ) : ℕ := i + 2 - ((2 - shortP i) * floorP i)
private def palNum (i : ℕ) : ℕ := bitMirror (leadP i) (shortP i)

private theorem preBits_pos (i : ℕ) : 0 < preBits i := by
  exact (Nat.le_log2 (show i + 2 ≠ 0 by omega)).mpr (by simp)

private theorem floorP_pos (i : ℕ) : 0 < floorP i := by unfold floorP; positivity

private theorem floorP_pow (i : ℕ) : (2 : ℕ) ^ preBits i = 2 * floorP i := by
  unfold floorP
  have h : preBits i = (preBits i - 1) + 1 := by have := preBits_pos i; omega
  exact (congrArg (fun a : ℕ => (2 : ℕ) ^ a) h).trans (pow_succ' 2 (preBits i - 1))

private theorem preBits_bounds (i : ℕ) : 2 * floorP i ≤ i + 2 ∧ i + 2 < 4 * floorP i := by
  have h := (Nat.log2_eq_iff (show i + 2 ≠ 0 by omega)).mp (show Nat.log2 (i + 2) = preBits i by rfl)
  rw [pow_succ', floorP_pow i] at h
  omega

private theorem shortP_le (i : ℕ) : shortP i ≤ 1 := by unfold shortP; split <;> omega

private theorem leadP_bounds (i : ℕ) : floorP i ≤ leadP i ∧ leadP i < 2 * floorP i := by
  have := preBits_bounds i
  unfold leadP shortP
  split <;> omega

private theorem leadP_pos (i : ℕ) : 0 < leadP i :=
  (floorP_pos i).trans_le (leadP_bounds i).1

private theorem len_eq_of_pow_bounds {h b : ℕ} (hb : 0 < b)
    (h₁ : (2 : ℕ) ^ (b - 1) ≤ h) (h₂ : h < (2 : ℕ) ^ b) :
    (Nat.digits 2 h).length = b := by
  have hl := (Nat.lt_digits_length_iff (by decide : 1 < (2 : ℕ)) h).mpr h₁
  have hh := (Nat.digits_length_le_iff (by decide : 1 < (2 : ℕ)) h).mpr h₂
  omega

private theorem leadP_len (i : ℕ) : (Nat.digits 2 (leadP i)).length = preBits i := by
  apply len_eq_of_pow_bounds (preBits_pos i) (leadP_bounds i).1
  rw [floorP_pow]
  exact (leadP_bounds i).2

private theorem palNum_spec (i : ℕ) :
    Pal (palNum i) ∧ (Nat.digits 2 (palNum i)).length = 2 * preBits i - shortP i ∧
    palNum i / 2 ^ ((Nat.digits 2 (palNum i)).length / 2) = leadP i := by
  have hd := shortP_le i
  have hb := preBits_pos i
  have h := bitMirror_spec (leadP_pos i) hd (by rw [leadP_len]; omega)
  change Pal (palNum i) ∧ _ ∧ _ at h
  rw [leadP_len] at h
  refine ⟨h.1, h.2.1, ?_⟩
  change bitMirror (leadP i) (shortP i) / 2 ^ ((Nat.digits 2 (bitMirror (leadP i) (shortP i))).length / 2) = leadP i
  rw [h.2.1, show (2 * preBits i - shortP i) / 2 = preBits i - shortP i by omega]
  exact h.2.2

private theorem leadP_mod (i : ℕ) : leadP i = floorP i + (i + 2) % floorP i := by
  have h := preBits_bounds i
  unfold leadP shortP
  split
  · rename_i H
    have hh : i + 2 = floorP i * 2 + (i + 2 - 2 * floorP i) := by omega
    have hh' : (i + 2) % floorP i = i + 2 - 2 * floorP i := by
      conv_lhs => rw [hh]
      rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [hh']
    omega
  · rename_i H
    have hh : i + 2 = floorP i * 3 + (i + 2 - 3 * floorP i) := by omega
    have hh' : (i + 2) % floorP i = i + 2 - 3 * floorP i := by
      conv_lhs => rw [hh]
      rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [hh']
    omega

private theorem palNum_increasing : StrictMono palNum := by
  intro i j hij
  have hi := palNum_spec i
  have hj := palNum_spec j
  have hb : preBits i ≤ preBits j := by
    apply (Nat.le_log2 (show j + 2 ≠ 0 by omega)).mpr
    have h := (Nat.le_log2 (show i + 2 ≠ 0 by omega)).mp (show preBits i ≤ Nat.log2 (i + 2) by rfl)
    omega
  have hd : preBits i = preBits j → shortP j ≤ shortP i := by
    intro heq
    have hp : floorP i = floorP j := by simp only [floorP, heq]
    unfold shortP
    rw [hp]
    split <;> split <;> omega
  have hdi := shortP_le i
  have hdj := shortP_le j
  have hpi := preBits_pos i
  have hpj := preBits_pos j
  by_cases hsame : preBits i = preBits j ∧ shortP i = shortP j
  · have hlen : (Nat.digits 2 (palNum i)).length = (Nat.digits 2 (palNum j)).length := by
      rw [hi.2.1, hj.2.1, hsame.1, hsame.2]
    have hp : floorP i = floorP j := by simp only [floorP, hsame.1]
    have hlead : leadP i < leadP j := by
      unfold leadP
      rw [hp, hsame.2]
      have he : (2 - shortP j) * floorP j ≤ i + 2 := by
        have hh : floorP i ≤ leadP i := (leadP_bounds i).1
        have hf := floorP_pos i
        rw [leadP, hp, hsame.2] at hh
        omega
      omega
    apply lt_of_not_ge
    intro hge
    have hquot := Nat.div_le_div_right (c := 2 ^ ((Nat.digits 2 (palNum j)).length / 2)) hge
    rw [← hlen, hi.2.2, hlen, hj.2.2] at hquot
    omega
  · have hlen : (Nat.digits 2 (palNum i)).length < (Nat.digits 2 (palNum j)).length := by
      rw [hi.2.1, hj.2.1]
      rcases lt_or_eq_of_le hb with hb' | hb'
      · omega
      · have h := hd hb'
        omega
    have h₁ := (Nat.digits_length_le_iff (by decide : 1 < (2 : ℕ)) (palNum i)).mp
      (show (Nat.digits 2 (palNum i)).length ≤ (Nat.digits 2 (palNum i)).length from le_rfl)
    have h₂ := (Nat.lt_digits_length_iff (by decide : 1 < (2 : ℕ)) (palNum j)).mp hlen
    exact h₁.trans_le h₂

private theorem palNum_covers {p : ℕ} (hp : Pal p) : ∃ i, palNum i = p := by
  let w := (Nat.digits 2 p).length
  let d := w % 2
  let k := w / 2
  let h := p / 2 ^ k
  let L := w - k
  let t : ℕ := 2 ^ (L - 1)
  have hw : 0 < w := List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.ne_of_gt hp.1))
  have hL : 0 < L := by dsimp [L,k]; omega
  have hd : d ≤ 1 := by dsimp [d]; omega
  have ht : 0 < t := by dsimp [t]; positivity
  have hs : bitMirror h d = p ∧ (Nat.digits 2 h).length = L := bitMirror_recovers hp
  have hpow : (2 : ℕ) ^ L = 2 * t := by
    have he : L = (L - 1) + 1 := by omega
    exact (congrArg (fun a : ℕ => (2 : ℕ) ^ a) he).trans (pow_succ' 2 (L - 1))
  have hh₁ : t ≤ h := (Nat.lt_digits_length_iff (by decide : 1 < (2 : ℕ)) h).mp (by rw [hs.2]; omega)
  have hh₂ : h < 2 * t := by
    rw [← hpow]
    exact (Nat.digits_length_le_iff (by decide : 1 < (2 : ℕ)) h).mp hs.2.le
  let N := h + (2 - d) * t
  have hN : 2 * t ≤ N ∧ N < 4 * t := by
    have hd' : d = 0 ∨ d = 1 := by omega
    rcases hd' with hd' | hd' <;> dsimp [N] <;> rw [hd'] <;> omega
  have hN' : 2 ≤ N := by omega
  let i := N - 2
  have hi : i + 2 = N := by dsimp [i]; omega
  have hiL : preBits i = L := by
    unfold preBits
    rw [hi]
    apply (Nat.log2_eq_iff (by omega : N ≠ 0)).mpr
    rw [pow_succ', hpow]
    omega
  have hiT : floorP i = t := by simp only [floorP, hiL, t]
  have hiD : shortP i = d := by
    unfold shortP
    rw [hi, hiT]
    have hd' : d = 0 ∨ d = 1 := by omega
    rcases hd' with hd' | hd'
    · have hf : ¬N < 3 * t := by dsimp [N]; rw [hd']; omega
      rw [if_neg hf, hd']
    · have hf : N < 3 * t := by dsimp [N]; rw [hd']; omega
      rw [if_pos hf, hd']
  refine ⟨i, ?_⟩
  have hiLead : leadP i = h := by
    unfold leadP
    rw [hi, hiT, hiD]
    dsimp [N]
    omega
  unfold palNum
  rw [hiLead, hiD]
  exact hs.1

theorem binary_palindrome_prefix (n : ℕ) (hn : 0 < n) :
    c n = (2 : ℕ) ^ (Nat.log2 (n + 1) - 1) +
      (n + 1) % ((2 : ℕ) ^ (Nat.log2 (n + 1) - 1)) := by
  let i := n - 1
  have hNth : Nat.nth Pal i = palNum i := by
    apply nth_eq_of_range palNum_increasing
    ext p
    change (∃ i, palNum i = p) ↔ Pal p
    exact ⟨by rintro ⟨i, rfl⟩; exact (palNum_spec i).1, palNum_covers⟩
  change Nat.nth Pal i / 2 ^ ((Nat.digits 2 (Nat.nth Pal i)).length / 2) = _
  rw [hNth, (palNum_spec i).2.2, leadP_mod]
  have hi : i + 2 = n + 1 := by dsimp [i]; omega
  rw [floorP, preBits, hi]

theorem main_without_permutation : ∀ n : ℕ, 0 < n →
    let L := Nat.log2 (n + 1)
    let t := 2 ^ (L - 1)
    let xₙ := 2 ^ b₂ n + b₁ n
    let yₙ := 2 ^ b₂ n - b₁ n
    c n = t + (n + 1) % t ∧
    b₁ n = c n / 2 ^ tr (c n) ∧
    b₂ n = L + tr (c n) + (if 3 * t ≤ n + 1 then 1 else 0) ∧
    a n = c n * 2 ^ (Nat.log2 (2 * (n + 1) / 3) + 3) ∧
    Rep (a n) xₙ yₙ ∧
    (∀ x y, Rep (a n) x y → xₙ ≤ x ∧ yₙ ≤ y) := by
  intro n hn
  dsimp only
  have hp := binary_palindrome_prefix n hn
  have hf := numeric_formulas_of_prefix n hn hp
  have hrep := canonical_rep n
  refine ⟨hp, hf.1, hf.2.1, hf.2.2, hrep.1, ?_⟩
  intro x y hx
  exact ⟨(hrep.2 x y hx).1.le, (hrep.2 x y hx).2.le⟩
private def valSlot (i : ℕ) := Nat.log2 i + 1
private def halfSlot (i : ℕ) : ℕ := 2 ^ Nat.log2 i
private def oddSlot (i : ℕ) := 2 * (i - halfSlot i) + 1
private def valueSlot (i : ℕ) := oddSlot i * 2 ^ valSlot i

private theorem slot_bounds {i : ℕ} (hi : 0 < i) :
    halfSlot i ≤ i ∧ i < 2 * halfSlot i := by
  have he := Nat.log2_eq_iff (k := Nat.log2 i) (Nat.ne_of_gt hi)
  obtain ⟨hlo, hhi⟩ := he.mp rfl
  rw [pow_succ'] at hhi
  exact ⟨hlo, hhi⟩

private theorem slotPow (i : ℕ) : (2 : ℕ) ^ valSlot i = 2 * halfSlot i :=
  pow_succ' _ _

private theorem proth_slot {i : ℕ} (hi : 0 < i) : ProthTerm (valueSlot i + 1) := by
  have h := slot_bounds hi
  refine ⟨oddSlot i, valSlot i, ⟨i - halfSlot i, rfl⟩, by simp [valSlot], ?_, rfl⟩
  rw [slotPow, oddSlot]
  omega

private theorem slot_of_proth {w : ℕ} (hw : ProthTerm (w + 1)) :
    ∃ i, 0 < i ∧ valueSlot i = w := by
  obtain ⟨a, m, ⟨q, hq⟩, hm, hlt, he⟩ := hw
  let t : ℕ := 2 ^ (m - 1)
  have ht : 0 < t := by dsimp [t]; positivity
  have hpow : (2 : ℕ) ^ m = 2 * t := by
    have heq : m = (m - 1) + 1 := by omega
    exact (congrArg (fun n : ℕ => (2 : ℕ) ^ n) heq).trans (pow_succ' _ _)
  let i := t + q
  have hi : 0 < i := by dsimp [i]; omega
  have hiLog : Nat.log2 i = m - 1 := by
    apply (Nat.log2_eq_iff (k := m - 1) (Nat.ne_of_gt hi)).mpr
    rw [pow_succ']
    change t ≤ i ∧ i < 2 * t
    dsimp [i]
    omega
  have hiHalf : halfSlot i = t := by simp only [halfSlot, hiLog, t]
  have hiV : valSlot i = m := by rw [valSlot, hiLog]; omega
  have hiOdd : oddSlot i = a := by rw [oddSlot, hiHalf]; dsimp [i]; omega
  refine ⟨i, hi, ?_⟩
  rw [valueSlot, hiV, hiOdd]
  omega

private theorem slot_val (i : ℕ) : (valueSlot i).factorization 2 = valSlot i := by
  apply val_two_mul_odd
  exact ⟨i - halfSlot i, rfl⟩

private theorem slot_val_le {i j : ℕ} (hi : 0 < i) (hj : 0 < j) (hij : i ≤ j) :
    valSlot i ≤ valSlot j := by
  have hh := (slot_bounds hi).1
  have h := (Nat.le_log2 (Nat.ne_of_gt hj)).mpr (hh.trans hij)
  unfold valSlot
  omega

private theorem slot_lt_of_val_lt {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (h : valSlot i < valSlot j) : i < j := by
  by_contra! hle
  have := slot_val_le hj hi hle
  omega

private theorem slot_cmp_same_val {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (h : valSlot i = valSlot j) : valueSlot i < valueSlot j ↔ i < j := by
  have hEq : halfSlot i = halfSlot j := by unfold halfSlot; congr 1; unfold valSlot at h; omega
  have hpos : 0 < (2 : ℕ) ^ valSlot j := by positivity
  rw [valueSlot, valueSlot, h, Nat.mul_lt_mul_right hpos, oddSlot, oddSlot, hEq]
  have h₁ := (slot_bounds hi).1
  have h₂ := (slot_bounds hj).1
  omega

private theorem slot_inj {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (h : valueSlot i = valueSlot j) : i = j := by
  have he : valSlot i = valSlot j := by
    rw [← slot_val i, ← slot_val j, h]
  have h₁ := slot_cmp_same_val hi hj he
  have h₂ := slot_cmp_same_val hj hi he.symm
  omega

private noncomputable def rankW (w : ℕ) : ℕ := by
  classical
  exact Nat.count ProthTerm (w + 1) + 1

private theorem rankW_pos (w : ℕ) : 0 < rankW w := by
  classical
  unfold rankW
  omega

private theorem rankW_inverse {w : ℕ} (h : ProthTerm (w + 1)) :
    Nat.nth ProthTerm (rankW w - 1) = w + 1 := by
  classical
  unfold rankW
  rw [Nat.add_sub_cancel]
  exact Nat.nth_count h

private theorem rankW_surj {n : ℕ} (hn : 0 < n) : ∃ w, ProthTerm (w + 1) ∧ rankW w = n := by
  classical
  let p := Nat.nth ProthTerm (n - 1)
  have hp : ProthTerm p := Nat.nth_mem_of_infinite proth_infinite _
  have hz := proth_pos hp
  let w := p - 1
  have he : w + 1 = p := by dsimp [w]; omega
  refine ⟨w, he.symm ▸ hp, ?_⟩
  unfold rankW
  rw [he, Nat.count_nth_of_infinite proth_infinite]
  omega

private theorem rankW_lt_iff {w z : ℕ} (hw : ProthTerm (w + 1)) (hz : ProthTerm (z + 1)) :
    rankW w < rankW z ↔ w < z := by
  have h := Nat.nth_lt_nth proth_infinite (k := rankW w - 1) (n := rankW z - 1)
  rw [rankW_inverse hw, rankW_inverse hz] at h
  have h₁ := rankW_pos w
  have h₂ := rankW_pos z
  omega

private theorem rankW_inj {w z : ℕ} (hw : ProthTerm (w + 1)) (hz : ProthTerm (z + 1))
    (he : rankW w = rankW z) : w = z := by
  have h := rankW_inverse hw
  rw [he, rankW_inverse hz] at h
  omega

private theorem valueSlot_pos {i : ℕ} (_hi : 0 < i) : 0 < valueSlot i := by
  unfold valueSlot oddSlot
  positivity

private theorem valueSlot_upper {i : ℕ} (hi : 0 < i) :
    valueSlot i < 2 ^ (2 * valSlot i) := by
  have hh := slot_bounds hi
  have hu : oddSlot i < 2 ^ valSlot i := by rw [oddSlot, slotPow]; omega
  unfold valueSlot
  rw [show 2 * valSlot i = valSlot i + valSlot i by omega, pow_add]
  exact Nat.mul_lt_mul_of_pos_right hu (by positivity)

private theorem lower_slot_unused_iff {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (h : valueSlot j < valueSlot i) : i ≤ j ↔ valSlot i < valSlot j := by
  constructor
  · intro hij
    have hle := slot_val_le hi hj hij
    rcases lt_or_eq_of_le hle with hlt | he
    · exact hlt
    · have := (slot_cmp_same_val hj hi he.symm).mp h
      omega
  · intro hlt
    exact (slot_lt_of_val_lt hi hj hlt).le

private theorem proth_of_dvd_below {w m : ℕ} (hw : 0 < w) (hm : 0 < m)
    (hb : w < 2 ^ (2 * m)) (hd : 2 ^ m ∣ w) : ProthTerm (w + 1) := by
  obtain ⟨e, a, ha, hwEq⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt hw)
  have hv : w.factorization 2 = e := by rw [hwEq, mul_comm, val_two_mul_odd ha]
  have hme : m ≤ e :=
    hv ▸ (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.ne_of_gt hw)).mp hd
  have hbound : w < 2 ^ (2 * e) :=
    hb.trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega))
  have hlt : a < 2 ^ e := by
    rw [hwEq, show 2 * e = e + e by omega, pow_add] at hbound
    exact Nat.lt_of_mul_lt_mul_left hbound
  exact ⟨a, e, ha, by omega, hlt, by rw [hwEq, mul_comm]⟩


private def skipStep (i : ℕ) : ℕ := 2 ^ (valSlot i + 1)
private def skipVal (i r : ℕ) : ℕ := skipStep i * (r + 1)
private def skipCount (i : ℕ) : ℕ := i - halfSlot i

private theorem skipVal_lt {i r : ℕ} (hr : r < skipCount i) : skipVal i r < valueSlot i := by
  have hmul : 2 * (r + 1) < 2 * (i - halfSlot i) + 1 := by unfold skipCount at hr; omega
  calc
    skipVal i r = 2 * (r + 1) * 2 ^ valSlot i := by unfold skipVal skipStep; rw [pow_succ']; ring
    _ < valueSlot i := by
      unfold valueSlot oddSlot
      exact Nat.mul_lt_mul_of_pos_right hmul (by positivity)

private theorem skipVal_proth {i r : ℕ} (hi : 0 < i) (hr : r < skipCount i) :
    ProthTerm (skipVal i r + 1) := by
  have h := skipVal_lt hr
  have hv := valueSlot_upper hi
  apply proth_of_dvd_below (m := valSlot i) (by unfold skipVal skipStep; positivity)
    (by simp [valSlot]) (h.trans hv)
  unfold skipVal skipStep
  refine ⟨2 * (r + 1), ?_⟩
  rw [pow_succ']
  ring

private theorem skipVal_criterion {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (hlt : valueSlot j < valueSlot i) :
    i ≤ j ↔ ∃ r, r < skipCount i ∧ skipVal i r = valueSlot j := by
  have hw : valueSlot j ≠ 0 := Nat.ne_of_gt (valueSlot_pos hj)
  rw [lower_slot_unused_iff hi hj hlt]
  have hd : valSlot i < valSlot j ↔ skipStep i ∣ valueSlot j := by
    rw [skipStep, Nat.prime_two.pow_dvd_iff_le_factorization hw, slot_val]
    omega
  rw [hd]
  constructor
  · rintro ⟨u, he⟩
    have hu : 0 < u := by
      by_contra! h
      have hz : u = 0 := by omega
      simp [hz] at he
      exact hw he
    let r := u - 1
    have hru : r + 1 = u := by dsimp [r]; omega
    have hEq : skipVal i r = valueSlot j := by rw [skipVal, hru, ← he]
    refine ⟨r, ?_, hEq⟩
    have hlt' : 2 * (r + 1) * 2 ^ valSlot i <
        (2 * skipCount i + 1) * 2 ^ valSlot i := by
      rw [← hEq, skipVal, skipStep, valueSlot, pow_succ'] at hlt
      unfold skipCount
      unfold oddSlot at hlt
      simpa only [mul_right_comm 2 (2 ^ valSlot i) (r + 1)] using hlt
    have hcancel := Nat.lt_of_mul_lt_mul_right hlt'
    omega
  · rintro ⟨r, _, h⟩
    exact ⟨r + 1, by rw [← h, skipVal]⟩

private theorem greedy_step {j : ℕ}
    (hused : ∀ t, t ∈ history j ↔
       ∃ i, 0 < i ∧ i ≤ j ∧ rankW (valueSlot i) = t) :
    Nat.nth (fun t : ℕ => 0 < t ∧ t ∉ history j) (skipCount (j + 1)) =
      rankW (valueSlot (j + 1)) := by
  classical
  let i := j + 1
  have hi : 0 < i := by dsimp [i]; omega
  let u := fun t : ℕ => 0 < t ∧ t ∉ history j
  let R := rankW (valueSlot i)
  have hR : u R := by
    refine ⟨rankW_pos _, ?_⟩
    intro h
    obtain ⟨b, hb, hbj, he⟩ := (hused R).mp h
    have hEq := rankW_inj (proth_slot hb) (proth_slot hi) he
    have hbi := slot_inj hb hi hEq
    dsimp [i] at hbi
    omega
  suffices h : Nat.count u R = skipCount i by
    change Nat.nth u (skipCount i) = R
    rw [← h]
    exact Nat.nth_count hR
  rw [Nat.count_eq_card_filter_range]
  let T := (Finset.range R).filter u
  let S := Finset.range (skipCount i)
  have hcard : S.card = T.card := by
    refine Finset.card_bij (fun r _ => rankW (skipVal i r)) ?_ ?_ ?_
    · intro r hr
      have hr' := Finset.mem_range.mp hr
      have hrank := (rankW_lt_iff (skipVal_proth hi hr') (proth_slot hi)).mpr (skipVal_lt hr')
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr hrank, rankW_pos _, ?_⟩
      intro ht
      obtain ⟨b, hb, hbj, he⟩ := (hused _).mp ht
      have hw := rankW_inj (proth_slot hb) (skipVal_proth hi hr') he
      have hlt : valueSlot b < valueSlot i := by rw [hw]; exact skipVal_lt hr'
      have hbi := (skipVal_criterion hi hb hlt).mpr ⟨r, hr', hw.symm⟩
      dsimp [i] at hbi
      omega
    · intro a ha b hb he
      have hv := rankW_inj (skipVal_proth hi (Finset.mem_range.mp ha))
        (skipVal_proth hi (Finset.mem_range.mp hb)) he
      unfold skipVal at hv
      have ht : 0 < skipStep i := by unfold skipStep; positivity
      have hc := Nat.eq_of_mul_eq_mul_left ht hv
      omega
    · intro t ht
      obtain ⟨ht₁, ht₂⟩ := Finset.mem_filter.mp ht
      obtain ⟨w, hw, hwR⟩ := rankW_surj ht₂.1
      obtain ⟨b, hb, he⟩ := slot_of_proth hw
      have hbR : rankW (valueSlot b) = t := by rwa [he]
      have hRank : rankW (valueSlot b) < rankW (valueSlot i) := by rw [hbR]; exact Finset.mem_range.mp ht₁
      have hlt := (rankW_lt_iff (proth_slot hb) (proth_slot hi)).mp hRank
      have hbi : i ≤ b := by
        by_contra! hn
        apply ht₂.2
        apply (hused t).mpr
        exact ⟨b, hb, by dsimp [i] at hn; omega, hbR⟩
      obtain ⟨r, hr, hrEq⟩ := (skipVal_criterion hi hb hlt).mp hbi
      exact ⟨r, Finset.mem_range.mpr hr, by rwa [hrEq]⟩
  simpa [T, S] using hcard.symm

private theorem used_rank (j : ℕ) (t : ℕ) : t ∈ history j ↔
    ∃ i, 0 < i ∧ i ≤ j ∧ rankW (valueSlot i) = t := by
  induction j generalizing t with
  | zero =>
    simp only [history, List.not_mem_nil, false_iff, not_exists]
    omega
  | succ j ih =>
    have hstep := greedy_step ih
    change Nat.nth (fun t : ℕ => 0 < t ∧ t ∉ history j)
      (j + 1 - 2 ^ Nat.log2 (j + 1)) = rankW (valueSlot (j + 1)) at hstep
    rw [history, hstep, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨i, hi, hij, hie⟩)
      · exact ⟨j + 1, by omega, by omega, rfl⟩
      · exact ⟨i, hi, by omega, hie⟩
    · rintro ⟨i, hi, hij, hie⟩
      by_cases he : i = j + 1
      · left
        exact (by simpa only [he] using hie.symm)
      · exact Or.inr ⟨i, hi, by omega, hie⟩

private theorem perm_eq_rank {i : ℕ} (hi : 0 < i) : perm i = rankW (valueSlot i) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  have hstep := greedy_step (used_rank j)
  exact hstep

private theorem rankW_proth (n : ℕ) (hn : 0 < n) :
    rankW (proth n - 1) = n := by
  classical
  have hp : ProthTerm (proth n) := Nat.nth_mem_of_infinite proth_infinite _
  have hp' : 0 < proth n := proth_pos hp
  unfold rankW
  rw [show proth n - 1 + 1 = proth n by omega]
  unfold proth
  rw [Nat.count_nth_of_infinite proth_infinite]
  omega

private theorem oddRep_slot (n : ℕ) :
    0 < (2 ^ b₂ n + b₁ n) / 2 ∧
      valueSlot ((2 ^ b₂ n + b₁ n) / 2) = proth n - 1 := by
  have hp : ProthTerm (proth n) := Nat.nth_mem_of_infinite proth_infinite _
  have hp' : 0 < proth n := proth_pos hp
  let w := proth n - 1
  obtain ⟨i, hi, he⟩ := slot_of_proth (w := w) (by
    rw [show w + 1 = proth n by dsimp [w]; omega]
    exact hp)
  have hb := slot_bounds hi
  have hpos : 0 < valSlot i := Nat.succ_pos _
  have ho : Odd (oddSlot i) := ⟨i - halfSlot i, rfl⟩
  have hlt : oddSlot i < 2 ^ valSlot i := by
    rw [oddSlot, slotPow]
    omega
  have hrep := rep_of_pair ho hpos hlt
  rw [show oddSlot i * 2 ^ valSlot i = w from he, ← a_eq_four_mul_proth_sub_one n] at hrep
  have hx := (rep_unique (canonical_rep n).1 hrep).1
  have hi' : (2 ^ b₂ n + b₁ n) / 2 = i := by
    rw [hx, slotPow, oddSlot]
    omega
  rw [hi']
  exact ⟨hi, he⟩
theorem proofMain : ∀ n : ℕ, 0 < n →
    let L := Nat.log2 (n + 1)
    let t := 2 ^ (L - 1)
    let xₙ := 2 ^ b₂ n + b₁ n
    let yₙ := 2 ^ b₂ n - b₁ n
    c n = t + (n + 1) % t ∧
    b₁ n = c n / 2 ^ tr (c n) ∧
    b₂ n = L + tr (c n) + (if 3 * t ≤ n + 1 then 1 else 0) ∧
    a n = c n * 2 ^ (Nat.log2 (2 * (n + 1) / 3) + 3) ∧
    Rep (a n) xₙ yₙ ∧
    (∀ x y, Rep (a n) x y → xₙ ≤ x ∧ yₙ ≤ y) ∧
    perm (xₙ / 2) = n := by
  intro n hn
  dsimp only
  have H := main_without_permutation n hn
  have hs := oddRep_slot n
  refine ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1, H.2.2.2.2.1, H.2.2.2.2.2, ?_⟩
  rw [perm_eq_rank hs.1, hs.2, rankW_proth n hn]

end OMA.S_mo_466152


theorem OMA.solution : type_of% @OMA.S_mo_466152.main := OMA.S_mo_466152.proofMain
