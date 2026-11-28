import OMAStatements.S_oeis_a368282

namespace MorphicHofstadter

open OMA.S_oeis_a368282

private theorem offset_succ (w : Nat → Bool) (d i : Nat) :
    offset w d (i+1) = offset w d i + d + (w i).toNat := by
  simp only [offset, Nat.mul_succ, ones]
  omega

private theorem offset_ge (w : Nat → Bool) {d : Nat} (hd : 0 < d) (i : Nat) :
    i ≤ offset w d i := by
  induction i with
  | zero => omega
  | succ i ih =>
    rw [offset_succ]
    omega

/-- The substitution assigns every output position to exactly one block.
Only existence is needed below; strict growth makes the index unique. -/
private theorem block_cover (w : Nat → Bool) {d : Nat} (hd : 0 < d) (k : Nat) :
    ∃ i, offset w d i ≤ k ∧ k < offset w d (i+1) := by
  have aux : ∀ u, k < offset w d u →
      ∃ i, offset w d i ≤ k ∧ k < offset w d (i+1) := by
    intro u
    induction u with
    | zero =>
      simp [offset, ones]
    | succ u ih =>
      intro hk
      by_cases h : k < offset w d u
      · exact ih h
      · exact ⟨u, by omega, hk⟩
  exact aux (k+1) (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (offset_ge w hd _))

/-- Move up to j steps into the run of d ones. -/
private theorem ones_run {w : Nat → Bool} {d : Nat} (h : Fixed w d)
    (i j : Nat) (hj : j ≤ d) :
    ones w (offset w d i + j) = ones w (offset w d i) + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj' : j < d := by omega
    change ones w (offset w d i + j) + (w (offset w d i + j)).toNat =
      ones w (offset w d i) + (j+1)
    rw [h.1 i j hj', ih (by omega), Bool.toNat_true]
    omega

private theorem ones_at_offset {w : Nat → Bool} {d : Nat} (h : Fixed w d) (i : Nat) :
    ones w (offset w d i) = d*i := by
  induction i with
  | zero => simp [offset, ones]
  | succ i ih =>
    have hr := ones_run h i d (Nat.le_refl d)
    rw [offset_succ, Nat.mul_succ]
    cases hw : w i with
    | false =>
      simp [hr, ih]
    | true =>
      have hz := h.2 i hw
      simp [ones, hz, hr, ih]

/--
OEIS A368281/A368282: for every positive divisor d, the prefix ones
counts of a fixed point of 0 ↦ 1^d, 1 ↦ 1^d 0 satisfy precisely the
specified Hofstadter-like recurrence.
-/
theorem recurrence {w : Nat → Bool} {d : Nat} (hd : 0 < d) (h : Fixed w d) :
    ones w 0 = 0 ∧ ∀ k : Nat, ones w (k+1) = (k+1) - ones w (ones w k / d) := by
  refine ⟨rfl, ?_⟩
  intro k
  obtain ⟨i,hi,hk⟩ := block_cover w hd k
  let j := k - offset w d i
  have hk' : k = offset w d i + j := by omega
  have hk1 : k+1 = offset w d i+(j+1) := by omega
  have hn := ones_at_offset h i
  have hbound : j < d + (w i).toNat := by
    rw [offset_succ] at hk
    omega
  by_cases hj : j < d
  · have ha : ones w k = d*i+j := by rw [hk', ones_run h i j (by omega), hn]
    have hb : ones w (k+1) = d*i+(j+1) := by
      rw [hk1, ones_run h i (j+1) (by omega), hn]
    have hdiv : ones w k / d = i := by
      rw [ha, Nat.add_comm, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hj]
      omega
    rw [hdiv, hb]
    dsimp [offset] at hk'
    omega
  · have hw : w i = true := by
      cases v : w i <;> simp [v] at hbound ⊢
      omega
    have hje : j = d := by simp [hw] at hbound; omega
    have hk0 : k = offset w d i + d := hk'.trans (by rw [hje])
    have ha : ones w k = d*i+d := by rw [hk0, ones_run h i d (Nat.le_refl d), hn]
    have hb : ones w (k+1) = d*i+d := by
      rw [ones, ha, hk0, h.2 i hw]
      simp
    have hdiv : ones w k / d = i+1 := by
      rw [ha, ← Nat.mul_succ, Nat.mul_div_right _ hd]
    rw [hdiv, hb, ones, hw, Bool.toNat_true]
    dsimp [offset] at hk0
    omega

private theorem offset_monotone (w : Nat → Bool) (d : Nat) {i j : Nat}
    (hij : i ≤ j) : offset w d i ≤ offset w d j := by
  induction j with
  | zero => rw [show i = 0 by omega]
  | succ j ih =>
    by_cases h : i ≤ j
    · have hs := ih h
      rw [offset_succ]
      omega
    · rw [show i = j + 1 by omega]

private theorem block_unique (w : Nat → Bool) (d k i j : Nat)
    (hi : offset w d i ≤ k ∧ k < offset w d (i+1))
    (hj : offset w d j ≤ k ∧ k < offset w d (j+1)) : i = j := by
  by_cases h : i = j
  · exact h
  · by_cases hjk : i < j
    · have := offset_monotone w d (show i+1 ≤ j by omega)
      omega
    · have : j+1 ≤ i := by omega
      have := offset_monotone w d this
      omega

/-- The infinite output of one substitution, found by locating its input block. -/
noncomputable def transform (w : Nat → Bool) (d : Nat) (hd : 0 < d) (k : Nat) : Bool :=
  decide (k < offset w d (Classical.choose (block_cover w hd k)) + d)

private theorem transform_at {w : Nat → Bool} {d : Nat} (hd : 0 < d) {k i : Nat}
    (hi : offset w d i ≤ k ∧ k < offset w d (i+1)) :
    transform w d hd k = decide (k < offset w d i + d) := by
  unfold transform
  rw [block_unique w d k _ i (Classical.choose_spec (block_cover w hd k)) hi]

private theorem transform_head (w : Nat → Bool) {d : Nat} (hd : 0 < d) :
    transform w d hd 0 = true := by
  rw [transform_at hd (i:=0) (by simp [offset, ones]; omega)]
  simp [offset, ones, hd]

private theorem ones_one_le (w : Nat → Bool) (h : w 0 = true) {k : Nat} (hk : 0 < k) :
    1 ≤ ones w k := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => simp [ones, h]
    | succ j =>
      have := ih (Nat.succ_pos _)
      simp only [ones] at *
      omega

private theorem offset_head (w : Nat → Bool) {d k : Nat} (hd : 0 < d)
    (h : w 0 = true) (hk : 0 < k) : k+1 ≤ offset w d k := by
  have ha := ones_one_le w h hk
  have hb : k ≤ d*k := by
    have := Nat.mul_le_mul_right k (show 1 ≤ d by omega)
    simpa using this
  unfold offset
  omega

private theorem ones_congr {w v : Nat → Bool} {k : Nat}
    (h : ∀ j < k, w j = v j) : ones w k = ones v k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hh := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    rw [ones, ones, hh, h k (Nat.lt_succ_self _)]

/-- If two words agree through k letters and start in 1, substitution makes
their agreement extend through at least k+1 letters. -/
private theorem agreement_grows {w v : Nat → Bool} {d k : Nat} (hd : 0 < d) (hw : w 0 = true)
    (h : ∀ j < k, w j = v j) :
    ∀ j < k+1, transform w d hd j = transform v d hd j := by
  intro j hj
  by_cases hk : k = 0
  · have : j = 0 := by omega
    subst j
    rw [transform_head, transform_head]
  · have hjk : j < offset w d k := Nat.lt_of_lt_of_le hj (offset_head w hd hw (by omega))
    obtain ⟨i,hi,hii⟩ := block_cover w hd j
    have hik : i < k := by
      by_cases he : i < k
      · exact he
      · have : k ≤ i := by omega
        have := offset_monotone w d this
        omega
    have same (s : Nat) (hs : s ≤ k) : offset w d s = offset v d s := by
      unfold offset
      rw [ones_congr (fun x hx => h x (Nat.lt_of_lt_of_le hx hs))]
    have hs₀ := same i (by omega)
    have hs₁ := same (i+1) (by omega)
    rw [transform_at hd ⟨hi,hii⟩, transform_at hd (i:=i) (by rw [← hs₀, ← hs₁]; exact ⟨hi,hii⟩), hs₀]

noncomputable def iter (d : Nat) (hd : 0 < d) : Nat → Nat → Bool
  | 0 => fun _ => true
  | n+1 => transform (iter d hd n) d hd

private theorem iter_head {d : Nat} (hd : 0 < d) (n : Nat) : iter d hd n 0 = true := by
  cases n with
  | zero => rfl
  | succ n => exact transform_head _ hd

private theorem iter_adjacent {d : Nat} (hd : 0 < d) (n : Nat) :
    ∀ j < n, iter d hd n j = iter d hd (n+1) j := by
  induction n with
  | zero =>
    intro j hj
    omega
  | succ n ih =>
    exact agreement_grows hd (iter_head hd n) ih

/-- An explicit limit of progressively stabilized finite prefixes. -/
noncomputable def word (d : Nat) (hd : 0 < d) (j : Nat) : Bool := iter d hd (j+1) j

private theorem word_eq_iter {d : Nat} (hd : 0 < d) {j n : Nat} (h : j < n) :
    word d hd j = iter d hd n j := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : j < n
    · exact (ih he).trans (iter_adjacent hd n j he)
    · have : j = n := by omega
      subst j
      rfl

private theorem transform_word {d : Nat} (hd : 0 < d) (j : Nat) :
    transform (word d hd) d hd j = word d hd j := by
  have hw : word d hd 0 = true := iter_head hd 1
  have eq := agreement_grows hd hw (fun k hk => word_eq_iter hd (n:=j) hk) j (Nat.lt_succ_self _)
  exact eq

/-- The canonical fixed point exists for every positive d, including d=1. -/
theorem word_fixed {d : Nat} (hd : 0 < d) : Fixed (word d hd) d := by
  constructor
  · intro i j hj
    let w := word d hd
    have hi : offset w d i ≤ offset w d i + j ∧
        offset w d i + j < offset w d (i+1) := by
      rw [offset_succ]
      omega
    rw [← transform_word hd, transform_at hd hi]
    simp [hj]
  · intro i h
    let w := word d hd
    have hi : offset w d i ≤ offset w d i + d ∧
        offset w d i + d < offset w d (i+1) := by
      rw [offset_succ]
      change w i = true at h
      simp [h]
    rw [← transform_word hd, transform_at hd hi]
    simp

/-- The Hofstadter-like recurrence determines its sequence uniquely. -/
theorem unique_recurrence (d : Nat) {a b : Nat → Nat}
    (ha0 : a 0 = 0) (hb0 : b 0 = 0)
    (ha : ∀ k, a (k+1) = k+1 - a (a k / d))
    (hb : ∀ k, b (k+1) = k+1 - b (b k / d)) : a = b := by
  have hale : ∀ k, a k ≤ k := by
    intro k
    cases k with
    | zero => simp [ha0]
    | succ k => rw [ha]; exact Nat.sub_le _ _
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rw [ha0, hb0]
    | succ k =>
      have hprev := ih k (Nat.lt_succ_self _)
      have harg : a k / d < k+1 := Nat.lt_succ_of_le (Nat.le_trans (Nat.div_le_self _ _) (hale k))
      rw [ha, hb, ← hprev, ih _ harg]

/-- The fully constructed binary word yields the unique sequence in A368282. -/
theorem canonical_solution {d : Nat} (hd : 0 < d) :
    (ones (word d hd) 0 = 0 ∧
      ∀ k, ones (word d hd) (k+1) = k+1 - ones (word d hd) (ones (word d hd) k / d)) ∧
    ∀ a : Nat → Nat, a 0 = 0 → (∀ k, a (k+1) = k+1 - a (a k/d)) → a = ones (word d hd) := by
  have h := recurrence hd (word_fixed hd)
  exact ⟨h, fun a ha0 ha => unique_recurrence d ha0 h.1 ha h.2⟩

/-- No other infinite binary word has the same fixed-point property. -/
theorem unique_fixed {w : Nat → Bool} {d : Nat} (hd : 0 < d)
    (hw : Fixed w d) : w = word d hd := by
  have h := recurrence hd hw
  have hs := (canonical_solution hd).2 (ones w) h.1 h.2
  funext i
  have hi := congrFun hs i
  have hj := congrFun hs (i+1)
  change ones w i + (w i).toNat = ones (word d hd) i + (word d hd i).toNat at hj
  rw [hi] at hj
  cases hx : w i <;> cases hy : word d hd i <;> simp_all

end MorphicHofstadter





theorem OMA.solution : type_of% @OMA.S_oeis_a368282.main := by
  intro d hd w hw
  exact MorphicHofstadter.recurrence (w:=w) hd hw
