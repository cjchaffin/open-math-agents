import FormalConjectures.ErdosProblems.«111»

-- Credit: @cjchaffin
-- Independent proof using weighted ordered edge graphs and a coloring-history construction.
-- Mathematical research: GPT-6.2 Sol and GPT-6.2 Astra. Lean formalization: GPT-6.2 Sol.
-- A separate deduction follows from Lambie-Hanson, Claim 4.1, arXiv:1902.08177.


/-! Ordered edge graphs and colorings of their iterates. -/

namespace Erdos111Shift

/-- An oriented version of a simple graph. -/
structure Digraph where
  Vertex : Type
  forward : Vertex → Vertex → Prop
  asymmetric : ∀ ⦃a b⦄, forward a b → ¬ forward b a

namespace Digraph

def Arc (D : Digraph) : Type :=
  {a : D.Vertex × D.Vertex // D.forward a.1 a.2}

def tail {D : Digraph} (a : D.Arc) : D.Vertex := a.1.1
def head {D : Digraph} (a : D.Arc) : D.Vertex := a.1.2

theorem arc_ext {D : Digraph} {a b : D.Arc} (h₁ : tail a = tail b)
    (h₂ : head a = head b) : a = b :=
  Subtype.ext (Prod.ext h₁ h₂)

theorem forward_arc {D : Digraph} (a : D.Arc) : D.forward (tail a) (head a) :=
  a.2

def arcs (D : Digraph) : Digraph where
  Vertex := D.Arc
  forward a b := head a = tail b
  asymmetric := by
    intro a b hab hba
    exact D.asymmetric (forward_arc a) (hab ▸ hba.symm ▸ forward_arc b)

def graph (D : Digraph) : SimpleGraph D.Vertex where
  Adj a b := D.forward a b ∨ D.forward b a
  symm := ⟨by intro a b h; exact h.symm⟩
  loopless := ⟨by
    intro a h
    obtain h | h := h
    · exact D.asymmetric h h
    · exact D.asymmetric h h⟩

def proper {D : Digraph} {C : Type} (f : D.Vertex → C) : Prop :=
  ∀ ⦃a b⦄, D.forward a b → f a ≠ f b

def order (α : Type) [LinearOrder α] : Digraph where
  Vertex := α
  forward := (· < ·)
  asymmetric := by intro a b h; exact lt_asymm h

def iterate (D : Digraph) : ℕ → Digraph
  | 0 => D
  | n + 1 => (D.iterate n).arcs

/-- The colors of outgoing arcs give a coloring of the preceding graph. -/
theorem proper_sets {D : Digraph} {C : Type} {f : D.arcs.Vertex → C}
    (hf : proper f) :
    proper (fun a : D.Vertex => {c : C | ∃ e : D.Arc, tail e = a ∧ f e = c}) := by
  intro a b h hab
  let e : D.Arc := ⟨(a, b), h⟩
  change ({c : C | ∃ q : D.Arc, tail q = a ∧ f q = c} : Set C) =
    {c | ∃ q : D.Arc, tail q = b ∧ f q = c} at hab
  have he : f e ∈ {c : C | ∃ q : D.Arc, tail q = a ∧ f q = c} := ⟨e, rfl, rfl⟩
  rw [hab] at he
  obtain ⟨q, hq, heq⟩ := he
  exact (hf (show head e = tail q from hq.symm)) heq.symm

def Palette : ℕ → Type
  | 0 => ℕ
  | n + 1 => Set (Palette n)

theorem collapse {D : Digraph} (r n : ℕ) {f : (D.iterate r).Vertex → Palette n}
    (hf : proper f) : ∃ g : D.Vertex → Palette (n + r), proper g := by
  induction r generalizing n with
  | zero => exact ⟨f, hf⟩
  | succ r ih =>
    have step := ih (n + 1) (proper_sets hf)
    have h : n + 1 + r = n + (r + 1) := by omega
    rwa [h] at step

/-- Iterating the ordered edge operation on a large well-order defeats natural-number colorings. -/
theorem no_natural_coloring (r : ℕ) :
    letI := IsWellOrder.linearOrder (WellOrderingRel : Set (Palette r) → Set (Palette r) → Prop)
    ¬ ∃ f : ((order (Set (Palette r))).iterate r).Vertex → ℕ, proper f := by
  letI := IsWellOrder.linearOrder (WellOrderingRel : Set (Palette r) → Set (Palette r) → Prop)
  rintro ⟨f, hf⟩
  have hc := collapse (D := order (Set (Palette r))) r 0 hf
  rw [Nat.zero_add] at hc
  obtain ⟨g, hg⟩ := hc
  refine Function.cantor_injective g ?_
  intro x y h
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exact (hg hxy h).elim
  · exact hxy
  · exact (hg hyx h.symm).elim

structure Hom (D E : Digraph) where
  toFun : D.Vertex → E.Vertex
  forward' : ∀ ⦃a b⦄, D.forward a b → E.forward (toFun a) (toFun b)

def Hom.arcs {D E : Digraph} (f : Hom D E) : Hom D.arcs E.arcs where
  toFun a := ⟨(f.toFun (tail a), f.toFun (head a)), f.forward' (forward_arc a)⟩
  forward' := by
    intro a b h
    exact congrArg f.toFun h

def Hom.iterate {D E : Digraph} (f : Hom D E) :
    (r : ℕ) → Hom (D.iterate r) (E.iterate r)
  | 0 => f
  | r + 1 => (f.iterate r).arcs

theorem Hom.iterate_injective {D E : Digraph} {f : Hom D E}
    (hf : Function.Injective f.toFun) (r : ℕ) :
    Function.Injective (f.iterate r).toFun := by
  induction r with
  | zero => exact hf
  | succ r ih =>
    intro a b hab
    apply arc_ext
    · apply ih
      exact congrArg tail hab
    · apply ih
      exact congrArg head hab

def height (D : Digraph) : (r : ℕ) → (D.iterate r).Vertex → D.Vertex
  | 0, a => a
  | r + 1, a => height D r (head a)

theorem height_forward {D : Digraph} (r : ℕ) {a b : (D.iterate r).Vertex}
    (h : (D.iterate r).forward a b) : D.forward (height D r a) (height D r b) := by
  induction r with
  | zero => exact h
  | succ r ih =>
    change head a = tail b at h
    change D.forward (height D r (head a)) (height D r (head b))
    rw [h]
    exact ih (forward_arc b)

end Digraph

end Erdos111Shift


/- A subgraph with precisely uncountable chromatic cardinal. -/

open Cardinal

namespace Erdos111Shift
namespace Digraph

variable {α : Type} [LinearOrder α] (D : Digraph) (level : D.Vertex → α)

def History (b : α) : Type := {v : D.Vertex // level v < b} → ℕ

def truncate {a b : α} (h : a ≤ b) (c : D.History level b) : D.History level a :=
  fun x => c ⟨x.1, x.2.trans_le h⟩

def HistoryNode : Type := (v : D.Vertex) × D.History level (level v)

variable {D level}

def predicted {a : α} (hist : D.History level a) (x : D.Vertex) (hx : level x < a) : ℕ :=
  hist ⟨x, hx⟩

section

variable (rises : ∀ ⦃u v⦄, D.forward u v → level u < level v)

noncomputable def selected (x : D.HistoryNode level) (k : ℕ) :
    Option {v : D.Vertex // D.forward v x.1} := by
  classical
  exact if h : ∃ v : {v : D.Vertex // D.forward v x.1}, predicted x.2 v.1 (rises v.2) = k
    then some (Classical.choose h) else none

theorem selected_spec (x : D.HistoryNode level) (k : ℕ)
    (h : ∃ v : {v : D.Vertex // D.forward v x.1}, predicted x.2 v.1 (rises v.2) = k) :
    ∃ v, selected rises x k = some v ∧ predicted x.2 v.1 (rises v.2) = k := by
  classical
  exact ⟨Classical.choose h, by simp [selected, h], Classical.choose_spec h⟩

def previous (x : D.HistoryNode level) (v : {v : D.Vertex // D.forward v x.1}) :
    D.HistoryNode level :=
  ⟨v.1, D.truncate level (rises v.2).le x.2⟩

def historyGraph : Digraph where
  Vertex := D.HistoryNode level
  forward a b := ∃ k v, selected rises b k = some v ∧ a = previous rises b v
  asymmetric := by
    intro x y h₁ h₂
    obtain ⟨_, v, _, rfl⟩ := h₁
    obtain ⟨_, w, _, h⟩ := h₂
    have hp := rises v.2
    have hq := rises w.2
    change level w.1 < level v.1 at hq
    have he : y.1 = w.1 := congrArg Sigma.fst h
    rw [← he] at hq
    exact lt_asymm hp hq

theorem history_rises {x y : (historyGraph rises).Vertex}
    (h : (historyGraph rises).forward x y) : level x.1 < level y.1 := by
  obtain ⟨_, v, _, rfl⟩ := h
  exact rises v.2

variable [WellFoundedLT α]

noncomputable def branch (c : (historyGraph rises).Vertex → ℕ) : D.Vertex → ℕ :=
  (InvImage.wf level wellFounded_lt).fix
    (fun v r => c ⟨v, fun z => r z.1 z.2⟩)

theorem branch_eq (c : (historyGraph rises).Vertex → ℕ) (v : D.Vertex) :
    branch rises c v = c ⟨v, fun z => branch rises c z.1⟩ := by
  unfold branch
  rw [WellFounded.fix_eq]

theorem natural_coloring_descends (c : (historyGraph rises).Vertex → ℕ) (hc : proper c) :
    proper (branch rises c) := by
  intro u v huv eq
  let x : D.HistoryNode level := ⟨v, fun z => branch rises c z.1⟩
  let k := branch rises c v
  have hx : ∃ w : {w : D.Vertex // D.forward w x.1},
      predicted x.2 w.1 (rises w.2) = k := ⟨⟨u, huv⟩, eq⟩
  obtain ⟨w, hselected, hcolor⟩ := selected_spec rises x k hx
  have ha : (historyGraph rises).forward (previous rises x w) x :=
    ⟨k, w, hselected, rfl⟩
  apply hc ha
  change c ⟨w.1, fun z => branch rises c z.1⟩ = c ⟨v, fun z => branch rises c z.1⟩
  rwa [← branch_eq rises c w.1, ← branch_eq rises c v]

private theorem exists_fresh {C : Type} [Uncountable C] (f : ℕ → C) :
    ∃ c, c ∉ Set.range f := by
  by_contra! h
  apply Set.not_countable_univ (α := C)
  rw [← Set.eq_univ_of_forall h]
  exact Set.countable_range f

private noncomputable def previousColors {C : Type} (default : C) (x : D.HistoryNode level)
    (f : ∀ y : D.HistoryNode level, level y.1 < level x.1 → C) (k : ℕ) : C :=
  match selected rises x k with
  | none => default
  | some y => f (previous rises x y) (rises y.2)

noncomputable def upperColor {C : Type} [Uncountable C] (default : C) :
    D.HistoryNode level → C :=
  (InvImage.wf (fun x : D.HistoryNode level => level x.1) wellFounded_lt).fix
    (fun x f => Classical.choose (exists_fresh (previousColors rises default x f)))

theorem upperColor_proper {C : Type} [Uncountable C] (default : C) :
    proper (D := historyGraph rises) (upperColor rises default) := by
  intro a b hab hsame
  obtain ⟨k, y, hy, rfl⟩ := hab
  change D.HistoryNode level at b
  let f := fun (x : D.HistoryNode level) (_ : level x.1 < level b.1) =>
    upperColor rises default x
  have hB : upperColor rises default b =
      Classical.choose (exists_fresh (previousColors rises default b f)) := by
    unfold upperColor
    rw [WellFounded.fix_eq]
    rfl
  have havoids : upperColor rises default b ∉ Set.range (previousColors rises default b f) :=
    hB.symm ▸ Classical.choose_spec (exists_fresh (previousColors rises default b f))
  apply havoids
  refine ⟨k, ?_⟩
  simp only [previousColors, hy]
  exact hsame

theorem chromatic_history (hD : ¬ ∃ f : D.Vertex → ℕ, proper f) :
    (historyGraph rises).graph.chromaticCardinal = ℵ₁ := by
  classical
  let J := historyGraph rises
  let C := (ℵ₁ : Cardinal).out
  have cmk : #C = ℵ₁ := Cardinal.mk_out _
  have : Uncountable C := Cardinal.aleph0_lt_mk_iff.mp (by
    simpa only [cmk] using (Cardinal.aleph0_lt_aleph_one : ℵ₀ < ℵ₁))
  let default : C := Classical.choice (Cardinal.nonempty_out (ne_of_gt (Cardinal.aleph_pos 1)))
  let c := upperColor rises default
  have hc : proper (D := J) c := upperColor_proper rises default
  have color : J.graph.Coloring C := SimpleGraph.Coloring.mk c (by
    rintro a b (h | h)
    · exact hc h
    · exact Ne.symm (hc h))
  let S := {κ : Cardinal | ∃ (F : Type) (_ : #F = κ), Nonempty (J.graph.Coloring F)}
  have hS : ℵ₁ ∈ S := ⟨C, cmk, ⟨color⟩⟩
  change sInf S = ℵ₁
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) hS
  · apply le_csInf ⟨ℵ₁, hS⟩
    rintro κ ⟨F, rfl, ⟨g⟩⟩
    rw [aleph_one_le_iff]
    by_contra! h
    obtain ⟨i⟩ : Nonempty (F ↪ ℕ) := (Cardinal.le_def F ℕ).mp (by simpa using h)
    apply hD
    refine ⟨branch rises (i ∘ g), natural_coloring_descends rises _ ?_⟩
    intro a b hab he
    exact g.valid (Or.inl hab) (i.injective he)

end

end Digraph
end Erdos111Shift


/- The history graph embeds in a shift over decorated letters. -/

namespace Erdos111Shift
namespace Digraph

noncomputable section

variable {α : Type} [LinearOrder α] (H : Digraph) (level : H.Vertex → α)

def decorated : Digraph where
  Vertex := (a : α) × H.History level a
  forward a b := a.1 < b.1
  asymmetric := by intro a b h; exact lt_asymm h

def decorate (f : H.Vertex → ℕ) : Hom (order α) (decorated H level) where
  toFun a := ⟨a, fun v => f v.1⟩
  forward' := by intro a b h; exact h

def forget : Hom (decorated H level) (order α) where
  toFun a := a.1
  forward' := by intro a b h; exact h

theorem forget_decorate (f : H.Vertex → ℕ) (r : ℕ)
    (a : ((order α).iterate r).Vertex) :
    ((forget H level).iterate r).toFun (((decorate H level f).iterate r).toFun a) = a := by
  induction r with
  | zero => rfl
  | succ r ih =>
    apply arc_ext
    · exact ih (tail a)
    · exact ih (head a)

theorem decorate_height (f : H.Vertex → ℕ) (r : ℕ)
    (a : ((order α).iterate r).Vertex) :
    height (decorated H level) r (((decorate H level f).iterate r).toFun a) =
      (⟨height (order α) r a, fun v => f v.1⟩ : (decorated H level).Vertex) := by
  induction r with
  | zero => rfl
  | succ r ih => exact ih (head a)

theorem decorate_eq_of_agree (f g : H.Vertex → ℕ) (r : ℕ)
    (a : ((order α).iterate r).Vertex)
    (h : ∀ x, level x < height (order α) r a → f x = g x) :
    ((decorate H level f).iterate r).toFun a = ((decorate H level g).iterate r).toFun a := by
  induction r with
  | zero =>
    change (⟨a, fun x => f x.1⟩ : (decorated H level).Vertex) = ⟨a, fun x => g x.1⟩
    exact congrArg (Sigma.mk a) (funext fun x => h x.1 x.2)
  | succ r ih =>
    have he := height_forward r (forward_arc a)
    apply arc_ext
    · exact ih (tail a) (fun x hx => h x (hx.trans he))
    · exact ih (head a) h

variable {H level}

def extend {b : α} (p : H.History level b) (v : H.Vertex) : ℕ := by
  classical
  exact if h : level v < b then p ⟨v, h⟩ else 0

theorem extend_eq {b : α} (p : H.History level b) (v : H.Vertex) (hv : level v < b) :
    extend p v = p ⟨v, hv⟩ := by
  classical
  simp [extend, hv]

abbrev orderShift (α : Type) [LinearOrder α] (r : ℕ) := (order α).iterate r
abbrev orderLevel (α : Type) [LinearOrder α] (r : ℕ) :
    (orderShift α r).Vertex → α := height (order α) r

theorem orderRises (α : Type) [LinearOrder α] (r : ℕ) :
    ∀ ⦃x y⦄, (orderShift α r).forward x y → orderLevel α r x < orderLevel α r y := by
  intro x y h
  exact height_forward (D := order α) r h

variable (r : ℕ)

def decorateNode (a : (orderShift α r).HistoryNode (orderLevel α r)) :
    ((decorated (orderShift α r) (orderLevel α r)).iterate r).Vertex :=
  ((decorate (orderShift α r) (orderLevel α r) (extend a.2)).iterate r).toFun a.1

theorem decorateNode_injective :
    Function.Injective (decorateNode (α := α) r) := by
  intro a b hab
  have h₁ : a.1 = b.1 := by
    simpa only [decorateNode, forget_decorate] using
      congrArg (((forget (orderShift α r) (orderLevel α r)).iterate r).toFun) hab
  obtain ⟨a, f⟩ := a
  obtain ⟨b, g⟩ := b
  change a = b at h₁
  subst b
  have h₂ := congrArg (height (decorated (orderShift α r) (orderLevel α r)) r) hab
  simp only [decorateNode, decorate_height] at h₂
  apply congrArg (Sigma.mk a)
  apply funext
  intro x
  have hp := eq_of_heq (Sigma.mk.inj_iff.mp h₂).2
  have hh := congrArg
    (fun p : (orderShift α r).History (orderLevel α r) (orderLevel α r a) => p x) hp
  simpa only [extend_eq _ _ x.2] using hh

theorem decorateNode_forward {a b : (orderShift α r).HistoryNode (orderLevel α r)}
    (h : (historyGraph (orderRises α r)).forward a b) :
    ((decorated (orderShift α r) (orderLevel α r)).iterate r).forward
      (decorateNode r a) (decorateNode r b) := by
  obtain ⟨_, v, _, rfl⟩ := h
  let D := orderShift α r
  let level := orderLevel α r
  have he : decorateNode r (previous (orderRises α r) b v) =
      ((decorate D level (extend b.2)).iterate r).toFun v.1 := by
    apply decorate_eq_of_agree
    intro x hx
    rw [extend_eq _ _ hx, extend_eq _ _ (hx.trans (orderRises α r v.2))]
    rfl
  rw [he]
  exact ((decorate D level (extend b.2)).iterate r).forward' v.2

end
end Digraph
end Erdos111Shift


/- Weighted bipartization bounds for iterated ordered edge graphs. -/

open Finset
open scoped BigOperators
open scoped Classical

namespace Erdos111Shift
namespace Digraph

noncomputable section

def badCost (D : Digraph) (S : Finset D.Vertex) (w : D.Vertex → ℕ)
    (c : D.Vertex → Bool) : ℕ :=
  ∑ a ∈ S, ∑ b ∈ S,
    if D.forward a b ∧ c a = c b then min (w a) (w b) else 0

variable {D : Digraph}

def outMass (E : Finset D.Arc) (w : D.Arc → ℕ) (x : D.Vertex) : ℕ :=
  ∑ e ∈ E, if tail e = x then w e else 0

def inMass (E : Finset D.Arc) (w : D.Arc → ℕ) (x : D.Vertex) : ℕ :=
  ∑ e ∈ E, if head e = x then w e else 0

def mass (E : Finset D.Arc) (w : D.Arc → ℕ) (x : D.Vertex) : ℕ :=
  outMass E w x + inMass E w x

def hubs (E : Finset D.Arc) : Finset D.Vertex :=
  E.image tail ∪ E.image head

theorem sum_outMass (E : Finset D.Arc) (w : D.Arc → ℕ) :
    ∑ x ∈ hubs E, outMass E w x = ∑ e ∈ E, w e := by
  unfold outMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have hh : tail e ∈ hubs E :=
    Finset.mem_union_left _ (Finset.mem_image_of_mem tail he)
  simp [hh]

theorem sum_inMass (E : Finset D.Arc) (w : D.Arc → ℕ) :
    ∑ x ∈ hubs E, inMass E w x = ∑ e ∈ E, w e := by
  unfold inMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have hh : head e ∈ hubs E :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem head he)
  simp [hh]

def paid (E : Finset D.Arc) (w : D.Arc → ℕ) (T : ℕ)
    (s : D.Vertex → Bool) (e : D.Arc) : Bool :=
  if T ≤ mass E w (tail e) ∧ mass E w (head e) ≤ mass E w (tail e) then s (tail e)
  else !(s (head e))

def tailFault (E : Finset D.Arc) (w : D.Arc → ℕ) (T : ℕ)
    (s : D.Vertex → Bool) (e : D.Arc) : Prop :=
  mass E w (tail e) < T ∨ paid E w T s e ≠ s (tail e)

def headFault (E : Finset D.Arc) (w : D.Arc → ℕ) (T : ℕ)
    (s : D.Vertex → Bool) (e : D.Arc) : Prop :=
  mass E w (head e) < T ∨ paid E w T s e ≠ !(s (head e))

theorem fault_cover (E : Finset D.Arc) (w : D.Arc → ℕ) (T : ℕ)
    (s : D.Vertex → Bool) {e f : D.Arc} (h : head e = tail f)
    (hc : paid E w T s e = paid E w T s f) :
    headFault E w T s e ∨ tailFault E w T s f := by
  by_contra! hbad
  have he : paid E w T s e = !(s (head e)) :=
    not_not.mp (fun h => hbad.1 (Or.inr h))
  have hf : paid E w T s f = s (tail f) :=
    not_not.mp (fun h => hbad.2 (Or.inr h))
  rw [he, hf, h] at hc
  cases hb : s (tail f) <;> simp [hb] at hc

theorem cost_le_charges (E : Finset D.Arc) (w : D.Arc → ℕ) (T : ℕ)
    (s : D.Vertex → Bool) :
    badCost D.arcs E w (paid E w T s) ≤
      ∑ e ∈ E,
        ((if headFault E w T s e then mass E w (head e) else 0) +
         (if tailFault E w T s e then mass E w (tail e) else 0)) := by
  let h (e f : D.Arc) :=
    if headFault E w T s e ∧ head e = tail f then w f else 0
  let t (e f : D.Arc) :=
    if tailFault E w T s f ∧ head e = tail f then w e else 0
  unfold badCost
  calc
    _ ≤ ∑ e ∈ E, ∑ f ∈ E, (h e f + t e f) := by
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro f _
      change (if head e = tail f ∧ paid E w T s e = paid E w T s f
        then min (w e) (w f) else 0) ≤ h e f + t e f
      split_ifs with ha
      · rcases fault_cover E w T s ha.1 ha.2 with he | hf
        · simp only [h, he, ha.1, and_self, if_true]
          exact (min_le_right _ _).trans (Nat.le_add_right _ _)
        · simp only [t, hf, ha.1, and_self, if_true]
          exact (min_le_left _ _).trans (Nat.le_add_left _ _)
      · exact Nat.zero_le _
    _ = ∑ e ∈ E, ((∑ f ∈ E, h e f) + ∑ f ∈ E, t f e) := by
      simp only [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro e _
      apply Nat.add_le_add
      · by_cases he : headFault E w T s e
        · simp only [h, he, true_and, if_true, mass, outMass, eq_comm (a := head e)]
          exact Nat.le_add_right _ _
        · simp [h, he]
      · by_cases he : tailFault E w T s e
        · simp only [t, he, true_and, if_true, mass, inMass]
          exact Nat.le_add_left _ _
        · simp [t, he]

theorem count_mul_le_weight {α : Type} (E : Finset α) (w : α → ℕ) (l : ℕ)
    (hw : ∀ e ∈ E, l ≤ w e) :
    E.card * l ≤ ∑ e ∈ E, w e := by
  calc
    E.card * l = ∑ _e ∈ E, l := by simp
    _ ≤ _ := Finset.sum_le_sum hw

theorem cost_trivial (S : Finset D.Vertex) (w : D.Vertex → ℕ) (c : D.Vertex → Bool) :
    badCost D S w c ≤ S.card * ∑ e ∈ S, w e := by
  unfold badCost
  calc
    _ ≤ ∑ _a ∈ S, ∑ b ∈ S, w b := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      split_ifs
      · exact min_le_right _ _
      · exact Nat.zero_le _
    _ = _ := by simp

def heavy (E : Finset D.Arc) (w : D.Arc → ℕ) (T : ℕ) : Finset D.Vertex :=
  (hubs E).filter fun x => T ≤ mass E w x

def clash (E : Finset D.Arc) (w : D.Arc → ℕ) (T : ℕ)
    (s : D.Vertex → Bool) (e : D.Arc) : Prop :=
  T ≤ mass E w (tail e) ∧ T ≤ mass E w (head e) ∧ s (tail e) = s (head e)

theorem charge_le_clash (E : Finset D.Arc) (w : D.Arc → ℕ) (T : ℕ)
    (s : D.Vertex → Bool) (e : D.Arc) :
    (if headFault E w T s e then mass E w (head e) else 0) +
      (if tailFault E w T s e then mass E w (tail e) else 0) ≤
    T + T + (if clash E w T s e then min (mass E w (tail e)) (mass E w (head e)) else 0) := by
  simp only [headFault, tailFault, paid, clash]
  by_cases ha : T ≤ mass E w (tail e) <;>
    by_cases hb : T ≤ mass E w (head e) <;>
    by_cases hd : mass E w (head e) ≤ mass E w (tail e) <;>
    rcases Bool.eq_false_or_eq_true (s (tail e)) with hs | hs <;>
    rcases Bool.eq_false_or_eq_true (s (head e)) with ht | ht <;>
    simp [ha, hb, hd, hs, ht, Nat.min_def] <;> (try split_ifs) <;> omega

theorem sum_clashes (E : Finset D.Arc) (w : D.Arc → ℕ) (T : ℕ)
    (s : D.Vertex → Bool) :
    (∑ e ∈ E, if clash E w T s e then min (mass E w (tail e)) (mass E w (head e)) else 0) ≤
      badCost D (heavy E w T) (mass E w) s := by
  let Q := E.filter (clash E w T s)
  let f (e : D.Arc) : D.Vertex × D.Vertex := (tail e, head e)
  let g (p : D.Vertex × D.Vertex) :=
    if D.forward p.1 p.2 ∧ s p.1 = s p.2 then min (mass E w p.1) (mass E w p.2) else 0
  have hf : Function.Injective f := fun _ _ he =>
    arc_ext (congrArg Prod.fst he) (congrArg Prod.snd he)
  have hQ : Q.image f ⊆ (heavy E w T) ×ˢ (heavy E w T) := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hm, htail, hhead, _⟩ := Finset.mem_filter.mp he
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem tail hm), htail⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem head hm), hhead⟩⟩
  calc
    _ = ∑ e ∈ Q, g (f e) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : clash E w T s e
      · simp [he, f, g, forward_arc e, he.2.2]
      · simp [he]
    _ = ∑ p ∈ Q.image f, g p := by
      rw [Finset.sum_image (fun _ _ _ _ h => hf h)]
    _ ≤ ∑ p ∈ (heavy E w T) ×ˢ (heavy E w T), g p :=
      Finset.sum_le_sum_of_subset_of_nonneg hQ (fun _ _ _ => Nat.zero_le _)
    _ = _ := by rw [Finset.sum_product]; rfl

theorem weighted_step (E : Finset D.Arc) (w : D.Arc → ℕ) (T : ℕ)
    (s : D.Vertex → Bool) :
    badCost D.arcs E w (paid E w T s) ≤
      E.card * (T + T) + badCost D (heavy E w T) (mass E w) s := by
  apply (cost_le_charges E w T s).trans
  calc
    _ ≤ ∑ e ∈ E, (T + T +
        (if clash E w T s e then min (mass E w (tail e)) (mass E w (head e)) else 0)) :=
      Finset.sum_le_sum fun e _ => charge_le_clash E w T s e
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      exact Nat.add_le_add_left (sum_clashes E w T s) _

def boundConstant : ℕ → ℕ
  | 0 => 1
  | r + 1 => 4 + 2 * boundConstant r

theorem weighted_iterate (D : Digraph) (r : ℕ) (S : Finset (D.iterate r).Vertex)
    (w : (D.iterate r).Vertex → ℕ) (l m : ℕ)
    (hl : 0 < l) (hm : 0 < m) (hw : ∀ x ∈ S, l ≤ w x)
    (hW : (∑ x ∈ S, w x) ≤ l * m ^ (r + 1)) :
    ∃ s : (D.iterate r).Vertex → Bool,
      badCost (D.iterate r) S w s ≤ boundConstant r * (∑ x ∈ S, w x) * m := by
  induction r generalizing l with
  | zero =>
    refine ⟨fun _ => false, (cost_trivial S w _).trans ?_⟩
    have h := (count_mul_le_weight S w l hw).trans hW
    have hs : S.card ≤ m := by
      simp only [Nat.zero_add, pow_one, Nat.mul_comm l] at h
      exact Nat.le_of_mul_le_mul_right h hl
    simpa [boundConstant, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_right (∑ x ∈ S, w x) hs
  | succ r ih =>
    let G := D.iterate r
    let T := 2 * l * m
    let W := ∑ x ∈ S, w x
    have hW' : (∑ x ∈ heavy S w T, mass S w x) ≤ 2 * W := by
      calc
        _ ≤ ∑ x ∈ hubs S, mass S w x :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by simp)
        _ = 2 * W := by
          simp only [mass, Finset.sum_add_distrib, two_mul, W]
          exact congrArg₂ (· + ·) (sum_outMass (D := G) S w) (sum_inMass (D := G) S w)
    have hT : 0 < T := by dsimp [T]; positivity
    have hM : (∑ x ∈ heavy S w T, mass S w x) ≤ T * m ^ (r + 1) := by
      apply hW'.trans
      calc
        _ ≤ 2 * (l * m ^ (r + 1 + 1)) := Nat.mul_le_mul_left 2 hW
        _ = _ := by rw [pow_succ]; dsimp [T]; ring
    obtain ⟨s, hs⟩ := ih (S := heavy S w T) (w := mass S w) T hT
      (fun _ hx => (Finset.mem_filter.mp hx).2) hM
    refine ⟨paid S w T s, (weighted_step S w T s).trans ?_⟩
    have hlight : S.card * (T + T) ≤ 4 * W * m := by
      calc
        _ = 4 * (S.card * l) * m := by dsimp [T]; ring
        _ ≤ _ := Nat.mul_le_mul_right m (Nat.mul_le_mul_left 4 (count_mul_le_weight S w l hw))
    have hheavy := hs.trans (Nat.mul_le_mul_right m (Nat.mul_le_mul_left (boundConstant r) hW'))
    calc
      _ ≤ 4 * W * m + boundConstant r * (2 * W) * m := Nat.add_le_add hlight hheavy
      _ = _ := by rw [boundConstant]; ring

end

end Digraph
end Erdos111Shift


/- Transfer a weighted ordered-edge bound to the exact finite-subgraph statement. -/

open Finset Cardinal
open scoped BigOperators Classical

namespace Erdos111Shift
namespace Digraph

noncomputable section

theorem badCost_transfer {D E : Digraph} (f : Hom D E) (hf : Function.Injective f.toFun)
    (S : Finset D.Vertex) (c : E.Vertex → Bool) :
    badCost D S (fun _ => 1) (c ∘ f.toFun) ≤
      badCost E (S.image f.toFun) (fun _ => 1) c := by
  unfold badCost
  rw [Finset.sum_image (fun _ _ _ _ h => hf h)]
  apply Finset.sum_le_sum
  intro a _
  rw [Finset.sum_image (fun _ _ _ _ h => hf h)]
  apply Finset.sum_le_sum
  intro b _
  split_ifs with hD hE hE
  · rfl
  · exact (hE ⟨f.forward' hD.1, hD.2⟩).elim
  · exact Nat.zero_le _
  · rfl

def crossing (D : Digraph) (c : D.Vertex → Bool) : SimpleGraph D.Vertex where
  Adj u v := D.graph.Adj u v ∧ c u ≠ c v
  symm := ⟨by intro _ _ h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro _ h; exact h.2 rfl⟩

theorem crossing_bipartite (D : Digraph) (c : D.Vertex → Bool) :
    (crossing D c).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (fun x => if c x then (1 : Fin 2) else 0) ?_⟩
  intro a b h
  have hn : c a ≠ c b := h.2
  cases ha : c a <;> cases hb : c b <;> simp_all

theorem distance_le_cost (D : Digraph) [Fintype D.Vertex] (c : D.Vertex → Bool) :
    Erdos111.bipartiteDistance D.graph ≤ badCost D Finset.univ (fun _ => 1) c := by
  let F : Finset (D.Vertex × D.Vertex) :=
    (Finset.univ ×ˢ Finset.univ).filter fun p => D.forward p.1 p.2 ∧ c p.1 = c p.2
  let image := F.image fun p => s(p.1, p.2)
  have hsub : D.graph.edgeSet \ (crossing D c).edgeSet ⊆ (image : Set (Sym2 D.Vertex)) := by
    intro p hp
    induction p using Sym2.inductionOn with
    | _ a b =>
      have hD : D.graph.Adj a b := hp.1
      have hn : c a = c b := by
        by_contra h
        exact hp.2 (show (crossing D c).Adj a b from ⟨hD, h⟩)
      rcases hD with hd | hd
      · exact Finset.mem_image.mpr ⟨(a, b), by simp [F, hd, hn], rfl⟩
      · exact Finset.mem_image.mpr ⟨(b, a), by simp [F, hd, hn.symm], Sym2.eq_swap⟩
  have hcard : F.card = badCost D Finset.univ (fun _ => 1) c := by
    calc
      F.card = ∑ _p ∈ F, (1 : ℕ) := by simp
      _ = _ := by rw [Finset.sum_filter, Finset.sum_product]; rfl
  have hK : (D.graph.edgeSet \ (crossing D c).edgeSet).ncard ∈
      {k : ℕ | ∃ G : SimpleGraph D.Vertex, G ≤ D.graph ∧ G.IsBipartite ∧
        (D.graph.edgeSet \ G.edgeSet).ncard = k} :=
    ⟨crossing D c, fun {_ _} h => h.1, crossing_bipartite D c, rfl⟩
  apply (Nat.sInf_le hK).trans
  exact (Set.ncard_le_ncard hsub).trans (by
    rw [Set.ncard_coe_finset, ← hcard]
    exact Finset.card_image_le)

def restrict (D : Digraph) (S : Set D.Vertex) : Digraph where
  Vertex := S
  forward a b := D.forward a.1 b.1
  asymmetric := by intro _ _ h; exact D.asymmetric h

def inclusion (D : Digraph) (S : Set D.Vertex) : Hom (restrict D S) D where
  toFun x := x.1
  forward' := by intro a b h; exact h

theorem hG_of_cost {D E : Digraph} (f : Hom D E) (hf : Function.Injective f.toFun)
    (n B : ℕ) (hn : 0 < n)
    (h : ∀ T : Finset E.Vertex, T.card = n → ∃ c, badCost E T (fun _ => 1) c ≤ B) :
    Erdos111.hG D.graph n ≤ B := by
  unfold Erdos111.hG
  apply csSup_le'
  rintro k ⟨S, hS, rfl⟩
  have hfin : S.Finite := Set.finite_of_ncard_ne_zero (hS.symm ▸ hn.ne')
  letI : Fintype (restrict D S).Vertex := hfin.fintype
  let g : Hom (restrict D S) E :=
    ⟨f.toFun ∘ (inclusion D S).toFun, fun {_ _} ha => f.forward' ha⟩
  have hg : Function.Injective g.toFun := hf.comp Subtype.val_injective
  have hT : (Finset.univ.image g.toFun).card = n := by
    rw [Finset.card_image_of_injective _ hg, Finset.card_univ]
    change @Fintype.card S hfin.fintype = n
    exact (@Nat.card_eq_fintype_card S hfin.fintype).symm.trans hS
  obtain ⟨c, hc⟩ := h _ hT
  exact (distance_le_cost (restrict D S) (c ∘ g.toFun)).trans
    ((badCost_transfer g hg Finset.univ c).trans hc)

theorem hG_iterate {D E : Digraph} (r : ℕ) (f : Hom E (D.iterate r))
    (hf : Function.Injective f.toFun) (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (hle : n ≤ m ^ (r + 1)) :
    Erdos111.hG E.graph n ≤ boundConstant r * n * m := by
  apply hG_of_cost f hf n _ hn
  intro S hS
  have hsum : (∑ _x ∈ S, (1 : ℕ)) = n := by simp [hS]
  simpa only [hsum] using
    weighted_iterate D r S (fun _ => 1) 1 m (by decide) hm (by simp)
      (by simpa only [hsum, one_mul] using hle)

theorem hG_isBigO {D E : Digraph} (r : ℕ) (f : Hom E (D.iterate r))
    (hf : Function.Injective f.toFun) {ε : ℝ} (hε : ((r + 1 : ℕ) : ℝ)⁻¹ ≤ ε) :
    (fun n : ℕ => (Erdos111.hG E.graph n : ℝ)) =O[Filter.atTop]
      (fun n => (n : ℝ) ^ (1 + ε)) := by
  apply Asymptotics.IsBigO.of_bound (2 * (boundConstant r : ℝ))
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  let z := (n : ℝ) ^ ((r + 1 : ℕ) : ℝ)⁻¹
  let m := ⌈z⌉₊
  have hnR : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hr : 0 < ((r + 1 : ℕ) : ℝ) := by positivity
  have hz : 1 ≤ z := Real.one_le_rpow hnR (by positivity)
  have hzm : z ≤ (m : ℝ) := Nat.le_ceil z
  have hm : 0 < m := Nat.ceil_pos.mpr (by linarith)
  have hzpow : z ^ (r + 1) = (n : ℝ) := by
    dsimp [z]
    rw [← Real.rpow_mul_natCast (by positivity), inv_mul_cancel₀ hr.ne', Real.rpow_one]
  have hnpow : n ≤ m ^ (r + 1) := by
    exact_mod_cast (calc
      (n : ℝ) = z ^ (r + 1) := hzpow.symm
      _ ≤ (m : ℝ) ^ (r + 1) := pow_le_pow_left₀ (by linarith) hzm _)
  have hupper : (m : ℝ) ≤ 2 * z := by
    have ht := Nat.ceil_lt_add_one (show 0 ≤ z by linarith)
    change (m : ℝ) < z + 1 at ht
    linarith
  have hfinite := hG_iterate r f hf n m (by omega) hm hnpow
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (boundConstant r : ℝ) * n * (m : ℝ) := by exact_mod_cast hfinite
    _ ≤ (boundConstant r : ℝ) * n * (2 * z) := mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = (2 * (boundConstant r : ℝ)) * ((n : ℝ) * z) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [Real.rpow_add (by positivity), Real.rpow_one]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hnR hε) (by positivity)

end
end Digraph
end Erdos111Shift

open Erdos111Shift Erdos111Shift.Digraph

theorem OMA.solution : type_of% @Erdos111.erdos_111.variants.erdos_conjecture := by
  intro ε hε
  obtain ⟨r, hr⟩ := exists_nat_gt ε⁻¹
  have he : ((r + 1 : ℕ) : ℝ)⁻¹ ≤ ε := by
    apply (inv_le_comm₀ (by positivity) hε).mpr
    exact hr.le.trans (by exact_mod_cast Nat.le_succ r)
  let α := Set (Palette r)
  let O : LinearOrder α := IsWellOrder.linearOrder (WellOrderingRel : α → α → Prop)
  letI : LinearOrder α := O
  have hWell : @WellFoundedLT α O.toLT :=
    ⟨show WellFounded (WellOrderingRel : α → α → Prop) from IsWellFounded.wf⟩
  let D := (order α).iterate r
  let rise := orderRises α r
  let G := historyGraph rise
  let f : Hom G ((decorated D (orderLevel α r)).iterate r) :=
    ⟨decorateNode r, fun {_ _} h => decorateNode_forward r h⟩
  refine ⟨G.Vertex, G.graph, @chromatic_history α O D (orderLevel α r) rise hWell
    (no_natural_coloring r), ?_⟩
  exact hG_isBigO r f (decorateNode_injective r) he
