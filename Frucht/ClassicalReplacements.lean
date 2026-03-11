import Mathlib
import Frucht.Classical

noncomputable section

universe u v w

open Setoid Function

attribute [restrict Classical.choice 2] Classical.uniqueChoice

@[classical, replace Classical.propDecidable]
def propDecidable' (a : Prop) : Decidable a :=
  Classical.uniqueChoice
    (match em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩)
    inferInstance

@[classical, restrict Classical.indefiniteDescription 3]
def definiteDescription
    {α} {p : α → Prop} (h : ∃ x, p x) (h' : ∀ {x y}, p x → p y → x = y) : {x // p x} :=
  Classical.uniqueChoice
    (let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩)
    ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => by simp; exact h' hx hy⟩

@[classical, restrict Classical.choose 3]
def Exists.chooseUnique
    {α} {p : α → Prop} (ex : ∃ a, p a) (unique : ∀ {x y}, p x → p y → x = y) :=
  (definiteDescription ex unique).val

@[classical, restrict Classical.choose_spec 3]
lemma Exists.chooseUnique_spec
    {α} {p : α → Prop} (ex : ∃ a, p a) (unique : ∀ {x y}, p x → p y → x = y) :
    p (ex.chooseUnique unique) :=
  (definiteDescription ex unique).property

namespace Equiv

@[classical, replace ofBijective]
def ofBijective' {α β} (f : α → β) (hf : Bijective f) : α ≃ β where
  toFun := f
  invFun := fun b =>
    (show ∃ a, f a = b by apply hf.surjective).chooseUnique
    (fun {x y} hx hy => by rw [← hy] at hx; exact hf.injective hx)
  left_inv := by
    intro x
    simp only
    generalize_proofs h h'
    exact hf.injective (h.chooseUnique_spec h')
  right_inv := by
    intro x
    simp only
    generalize_proofs h h'
    exact h.chooseUnique_spec h'

@[classical, replace ofInjective]
def ofInjective' {α β} (f : α → β) (hf : Injective f) : α ≃ Set.range f :=
  ofBijective' (fun x => ⟨f x, by simp⟩) (by
    constructor
    · intro x y eq
      simp only [Subtype.mk.injEq] at eq
      simpa using hf eq
    · intro x
      obtain ⟨y, hy⟩ := x.2
      simpa [Subtype.ext_iff] using ⟨y, hy⟩)

@[classical, replace punitOfNonemptyOfSubsingleton]
def punitOfNonemptyOfSubsingleton' {α} [h : Nonempty α] [Subsingleton α] :
    α ≃ PUnit.{v} := by
  elim_choice Equiv.punitOfNonemptyOfSubsingleton.{u, v} (α := α) unfolding Nonempty.some
  infer_instance

end Equiv

namespace List

@[classical, replace pairwise_lt_range']
lemma pairwise_lt_range'' {s n} (step := 1) (pos : 0 < step := by simp) :
    List.Pairwise (· < ·) (range' s n step) := by
  elim_choice pairwise_lt_range' (s := s) (n := n) step pos
    unfolding Exists.choose Exists.choose_spec
  omega

end List

namespace WellFounded

variable {α} {r : α → α → Prop} [wo : IsWellOrder α r]
    (H : WellFounded r) (s : Set α) (h : s.Nonempty)

@[classical] lemma min_aux
    {x y : α} (hx : x ∈ s ∧ ∀ x_1 ∈ s, ¬r x_1 x) (hy : y ∈ s ∧ ∀ x ∈ s, ¬r x y) : x = y := by
  have := hx.2 y hy.1
  have := hy.2 x hx.1
  have := trichotomous (r := r) x y
  tauto

@[classical, restrict WellFounded.min 2]
def min' : α := by
  elim_choice H.min s h
  apply WellFounded.min_aux

@[classical, restrict min_mem 2]
lemma min_mem' : H.min' s h ∈ s := by
  elim_choice H.min_mem s h <;>
    (first | apply WellFounded.min_aux | infer_instance)

@[classical, restrict not_lt_min 2]
lemma not_lt_min' {x} (hx : x ∈ s) : ¬r x (H.min' s h) := by
  elim_choice H.not_lt_min s h hx unfolding WellFounded.min_mem <;>
    (first | apply WellFounded.min_aux | infer_instance)

end WellFounded

namespace CompletelyDistribLattice

@[classical, restrict toCompleteLattice -1 1]
instance toCompleteLattice' {α} [self : CompleteLattice α] :
    CompleteLattice α := self

@[classical, restrict toCompleteDistribLattice -1 1]
instance toCompleteDistribLattice' {α} [self : CompleteDistribLattice α] :
    CompleteDistribLattice α := self

end CompletelyDistribLattice

namespace Fintype

@[classical, replace Fintype.finite]
theorem finite' {α} (_inst : Fintype α) : Finite α := by
  letI := Classical.decEq α
  obtain ⟨e⟩ := truncEquivFin α
  exact ⟨e⟩

@[classical] theorem equivOfCardEq' {α β} [Fintype α] [Fintype β] (h : card α = card β) :
    Nonempty (α ≃ β) := by
  letI := Classical.decEq α
  letI := Classical.decEq β
  obtain ⟨e⟩ := truncEquivOfCardEq h
  exact ⟨e⟩

end Fintype

attribute [-instance] CompleteLinearOrder.toCompletelyDistribLattice

namespace CompleteLinearOrder

@[classical] instance toCompleteDistribLattice
    {α} [h : CompleteLinearOrder α] : CompleteDistribLattice α := {
    __ := ‹CompleteLinearOrder α›
}

@[classical, replace toConditionallyCompleteLinearOrderBot]
instance toConditionallyCompleteLinearOrderBot'
    {α} [h : CompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot α := by
  elim_choice toConditionallyCompleteLinearOrderBot (α := α) <;> infer_instance

end CompleteLinearOrder

attribute [-instance] Set.instCompleteAtomicBooleanAlgebra

namespace CompleteAtomicBooleanAlgebra

@[classical, restrict toCompleteBooleanAlgebra -1 1]
instance toCompleteBooleanAlgebra' {α} [self : CompleteBooleanAlgebra α] :
    CompleteBooleanAlgebra α := self

end CompleteAtomicBooleanAlgebra

@[classical] instance Set.instCompleteBooleanAlgebra {α} : CompleteBooleanAlgebra (Set α) :=
  { Set.instBooleanAlgebra with
    le_sSup := fun _ t t_in _ a_in => ⟨t, t_in, a_in⟩
    sSup_le := fun _ _ h _ ⟨t', ⟨t'_in, a_in⟩⟩ => h t' t'_in a_in
    le_sInf := fun _ _ h _ a_in t' t'_in => h t' t'_in a_in
    sInf_le := fun _ _ t_in _ h => h _ t_in }

namespace Function

open Classical

@[classical, restrict invFun -2 2 4]
def invFun' {α β : Sort*} [Inhabited α] (f : α → β) (hf : Injective f) : β → α :=
  fun b => if h : ∃ x, f x = b then h.chooseUnique (fun h h' => hf (h' ▸ h)) else default

@[classical, restrict leftInverse_invFun -2 2]
lemma leftInverse_invFun' {α β : Sort*} [Inhabited α] {f : α → β}
    (hf : Injective f) : LeftInverse (invFun' f hf) f := by
  intro x
  simp only [invFun', exists_apply_eq_apply, ↓reduceDIte]
  generalize_proofs h h'
  exact hf (h.chooseUnique_spec h')

@[classical, restrict invFun_eq -2 2 5]
lemma invFun_eq' {α β : Sort*} [Inhabited α] {f : α → β} {b : β}
    (hf : Injective f) (hb : ∃ a, f a = b) : f (invFun' f hf b) = b := by
  simp only [invFun', hb, ↓reduceDIte]
  obtain ⟨a, ha⟩ := hb
  generalize_proofs hb eq
  rw [hb.chooseUnique_spec eq]

@[classical, replace Embedding.setValue]
def Embedding.setValue' {α β : Sort*} (f : α ↪ β) (a : α) (b : β)
    [∀ a', Decidable (a' = a)] [∀ a', Decidable (f a' = b)] : α ↪ β :=
  ⟨fun a' => if a' = a then b else if f a' = b then f a else f a', by
    intro x y h
    simp only at h
    split_ifs at h <;> try simp_all
    · rename_i h₁ h₂ h₃
      rw [← h, f.apply_eq_iff_eq] at h₂
      exact h₁ h₂
    · rename_i h₁ h₂ h₃
      rwa [← h₃, f.apply_eq_iff_eq] at h₁⟩

@[classical, replace Embedding.setValue_eq]
def Embedding.setValue_eq' {α β : Sort*} (f : α ↪ β) (a : α) (b : β)
    [∀ a', Decidable (a' = a)] [∀ a', Decidable (f a' = b)] : (f.setValue' a b) a = b := by
  simp [setValue']

@[classical, replace Embedding.schroeder_bernstein_of_rel]
theorem Embedding.schroeder_bernstein_of_rel'
    {α β : Type*} {f : α → β} {g : β → α} (hf : Function.Injective f)
    (hg : Function.Injective g) (R : α → β → Prop) (hp₁ : ∀ a : α, R a (f a))
    (hp₂ : ∀ b : β, R (g b) b) :
    ∃ h : α → β, Bijective h ∧ ∀ a : α, R a (h a) := by
  by_cases em : IsEmpty β
  · have : IsEmpty α := f.isEmpty
    exact ⟨_, ((Equiv.equivEmpty α).trans (Equiv.equivEmpty β).symm).bijective, by simp⟩
  · simp only [not_isEmpty_iff] at em
    cases' em with x
    letI : Inhabited β := ⟨x⟩
    elim_choice Embedding.schroeder_bernstein_of_rel hf hg R hp₁ hp₂ <;>
      first | infer_instance | assumption

end Function

namespace Cardinal

@[classical, replace mk_union_of_disjoint]
lemma mk_union_of_disjoint' {α} {S T : Set α} (H : Disjoint S T) : #(S ∪ T : Set α) = #S + #T := by
  elim_choice mk_union_of_disjoint H

@[classical, replace nonempty_unique]
lemma nonempty_unique' {α} [hα : Subsingleton α] [ne : Nonempty α] : Nonempty (Unique α) := by
  obtain ⟨x⟩ := ne
  refine ⟨⟨⟨x⟩, fun y => hα.elim y x⟩⟩

@[classical, replace mk_insert]
theorem mk_insert' {α} {s : Set α} {a : α} (h : a ∉ s) : #(insert a s : Set α) = #s + 1 := by
  elim_choice mk_insert h; infer_instance

open Fintype in
@[classical, replace mk_fintype]
theorem mk_fintype' (α : Type u) [h : Fintype α] : #α = Fintype.card α := by
  obtain ⟨e⟩ := equivOfCardEq' (show card α = card (ULift.{u, 0} (Fin (Fintype.card α))) by simp)
  exact mk_congr e

end Cardinal

@[classical, replace quotientKerEquivOfSurjective]
def quotientKerEquivOfSurjective' {α β} (f : α → β) (hf : Surjective f) :
    Quotient (ker f) ≃ β :=
  (Setoid.quotientKerEquivRange f).trans (Surjective.range_eq hf ▸ Equiv.Set.univ _)

@[classical, replace small_subtype]
def small_subtype' (α) [hα : Small.{u} α] (P : α → Prop) : Small.{u} { x // P x } := by
  obtain ⟨S, ⟨e⟩⟩ := hα
  exact ⟨_, ⟨Equiv.subtypeEquivOfSubtype e.symm (p := P) |>.symm⟩⟩

@[classical, replace small_of_surjective]
theorem small_of_surjective' {α β} [hα : Small.{u} α] {f : α → β} (hf : Surjective f) :
    Small.{u} β := by
  obtain ⟨S, ⟨e⟩⟩ := hα
  refine ⟨_, ⟨quotientKerEquivOfSurjective' (f ∘ e.symm) ?_ |>.symm⟩⟩
  simpa

@[classical, replace small_sum]
instance small_sum' {α β} [hα : Small.{w} α] [hβ : Small.{w} β] : Small.{w} (α ⊕ β) := by
  obtain ⟨S, ⟨e⟩⟩ := hα
  obtain ⟨S', ⟨e'⟩⟩ := hβ
  exact ⟨_, ⟨Equiv.sumCongr e e'⟩⟩

@[classical, replace isLeast_csInf]
theorem isLeast_csInf'
    {α} [ConditionallyCompleteLinearOrder α] {s : Set α} [WellFoundedLT α] (hs : s.Nonempty) :
    IsLeast s (sInf s) := by
  have : IsWellOrder α (InvImage (· < ·) id) := by
    simp (config := {unfoldPartialApp := true}) [InvImage]
    infer_instance
  elim_choice isLeast_csInf hs
    unfolding sInf_eq_argmin_on argminOn argminOn_mem not_lt_argminOn argminOn_le <;>
    assumption
