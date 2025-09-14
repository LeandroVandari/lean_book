variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun h: ∀ x, p x ∧ q x =>
      And.intro
        (fun x: α =>
          show p x from (h x).left)
        (fun x: α =>
          show q x from (h x).right))

    (fun h: (∀ x, p x) ∧ (∀ x, q x) =>
      let ⟨hpx, hpq⟩ := h
      (fun x: α =>
        show p x ∧ q x from ⟨hpx x, hpq x⟩))
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  (
    fun hp_imp_q: (∀ x, p x → q x) =>
      (fun hpx: (∀ x, p x) =>
        (fun x =>
        suffices hpx: p x from (hp_imp_q x) hpx
        show p x from hpx x))
  )
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  (
    fun hporq: (∀ x, p x) ∨ (∀ x, q x) =>
      Or.elim hporq
        (fun hpx: ∀ x, p x =>
          (fun x: α => Or.inl (hpx x)))
        (fun hqx: ∀ x, q x =>
          (fun x: α => Or.inr (hqx x)))
  )


