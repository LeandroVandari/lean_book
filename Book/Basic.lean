variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h: p ∧ q =>
      show q ∧ p from ⟨ h.right, h.left ⟩)
    (fun h: q∧ p =>
      show p ∧ q from ⟨ h.right, h.left⟩ )


example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h: p ∨ q =>
      Or.elim h
        (fun h₁: p => Or.inr h₁)
        (fun h₁: q => Or.inl h₁))
    (fun h: q ∨ p =>
      Or.elim h
        (fun h₁: q => Or.inr h₁)
        (fun h₁: p => Or.inl h₁) )

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h: (p ∧ q) ∧ r =>
      show p ∧ (q ∧ r) from ⟨ h.left.left, ⟨ h.left.right, h.right⟩ ⟩ )
    (fun h: p ∧ (q ∧ r) =>
      show (p ∧ q) ∧ r from ⟨ ⟨ h.left, h.right.left⟩, h.right.right⟩  )

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h: (p ∨ q) ∨ r =>
      Or.elim h
        (fun h₁: p ∨ q =>
          Or.elim h₁
            (fun h₂: p =>
              Or.inl h₂)
            (fun h₂: q =>
              Or.inr (Or.inl h₂)))
        (fun h₁: r =>
          Or.inr (Or.inr h₁)))

    (fun h: p ∨ (q ∨ r) =>
      Or.elim h
        (fun h₁: p =>
          Or.inl (Or.inl h₁))
        (fun h₁: q ∨ r =>
          Or.elim h₁
            (fun h₂: q =>
              Or.inl (Or.inr h₂))
            (fun h₂: r =>
              Or.inr h₂)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h: p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim h.right
        (fun h₁: q =>
          Or.inl (And.intro hp h₁))
        (fun h₁: r =>
          Or.inr (And.intro hp h₁))
      )

    (fun h: (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun h₁: p ∧ q =>
          And.intro h₁.left (Or.inl h₁.right))
        (fun h₁: p ∧ r =>
          And.intro h₁.left (Or.inr h₁.right))
    )
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun h: p ∨ (q ∧ r) =>
      Or.elim h
        (fun h₁: p =>
          ⟨Or.inl h₁, Or.inl h₁⟩)
        (fun h₁: q ∧ r =>
          ⟨Or.inr h₁.left, Or.inr h₁.right⟩ ))

    (fun h: (p ∨ q) ∧ (p ∨ r) =>
      have hpq: p ∨ q := h.left
      have hpr: p ∨ r := h.right

      Or.elim hpq
        (fun h₁: p => Or.inl h₁)
        (fun h₁: q =>
          Or.elim hpr
            (fun h₂: p => Or.inl h₂)
            (fun h₂: r => Or.inr (And.intro h₁ h₂))))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h: p → (q → r) =>
      (fun hpq: p ∧ q =>
        show r from h hpq.left hpq.right))
    (fun h: p ∧ q → r =>
      (fun hp: p =>
        fun hq: q =>
          show r from h ⟨hp, hq⟩ ))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun h: (p ∨ q) → r =>
      And.intro
        (fun hp: p =>
          h (Or.inl hp))
        (fun hq: q =>
          h (Or.inr hq)))

    (fun h: (p → r) ∧ (q → r) =>
      (fun hpq: p ∨ q =>
        Or.elim hpq
          (fun hp: p =>
            h.left hp)
          (fun hq: q =>
            h.right hq)))


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h: ¬(p ∨ q) =>
      have hnp: ¬p :=
        (fun hp: p =>
          absurd (Or.inl hp) h)
      have hnq: ¬q :=
        (fun hq: q =>
          absurd (Or.inr hq) h)
      show ¬p ∧ ¬ q from And.intro hnp hnq)

    (fun h: ¬p ∧ ¬q =>
      (fun h₁: p ∨ q =>
        Or.elim h₁
          (fun hp: p =>
            absurd hp h.left)
          (fun hq: q =>
            absurd hq h.right)))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  (fun h: ¬p ∨ ¬q =>
    fun hpq: p ∧ q =>
      Or.elim h
        (fun hnp: ¬p =>
          absurd hpq.left hnp)
        (fun hnq: ¬q =>
          absurd hpq.right hnq) )

example : ¬(p ∧ ¬p) :=
  (fun h: p ∧ ¬p =>
    absurd h.left h.right)

example : p ∧ ¬q → ¬(p → q) :=
  (fun h: p ∧ ¬q =>
    fun hpiq: p → q =>
      absurd (hpiq h.left) h.right)

example : ¬p → (p → q) :=
  (fun h: ¬p =>
    (fun hp: p =>
      absurd hp h))

example : (¬p ∨ q) → (p → q) :=
  (fun h: ¬p ∨ q =>
    Or.elim h
      (fun hnp: ¬p =>
        fun hp: p =>
          absurd hp hnp)
      (fun hq: q =>
        fun _: p =>
          show q from hq))


example : p ∨ False ↔ p :=
  Iff.intro
    (fun h: p ∨ False =>
      Or.elim h
        (fun hp: p =>
          hp)
        (fun hf: False =>
          False.elim hf))
    (fun h: p =>
      Or.inl h)

example : p ∧ False ↔ False :=
  Iff.intro
    (fun h: p ∧ False => h.right.elim)
    (fun h: False =>
      h.elim)

example : (p → q) → (¬q → ¬p) :=
  (fun h: p → q =>
    (fun hnq: ¬q =>
      (fun hp: p =>
        absurd (h hp) hnq)))
