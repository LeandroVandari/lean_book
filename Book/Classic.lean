open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  (fun h: p → q ∨ r =>
    byCases
      (fun hq: q =>
        Or.inl (fun _ => hq)
      )
      (fun hnq: ¬q =>
        Or.inr (fun hp: p =>
          Or.elim (h hp)
            (fun hq: q => absurd hq hnq)
            (fun hr: r => hr)))
  )

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  (fun h: ¬(p ∧ q) =>
    Or.elim (em q)
      (fun hq: q =>
        Or.elim (em p)
          (fun hp: p =>
            absurd (⟨hp, hq⟩) h)
          (fun hnp: ¬p =>
            Or.inl hnp))
      (fun hnq: ¬q =>
        Or.inr hnq)
  )
example : ¬(p → q) → p ∧ ¬q :=
  (fun h: ¬(p → q) =>
    byCases
      (fun hq: q =>
        absurd (fun _ => hq) h)
      (fun hnq: ¬q =>
        suffices hp: p from ⟨hp, hnq⟩
        show p from
          byCases
            (fun hp: p => hp)
            (fun hnp: ¬p =>
              False.elim (h (fun hp: p => False.elim (hnp hp)))))
  )
example : (p → q) → (¬p ∨ q) :=
  (fun h: p → q =>
    byCases
      (fun hp: p =>
        Or.inr (h hp))
      (fun hnp: ¬p =>
        Or.inl hnp)
  )
example : (¬q → ¬p) → (p → q) :=
  (fun h: ¬q → ¬p =>
    byCases
      (fun hp: p =>
        Or.elim (em q)
          (fun hq: q =>
            show p → q from (fun _ => hq))
          (fun hnq: ¬q =>
            absurd hp (h hnq)))
      (fun hnp: ¬p =>
        (fun hp: p => absurd hp hnp))
  )
example : p ∨ ¬p :=
  em p

example : (((p → q) → p) → p) :=
  (
    fun hpqp: (p → q) → p => sorry
  )
