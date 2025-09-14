variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ _x : α, r) ↔ r) :=
  (
    fun ha: α =>
      Iff.intro
        (fun hx: (∀ _x : α, r) =>
          hx ha)
        (fun hr: r =>
          (fun _x: α => hr))
  )
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (fun hpxr: (∀ x, p x ∨ r) =>
      Or.elim (Classical.em r)
        (fun hr: r => Or.inr hr)
        (fun hnr: ¬r =>
          Or.inl (
            fun x =>
              Or.elim (hpxr x)
                (fun hpx: p x => hpx)
                (fun hr: r => absurd hr hnr)
          ))
    )
    (fun hpxr: (∀ x, p x) ∨ r =>
      Or.elim hpxr
        (fun hpx: (∀ x, p x) =>
          (fun x => Or.inl (hpx x)))
        (fun hr: r =>
          fun _ => Or.inr hr))

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun hrpx: (∀ x, r → p x) =>
      (fun hr: r =>
        fun x => hrpx x hr))

    (fun hrpx: (r → ∀ x, p x) =>
      (fun x =>
        (fun hr: r =>
          hrpx hr x)))
