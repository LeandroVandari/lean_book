open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _x : α, r) → r :=
  (fun hxr: ∃_x, r =>
    Exists.elim hxr
      (fun _x =>
        (fun hr: r => hr)))

example (a : α) : r → (∃ _x : α, r) :=
  (fun hr: r =>
    Exists.intro a hr)

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun hx: (∃x, p x ∧ r) =>
      Exists.elim hx
        (fun x =>
          (fun hpxr: p x ∧ r =>
            And.intro
              ⟨x, hpxr.left⟩
              hpxr.right)))

    (fun hx: (∃x, p x) ∧ r =>
      hx.left.elim
        (fun x =>
          fun hpx: p x =>
            ⟨x, hpx, hx.right⟩))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun hxpq: (∃x, p x ∨ q x) =>
      hxpq.elim
        (fun x =>
          fun hpq: p x ∨ q x =>
            hpq.elim
              (fun hp: p x =>
                Or.inl ⟨x, hp⟩)
              (fun hq: q x =>
                Or.inr ⟨x, hq⟩)))

    (fun hpq: (∃x, p x) ∨ (∃x, q x) =>
      hpq.elim
        (fun hp: (∃x, p x) =>
          hp.elim
            (fun x =>
              (fun hpx: p x =>
                ⟨x, Or.inl hpx⟩)))
        (fun hq: (∃x, q x) =>
          hq.elim
            (fun x =>
              (fun hqx: q x =>
                ⟨x, Or.inr hqx⟩))))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (fun h: (∀ x, p x) =>
      (fun ⟨x, hpnx⟩ => hpnx (h x)) )
    (fun h: ¬(∃x, ¬p x) =>
      (fun x => Or.elim (em (p x))
        (fun hpx: p x => hpx)
        (fun hpnx: ¬p x => absurd ⟨x, hpnx⟩ h)))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (fun ⟨x, hpx⟩ =>
      (fun hnp: ∀ x, ¬p x =>
        (hnp x) hpx) )
    (fun hnxnpx: ¬(∀ x, ¬ p x) =>
      Or.elim (em (∃x, p x))
        (fun true => true)
        (fun hnxpx: ¬∃x, p x =>
          have haxnpx: ∀x, ¬ p x := (fun x => fun hpx => absurd ⟨x, hpx⟩ hnxpx)
          absurd haxnpx hnxnpx))
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (fun hnpx: ¬∃x, p x =>
      fun x =>
        fun hpx: p x =>
          hnpx ⟨x, hpx⟩)
    (fun hnpx: ∀x, ¬ p x =>
      fun ⟨x, hpx⟩ =>
        (hnpx x) hpx)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (fun hnapx: ¬∀ x, p x =>
      Or.elim (em (∃x, ¬p x))
        (fun hex => hex)
        (fun hnex: ¬∃x, ¬ p x =>
          have hapx: ∀x, p x :=
            (fun x =>
              Or.elim (em (p x))
                (fun hpx: p x => hpx)
                (fun hnpx: ¬p x =>
                  absurd ⟨x, hnpx⟩ hnex))
          absurd hapx hnapx
          ))
    (fun ⟨x, hnpx⟩ =>
      fun haxpx: ∀x, p x => absurd (haxpx x) hnpx
      )

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (λhaxpxr: ∀x, p x → r =>
      λ ⟨x, hpx⟩ => (haxpxr x) hpx)
    (λ hexpxr: (∃x, p x) → r =>
      (λ x =>
        (λ hpx: p x =>
          hexpxr (⟨x, hpx⟩))))

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (λ ⟨x, hpxr⟩ =>
      λhaxpx: ∀x, p x =>
        hpxr (haxpx x))
    (λhaxpxr: (∀x, p x) → r =>
      byCases
        (λhap: ∀x, p x => ⟨a, λ _ => haxpxr hap⟩)
        (λhnap: ¬∀x, p x =>
          byContradiction
            (λhnex: ¬∃ x, p x → r =>
              have hap: ∀x, p x :=
                (λ x =>
                  byContradiction
                    (λhnp: ¬p x =>
                      have hex: ∃x, p x → r := ⟨x, λhpx => absurd hpx hnp⟩
                      absurd hex hnex))
              show False from hnap hap))
    )
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (λ⟨x, hx⟩ =>
      λhr: r =>
        ⟨x, hx hr⟩)
    (λh1: r → ∃ x, p x =>
      byCases
        (λhr: r =>
          Exists.elim (h1 hr)
            (λx =>
              λhpx: p x =>
                ⟨x, λ_ => hpx⟩))
        (λhnr: ¬r =>
          ⟨a, λhr: r => absurd hr hnr⟩ ))
