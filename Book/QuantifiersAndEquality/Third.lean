variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have hnsbb: ¬ shaves barber barber :=
    fun sbb: shaves barber barber => ((h barber).mp sbb) sbb
  have hsbb: shaves barber barber :=
    (h barber).mpr hnsbb

  show False from hnsbb hsbb
