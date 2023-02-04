variables A B C D : Prop

section 
  example : A ∧ (A → B) → B :=
    assume h: A ∧ (A → B),
    have h1: A → B, from and.elim_right h,
    have h2: A, from and.elim_left h,
    show B, from h1 h2
end

section
example : A → ¬(¬A ∧ B) :=
  assume h1: A,
  assume h2: ¬A ∧B,
  show false, from (and.left h2) h1
end

section 
  example : ¬(A ∧ B) → (A → ¬B) :=
    assume ha: ¬(A ∧ B),
    assume hb: A,
    assume hc: B,
    show false, from (ha (and.intro hb hc))
end

section
  example (h1 : A ∨ B) (h2 : A → C) (h3 : B → D) : C ∨ D :=

  or.elim h1
  (
    assume ha: A,
    have hb: C, from h2 ha,
    have hc: C ∨ D, from or.inl hb,
    show C ∨ D, from hc
  )

  (
    assume hd: B,
    have he: D, from h3 hd,
    have hf: C ∨ D, from or.inr he,
    show C ∨ D, from hf 
  )
end

section
  example (h : ¬A ∧ ¬B) : ¬(A ∨ B) :=

    assume h1: A ∨ B,

    show false, from or.elim h1
      (
      assume h3: A,
      have h4: ¬A, from and.elim_left h,
      show false, from h4 h3
      )

      (
      assume h3: B,
      have h4: ¬B, from and.elim_right h,
      show false, from h4 h3
      )
end

section
example : ¬(A ↔ ¬A) :=
  assume ha: (A ↔ (A → false)),

  have h1: A → (A → false), from iff.elim_left ha,
  have h2: (A → false) → A, from iff.elim_right ha,
  have hc: (A → false), from (assume hb: A, ((h1 hb) hb)),
  have hd: A, from h2 hc,  
  show false, from (h1 hd) hd
end
