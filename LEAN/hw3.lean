import data.set
open set

-- 1. Replace "sorry" in these examples.
section
  variable {U : Type}
  variables A B C : set U

  example : ∀ x, x ∈ A ∩ C → x ∈ A ∪ B :=
  assume a,
  assume h1 : a ∈ A ∩ C,

  show a ∈ A ∪ B, from or.inl (and.left h1)

  example : ∀ x, x ∈ (A ∪ B)ᶜ → x ∈ Aᶜ :=
  
  assume a,
  assume h1 : a ∈ (A ∪ B)ᶜ,

  show ¬ (a ∈ A), from 
      (
      assume h2 : a ∈ A,
      have h3 : a ∈ A ∪ B, from or.inl h2,
      show false, from h1 h3
      )
end

-- 2. Replace "sorry" in the last example.
section
  variable {U : Type}

  /- defining "disjoint" -/
  def disj (A B : set U) : Prop := ∀ ⦃x⦄, x ∈ A → x ∈ B → false

  example (A B : set U) (h : ∀ x, ¬ (x ∈ A ∧ x ∈ B)) : disj A B :=
  assume x,
  assume h1 : x ∈ A,
  assume h2 : x ∈ B,
  have h3 : x ∈ A ∧ x ∈ B, from and.intro h1 h2,
  show false, from h x h3

  -- notice that we do not have to mention x when applying
  --   h : disj A B
  example (A B : set U) (h1 : disj A B) (x : U) (h2 : x ∈ A) (h3 : x ∈ B) : false :=
  h1 h2 h3

  -- the same is true of ⊆
  example (A B : set U) (x : U) (h : A ⊆ B) (h1 : x ∈ A) : x ∈ B :=
  h h1

  example (A B C D : set U) (h1 : disj A B) (h2 : C ⊆ A) (h3 : D ⊆ B) : disj C D :=
  assume a,
  assume e1 : a ∈ C,
  assume e2 : a ∈ D,

  have e3 : a ∈ A, from h2 e1,
  have e4 : a ∈ B, from h3 e2,

  show false, from h1 e3 e4
end

-- 3. Prove the following facts about indexed unions and
-- intersections, using the theorems Inter.intro, Inter.elim,
-- Union.intro, and Union.elim listed above.
section
  variables {I U : Type}
  variables {A : I → set U} {B : I → set U} {C : set U}

  theorem Inter.intro {x : U} (h : ∀ i, x ∈ A i) : x ∈ ⋂ i, A i :=
  by simp; assumption

  @[elab_simple]
  theorem Inter.elim {x : U} (h : x ∈ ⋂ i, A i) (i : I) : x ∈ A i :=
  by simp at h; apply h

  theorem Union.intro {x : U} (i : I) (h : x ∈ A i) : x ∈ ⋃ i, A i :=
  by {simp, existsi i, exact h}

  theorem Union.elim {b : Prop} {x : U}
  (h₁ : x ∈ ⋃ i, A i) (h₂ : ∀ (i : I), x ∈ A i → b) : b :=
  by {simp at h₁, cases h₁ with i h, exact h₂ i h}

  example : (⋂ i, A i) ∩ (⋂ i, B i) ⊆ (⋂ i, A i ∩ B i) :=

  assume a,

  assume h1 : a ∈ ((⋂ i, A i) ∩ (⋂ i, B i)),
  

  show a ∈ (⋂ i, A i ∩ B i), from Inter.intro 
    (
      assume i : I,

      have h2 : a ∈ (⋂ i, B i), from and.right h1,
      have h3 : a ∈ (⋂ i, A i), from and.left h1,

      have h4 : a ∈ (B i), from Inter.elim h2 i,
      have h5 : a ∈ (A i), from Inter.elim h3 i,

      show a ∈ (A i ∩ B i), from and.intro h5 h4
    )

  example : C ∩ (⋃i, A i) ⊆ ⋃i, C ∩ A i :=

  assume a,
  assume h1 : a ∈ C ∩ (⋃i, A i),

  have h2 : a ∈ (⋃i, A i), from and.right h1,
  have h3 : a ∈ C, from and.left h1,

  Union.elim h2 
  (
    assume i : I,
    assume temp1 : a ∈ A i,
    have temp2 : a ∈ C ∩ A i, from and.intro h3 temp1,
    show a ∈ ⋃i, C ∩ A i, from Union.intro i temp2
  )
end

-- 4. Prove the following fact about power sets. You can use the
-- theorems subset.trans and subset.refl
section
  variable  {U : Type}
  variables A B C : set U

  -- For this exercise these two facts are useful
  example (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C :=
  subset.trans h1 h2

  example : A ⊆ A :=
  subset.refl A

  example (h : A ⊆ B) : powerset A ⊆ powerset B :=
  assume a,
  assume h1 : a ∈ powerset A,

  show a ∈ powerset B, from subset.trans h1 h

  example (h : powerset A ⊆ powerset B) : A ⊆ B :=
  
  show A ⊆ B, from h (subset.refl A)
end

-- 5. Replace the sorry commands in the following proofs to show that
-- we can create a partial order R'​ out of a strict partial order R.
section
  parameters {A : Type} {R : A → A → Prop}
  parameter (irreflR : irreflexive R)
  parameter (transR : transitive R)

  def R' (a b : A) : Prop := R a b ∨ a = b

  theorem reflR' (a : A) : R' a a :=
  have h1: a = a, from rfl,
  or.inr h1 

  theorem transR' {a b c : A} (h1 : R' a b) (h2 : R' b c): R' a c :=

  or.elim h1
  (
    assume temp1 : R a b, 

    or.elim h2
     (
      assume temp2 : R b c,
        have temp3 : R a c, from transR temp1 temp2,
        show R' a c, from or.inl temp3
     )

     (
      assume temp2 : b = c,
        show R' a c, from eq.subst temp2 h1
     )

  )
  (
    assume temp1 : a = b,
      have temp2 : b = a, from symm temp1,
      show R' a c, from eq.subst temp2 h2
  )

  theorem antisymmR' {a b : A} (h1 : R' a b) (h2 : R' b a) : a = b :=

  or.elim h1
  (
    assume temp1 : R a b,

    or.elim h2
      (
        assume temp2 : R b a,
          have temp3 : R a a, from transR temp1 temp2,
          show a = b, from false.elim (irreflR a temp3)
      )
      (
        assume temp2 : b = a,
          show a = b, from symm temp2
      )
  )
  (
    assume temp1 : a = b,
      show a = b, from temp1
  )
end

-- 6
section
  parameters {A : Type} {R : A → A → Prop}
  parameter (reflR : reflexive R)
  parameter (transR : transitive R)

  def S (a b : A) : Prop := R a b ∧ R b a

  example : transitive S :=
  
  assume x y z : A,
  assume a1 : S x y,
  assume a2 : S y z,

  have h1 : R x z, from transR a1.left a2.left,
  have h2 : R z x, from transR a2.right a1.right,

  show S x z, from ⟨h1, h2⟩
end

-- 7. Only one of the following two theorems is provable. Figure out
-- which one is true, and replace the sorry command with a complete
-- proof.
section
  parameters {A : Type} {a b c : A} {R : A → A → Prop}
  parameter (Rab : R a b)
  parameter (Rbc : R b c)
  parameter (nRac : ¬ R a c)

  theorem R_is_strict_partial_order : irreflexive R ∧ transitive R :=
  sorry

  theorem R_is_not_strict_partial_order : ¬(irreflexive R ∧ transitive R) :=
  assume h1 : irreflexive R ∧ transitive R,

  show false, from nRac (h1.right Rab Rbc)
end

-- 8
section
  open nat

  example : 1 ≤ 4 :=

  have h1 : 1 ≤ 2, from nat.le_succ 1,
  have h2 : 2 ≤ 3, from nat.le_succ 2,

  have h3 : 1 ≤ 3, from nat.le_trans h1 h2,
  have h4 : 3 ≤ 4, from nat.le_succ 3,

  show 1 ≤ 4, from nat.le_trans h3 h4
end
