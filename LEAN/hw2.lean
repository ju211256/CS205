-- 1
section
  variable A : Type
  variable f : A → A
  variable P : A → Prop
  variable h : ∀x, P x → P (f x)

  example : ∀y, P y → P (f (f y)) :=

  assume y : A,
  assume h0: P y,
  have h1: (P y → P (f y)), from h y,
  have h2: P (f y), from h1 h0,
  have h3: P (f y) → P (f (f y)), from h (f y),
  show P (f (f y)), from h3 h2
end

-- 2
section
  variable U : Type
  variables A B : U → Prop

  example : (∀x, A x ∧ B x) → ∀x, A x :=
  assume h : (∀x, A x ∧ B x),
  assume y,
  have h1: A y ∧ B y, from h y,
  show A y, from and.left h1
end

-- 3
section
  variable U : Type
  variables A B C : U → Prop

  variable h1 : ∀x, A x ∨ B x
  variable h2 : ∀x, A x → C x
  variable h3 : ∀x, B x → C x

  example : ∀x, C x :=
  assume y : U,

  have h0: A y ∨ B y, from h1 y,

  or.elim h0
  ( 
    assume Ay,
    have ha: A y → C y, from h2 y,
    have hb: C y, from ha Ay,
    show C y, from hb
  )
  (
    assume By,
    have ha: B y → C y, from h3 y,
    have hb: C y, from ha By,
    show C y, from hb
  )
end

-- 4
open classical

axiom not_iff_not_self (P : Prop) : ¬(P ↔ ¬P)

example (Q : Prop) : ¬(Q ↔ ¬Q) :=
not_iff_not_self Q

section
  variable Person : Type
  variable shaves : Person → Person → Prop
  variable barber : Person
  variable h : ∀x, shaves barber x ↔ ¬shaves x x

  example : false :=
    not_iff_not_self
    (shaves barber barber)
    (h barber)
end

-- 5
section
  variable U : Type
  variables A B : U → Prop

  example : (∃x, A x) → ∃x, A x ∨ B x :=

  assume h1 : ∃x, A x,

  exists.elim h1
  (
    assume a (h0: A a),
    have h2: A a ∨ B a, from or.inl h0,
    show ∃x, A x ∨ B x, from exists.intro a h2
  )
end

-- 6
section
  variable U : Type
  variables A B : U → Prop

  variable h1 : ∀x, A x → B x
  variable h2 : ∃x, A x

  example : ∃x, B x :=
  
  exists.elim h2
  (
    assume y (h3: A y),
    have h0: A y → B y, from h1 y,
    have h4: B y, from h0 h3,
    show ∃x, B x, from exists.intro y h4
  )
end

-- 7
section
  variable  U : Type
  variables A B C : U → Prop

  example (h1 : ∃x, A x ∧ B x) (h2 : ∀x, B x → C x) :
      ∃x, A x ∧ C x :=

  exists.elim h1
  (
  assume a (h0 : A a ∧ B a),
  have ha : B a, from h0.right,
  have hb : B a → C a, from h2 a,
  have hc : C a, from hb ha,
  have hd : A a, from and.left h0,
  have he : A a ∧ C a, from and.intro hd hc,
  show ∃x, A x ∧ C x, from exists.intro a he
  )
end

-- 8
section
  variable  U : Type
  variables A B C : U → Prop

  example : (¬∃x, A x) → ∀x, ¬A x :=
  
  assume h1 : ¬ ∃ x, A x,

  assume y : U,
  assume h2 : A y,

  have h2 : ∃ x, A x, from exists.intro y h2,

  show false, from h1 h2
end

-- 9
section
  variable  U : Type
  variables A B C : U → Prop

  example : (∀x, ¬A x) → ¬∃x, A x :=

  assume h01: ∀x, ¬A x,

  show ¬∃x, A x, from not.intro
  (
    assume h1: ∃x, A x,

    exists.elim h1
    (
      assume y (h2: A y),
      have h3: ¬A y, from h01 y,
      show false, from h3 h2
    )
  )
end

-- 10
section
  variable  U : Type
  variables R : U → U → Prop

  example : (∃x, ∀y, R x y) → ∀y, ∃x, R x y :=
  
  assume h1: ∃x, ∀y, R x y,
  
  show ∀y, ∃x, R x y, from 
    exists.elim h1 
    (
      assume x (h2:(∀y, R x y)),
      assume y : U,
      
      have h3: (R x y), from h2 y,
    
      exists.intro x h3
    )
end
