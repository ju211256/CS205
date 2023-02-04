import data.set
import data.int.basic
import data.nat.basic
open function int set nat

section
  def f (x : ℤ) : ℤ := x + 3
  def g (x : ℤ) : ℤ := -x
  def h (x : ℤ) : ℤ := 2 * x + 3

  -- 1
  example : injective h :=

  assume x,
  assume y,

  assume h1: 2 * x + 3 = 2 * y + 3,
  
  have h2: 2 * x = 2 * y, from add_right_cancel h1,

  show x = y, from mul_left_cancel₀ dec_trivial h2


  -- 2
  example : surjective g :=
  
  assume f,

  have h1: g (-f) = -(-f), from rfl,
  have h2: g (-f) = f, from neg_neg f,
  show ∃ (a : ℤ), g a = f, from exists.intro (-f) h2


  -- 3
  example (A B : Type) (u : A → B) (v1 : B → A) (v2 : B → A)
    (h1 : left_inverse v1 u) (h2 : right_inverse v2 u) : v1 = v2 :=
  funext
    (assume x,
      calc
        v1 x = v1 (u (v2 x)) : by rw h2
         ... = v2 x          : by rw h1)
end

-- 4
section
  variables {X Y : Type}
  variable f : X → Y
  variables A B : set X

  example : f '' (A ∩ B) ⊆ f '' A ∩ f '' B :=
  assume y,
  assume h1 : y ∈ f '' (A ∩ B),
  show y ∈ f '' A ∩ f '' B, from exists.elim h1
  (
    assume a,
    assume b,

    have e1: f a = y, from and.right b,

    have e2: a ∈ A, from and.left (and.left b),
    have e3: a ∈ A ∧ f a = y, from and.intro e2 e1,
    have e4: y ∈ f '' A, from exists.intro a e3,

    have e5: a ∈ B, from and.right (and.left b),
    have e6: a ∈ B ∧ f a = y, from and.intro e5 e1,
    have e7: y ∈ f '' B, from exists.intro a e6,

    show y ∈ f '' A ∩ f '' B, from and.intro e4 e7
  )
end


-- 5
example : ∀ m n k : nat, m * (n + k) = m * n + m * k :=
  begin
    intros m n k,
    induction m,

    rw zero_mul,
    rw zero_mul,
    rw zero_mul,

    rw succ_mul,
    rw succ_mul,
    rw succ_mul,

    rw ← add_assoc,
    rw ← add_assoc,

    rw add_right_comm,

    rw m_ih,

    rw add_comm,

    rw add_assoc,
    rw add_assoc,
    rw add_assoc,

    rw add_left_comm
  end

-- 6
example : ∀ n : nat, 0 * n = 0 :=
  begin
    intro n,
    induction n,
    
    refl,

    rw mul_succ,

    rw n_ih
  end

-- 7
example : ∀ n : nat, 1 * n = n :=
  begin
    intro n,
    induction n,

    rw mul_zero,

    rw mul_succ,

    rw n_ih
  end

-- 8
example : ∀ m n k : nat, (m * n) * k = m * (n * k) :=
  begin
    intros m n k,
    induction k,

    rw mul_zero,
    rw mul_zero,
    rw mul_zero,

    rw mul_succ,
    rw mul_succ,

    rw left_distrib,

    rw k_ih
  end

-- 9
example : ∀ m n : nat, m * n = n * m :=
  begin
  intros m n,
  induction m,

  rw mul_zero,

  rw zero_mul,

  rw mul_succ,

  rw succ_mul,

  rw m_ih
  end
