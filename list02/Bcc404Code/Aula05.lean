-- 2. Listas encadeadas (tipo List na biblioteca)

import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith

-- List

inductive list (A : Type) where
| nil : list A
| cons : A → list A → list A
deriving Repr
-- cons 1 (cons 2 (cons 3 nil))

open list --

-- length
-- implicito {A : Type}
def size {A : Type}(xs : list A) : ℕ :=
  match xs with
  | nil => 0
  | cons _ xs => Nat.succ (size xs)

-- repeat
def listRepeat {A : Type}(n : ℕ)(x : A) : list A :=
  match n with
  | Nat.zero => nil
  | Nat.succ n' => cons x (listRepeat n' x)

-- append
def cat {A : Type}(xs ys : list A) : list A :=
  match xs with
  | nil => ys                         -- (1)
  | cons x xs' => cons x (cat xs' ys) -- (2)

infixl:60 " .++. " => cat

def reverse {A : Type}(xs : list A) : list A :=
  match xs with
  | nil => nil   -- (1)
  | cons x' xs' => reverse xs' .++. (cons x' nil) -- (2)

def rev {A : Type}(xs ac : list A) : list A :=
  match xs with
  | nil => ac
  | cons x' xs' => rev xs' (cons x' ac)

#check Nat.succ_add

lemma cat_size {A}(xs ys : list A) :
  size (xs .++. ys) = size xs + size ys := by
  induction xs with
  | nil =>
    simp [size, cat]
  | cons _ xs' IH =>
    simp [size, cat, IH, Nat.succ_add]

lemma listRepeat_size {A}(x : A)(n : ℕ) :
  size (listRepeat n x) = n := by
  induction n with
  | zero =>
    simp [listRepeat, size]
  | succ n' IH =>
    simp [listRepeat, size]
    exact IH

lemma reverse_size {A}(xs : list A) :
  size (reverse xs) = size xs := by
  induction xs with
  | nil =>
    simp [reverse, size]
  | cons _ _ IH =>
    simp [reverse, cat_size, size]
    exact IH

lemma cat_assoc {A}(xs ys zs : list A)
  : xs .++. ys .++. zs = xs .++. (ys .++. zs) := by
  induction xs with
  | nil =>
    simp [cat]
  | cons x xs' IH =>
    simp [cat]
    exact IH

lemma cat_nil_r {A}(xs : list A)
  : xs .++. nil = xs := by
  induction xs with
  | nil =>
    simp [cat]
  | cons x xs' IH =>
    simp [cat]
    exact IH

lemma reverse_cat {A}(xs ys : list A) :
  reverse (xs .++. ys) = reverse ys .++. reverse xs := by
  induction xs with
  | nil =>
    simp [reverse, cat, cat_nil_r]
  | cons x xs' IH =>
    simp [reverse, IH, cat_assoc]

lemma reverse_reverse {A}(xs : list A) :
  reverse (reverse xs) = xs := by
  induction xs with
  | nil =>
    simp [reverse]
  | cons x xs' IH =>
    simp [reverse, reverse_cat, cat]
    exact IH


mutual
  lemma rev_cat_xss {A} (xs1 xs2 ys : list A) :
    rev (xs1 .++. xs2) ys = rev xs2 nil .++. rev xs1 ys := by
      cases xs1 with
      | nil =>
          simp [cat, rev]
          apply Eq.symm
          simp [rev_cat_nil xs2 ys]
      | cons x1' xs1' =>
          simp [rev]
          simp [rev_cat_xss xs1' xs2 (cons x1' ys)]
  lemma rev_cat_nil {A} (xs ys : list A) :
    rev xs nil .++. ys = rev xs ys := by
      have H0 (k : A) (ks : list A) : cons k ks = cons k nil .++. ks := by
        cases ks with
        | nil => simp [cat_nil_r]
        | cons k' ks' => simp [cat]
      cases xs with
      | nil => simp [rev, cat]
      | cons x' xs' =>
          rw [H0]
          simp [rev_cat_xss (cons x' nil) xs' nil]
          simp [rev]
          simp [cat_assoc]
          simp [cat]
          simp [rev_cat_nil xs' (cons x' ys)]
end


lemma reverse_rev {A} (xs : list A) :
  reverse xs = rev xs nil := by
  induction xs with
  | nil =>
    simp [reverse, rev]
  | cons x' xs' IH =>
    simp [reverse, rev]
    rw [<- rev_cat_nil xs' (cons x' nil)]
    simp [IH]




section MAP
  variable {A B : Type}

  -- high-order function

  def map (f : A → B)(xs : list A) : list B :=
    match xs with
    | nil => nil
    | cons y ys => cons (f y) (map f ys)


  lemma map_id (xs : list A)
    : map (λ x => x) xs = xs := by
    induction xs with
    | nil => rfl
    | cons y ys IH =>
      simp [map]
      exact IH

  lemma map_app (xs ys : list A)(f : A → B)
    : map f (xs .++. ys) = (map f xs) .++. (map f ys) := by
    induction xs with
    | nil =>
        simp [cat]
    | cons x' xs' IH =>
        simp [map, IH, cat]

  lemma map_compose (f : A → B)(g : B → C)(xs : list A)
    : map (λ x => g (f x)) xs = (map g (map f xs)) := by
    induction xs with
    | nil =>
        simp [map]
    | cons x' xs' IH =>
        simp [map]
        exact IH

end MAP

section FILTER
  variable {A : Type}

  def filter (p : A → Bool)(xs : list A) : list A :=
    match xs with
    | nil => nil
    | cons y ys => if p y then cons y (filter p ys)
                    else filter p ys

  lemma filter_cat (p : A → Bool)(xs ys : list A) :
    filter p xs .++. filter p ys = filter p (xs .++. ys) := by
    induction xs with
    | nil =>
        simp [filter, cat]
    | cons x' xs' IH =>
        simp [filter]
        split
        ·
          simp [cat]
          exact IH
        ·
          exact IH


  lemma filter_reverse (p : A → Bool)(xs : list A) :
    reverse (filter p xs) = filter p (reverse xs) := by
    induction xs with
    | nil =>
        simp [filter, reverse]
    | cons x' xs' IH =>
        simp [filter]
        split
        ·
          simp [reverse]
          simp [<- filter_cat]
          simp [<- IH]
          simp [filter]
          split
          ·
            rfl
          ·
            contradiction
        ·
          simp [reverse]
          simp [<- filter_cat]
          simp [<- IH]
          simp [filter]
          split
          ·
            contradiction
          ·
            simp [cat_nil_r]


  lemma filter_size (p : A → Bool)(xs : list A) :
    size (filter p xs) ≤ size xs := by
    induction xs with
    | nil =>
        simp [size]
    | cons x' xs' IH =>
        simp [filter]
        split
        ·
          simp [size]
          apply Nat.succ_le_succ
          exact IH
        ·
          apply le_trans IH
          simp [size]
          simp [Nat.le_succ]


end FILTER

section MEMBERSHIP
  variable {A : Type}

  def member [DecidableEq A](x : A)(xs : list A) : Bool :=
    match xs with
    | nil => false
    | cons y ys => match decEq x y with
                   | isFalse _ => member x ys
                   | isTrue _ => true

  lemma member_cat_true_left [DecidableEq A](x : A)(xs : list A) :
    member x xs = true → member x (xs .++. ys) = true := by
    induction xs with
    | nil =>
        simp [member]
    | cons x' xs' IH =>
        simp [member]
        split
        ·
          exact IH
        ·
          simp

  lemma member_cat_true_right [DecidableEq A](x : A)(xs : list A) :
    member x ys = true → member x (xs .++. ys) = true := by
    induction xs with
    | nil =>
        simp [cat]
    | cons x' xs' IH =>
        simp [cat]
        simp [member]
        split
        ·
          exact IH
        ·
          simp


  lemma member_cat_and [DecidableEq A] (a : A) (xs ys : list A) :
    (member a xs = false ∧ member a ys = false) → (member a (xs .++. ys) = false) := by
    have H0 (k1 k2 : A) (ks : list A) : k1 = k2 → member k1 (cons k2 ks) = true := by
      intros Hk
      simp [member]
      split
      .
        contradiction
      .
        simp
    intros H
    rcases H with ⟨H1 , H2⟩
    have H_aux (k1 k2 : A) (ks : list A) :
      ¬ k1 = k2 →
      member k1 (cons k2 ks) = false →
      ---------------------------------
      member k1 ks = false := by
        intros h0 h1
        simp [member] at h1
        split at h1
        .
          exact h1
        .
          absurd H1
          contradiction
    induction xs with
    | nil =>
        simp [cat]
        exact H2
    | cons x' xs' IH =>
        simp [member]
        split
        .
          rename_i x h _
          apply IH
          apply (H_aux a x' xs' h)
          exact H1
        .
          rename_i x h _
          absurd H1
          simp
          apply H0
          exact h

  lemma member_reverse [DecidableEq A](x : A)(xs : list A) :
    member x xs = member x (reverse xs) := by
    induction xs with
    | nil =>
        simp [member]
    | cons x' xs' IH =>
        simp [member]
        split
        ·
          simp [reverse, IH]
          cases H : member x (reverse xs') with
          | true  =>
            apply Eq.symm
            apply member_cat_true_left
            exact H
          | false =>
            apply Eq.symm
            apply (member_cat_and x (reverse xs') (cons x' nil))
            apply And.intro
            .
              exact H
            .
              simp [member]
              split
              .
                rfl
              .
                contradiction
        ·
          apply Eq.symm
          simp [reverse]
          apply member_cat_true_right
          simp [member]
          split
          .
            contradiction
          .
            rfl

end MEMBERSHIP
