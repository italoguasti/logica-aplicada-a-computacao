import Mathlib.Tactic.Basic

section PropLogic

  variable (A B C : Prop)

  theorem first_theorem
    : (A → B) → A → B := by
      intros H1 H2
      apply H1
      assumption

  theorem first2 : (A → B) → A → B :=
    λ H : A → B => H

-- *** Exercício 1.

  lemma ex1 : A → B → A := by
    intros HA HB
    exact HA

-- *** Exercício 2.

  lemma ex2 : (A → B) → (B → C) → A → C := by
    intros HAB HBC HA
    apply HBC
    apply HAB
    exact HA

-- ** Conjunção
-- par

  theorem and_comm1 : (A ∧ B) → (B ∧ A) := by
      intros H
      rcases H with ⟨ H1 , H2 ⟩
      apply And.intro
      ·
        exact H2
      ·
        assumption

  theorem and_assoc1
    : A ∧ (B ∧ C) → (A ∧ B) ∧ C := by
      intros H
      rcases H with ⟨ H1, H2, H3 ⟩
      apply And.intro
      ·
        apply And.intro
        ·
          exact H1
        ·
          exact H2
      ·
        exact H3

-- *** Exercício 3

  theorem ex3 : (A ∧ B) ∧ C -> A ∧ (B ∧ C) := by
    intros H
    rcases H with ⟨ ⟨ HA, HB ⟩, HC ⟩
    apply And.intro
    · exact HA
    · apply And.intro
      · exact HB
      · exact HC

-- *** Exercício 4

  theorem ex4 : ((A ∧ B) → C) → (A → B → C) := by
    intros H HA HB
    apply H
    exact And.intro HA HB

-- *** Exercício 5

  theorem ex5 : (A → B → C) → ((A ∧ B) → C) := by
    intros H HAB
    rcases HAB with ⟨ HA, HB ⟩
    apply H
    · exact HA
    · exact HB

-- *** Exercício 6

  theorem ex6 : ((A → B) ∧ (A → C)) → A → (B ∧ C) := by
    intros H HA
    rcases H with ⟨ HAB, HAC ⟩
    apply And.intro
    · apply HAB
      exact HA
    · apply HAC
      exact HA

  -- A ↔ B = (A → B) ∧ (B → A)

  lemma iff_demo : (A ∧ B) ↔ (B ∧ A) := by
    apply Iff.intro
    ·
      intros H
      rcases H with ⟨ H1, H2 ⟩
      apply And.intro <;> assumption
    ·
      intros H
      rcases H with ⟨ H1, H2 ⟩
      apply And.intro <;> assumption

-- Negação
-- ¬ A ≃ A → False

  lemma modus1 : ((A → B) ∧ ¬ B) → ¬ A := by
    intros H
    rcases H with ⟨ H1 , H2 ⟩
    intros HA
    apply H2
    apply H1
    exact HA

  lemma contraEx : A → ¬ A → B := by
    intros H1 H2
    contradiction

  lemma or_comm1 : (A ∨ B) → (B ∨ A) := by
    intros H
    rcases H with H1 | H2
    ·
      right
      exact H1
    ·
      left
      exact H2

  lemma orex2 : ((A ∨ B) ∧ ¬ A) → B := by
    intros H
    rcases H with ⟨ H1 | H2, H3 ⟩
    ·
      contradiction
    ·
      exact H2

-- Exercício 8

  lemma ex8 : (A ∨ (B ∧ C)) → (A ∨ B) ∧ (A ∨ C) := by
    intros H
    rcases H with HA | ⟨ HB, HC ⟩
    ·
      apply And.intro <;> left <;> exact HA
    ·
      apply And.intro <;> right
      · exact HB
      · exact HC

-- Lógica clássica

  open Classical

  -- excluded middle

  #check (em A)

  lemma doubleNeg : ¬ (¬ A) ↔ A := by
    apply Iff.intro
    ·
      have H1 : A ∨ ¬ A := em A
      rcases H1 with H1 | H2
      ·
        intros _H3
        exact H1
      ·
        intros H3
        contradiction
    ·
      intros H H1
      contradiction

-- Exercício 9

lemma ex9 : (¬ B → ¬ A) → (A → B) := by
  intros H HA
  by_contra HNB
  have HNA := H HNB
  contradiction

-- Exercício 10

lemma ex10 : ((A → B) → A) → A := by
  intros H
  by_cases HA : A
  · exact HA
  · apply H
    intro _
    contradiction

end PropLogic
