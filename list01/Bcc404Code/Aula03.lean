import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

-- Aula 03: Programação funcional em Lean

-- # Interagindo com o Lean

-- Avaliando expressões

#eval 2 * 4

-- Obtendo tipo de expressões

#check String.append
#check not

-- # Funções e definições

def sayHello (s : String) : String :=
  String.append "Hello " (String.append s "!")

def helloLean := sayHello "Lean"

#eval helloLean

def maximum (n m : ℕ) : ℕ :=
  if n > m then n else m

#eval maximum (2 + 4) (2 * 8)

-- # Tipos
-- level polymorphism
-- estratificação de tipos
-- Bool : Type_0 : Type_1 : Type_2 ...
--
-- Paradoxo Russell

def Bla : Type := Nat -- Bla e Nat são tipos diferentes

-- isso leva a um erro

-- def theAnswer : Bla := 42

-- forma correta

abbrev Natural := Nat

def Answer : Natural := 42

-- Registros

structure Point where
  x : Nat
  y : Nat
deriving Repr

-- Repr: permite representação como strings

def origin : Point := {x := 0 , y := 0}
def origin1 : Point := Point.mk 0 0

-- NomeRegistro.mk arg1 ... argn

#eval origin
-- Se a : Point, a.x a.y

def addPoints (a b : Point) : Point :=
  {x := a.x + b.x, y := a.y + b.y}

def addPoint (a b : Point) : Point :=
  match a, b with
  | Point.mk x1 y1, Point.mk x2 y2 =>
    Point.mk (x1 + x2) (y1 + y2)

-- #Tipos de dados algébricos

-- 0. Enumerações

inductive WeekDay where
| Sunday : WeekDay
| Monday : WeekDay
| Tuesday : WeekDay
| Wednesday : WeekDay
| Thursday : WeekDay
| Friday : WeekDay
| Saturday : WeekDay
deriving Repr

-- Funções totais / funções parciais.
-- Verificação de totalidade
--  1. Casamento de padrão exaustivo
--  2. Funções recursivas devem sempre terminar.
--  2.1. Chamadas recursivas devem ser feitas somente sobre
--       argumentos sintaticamente "menores".

def nextDay (d : WeekDay) : WeekDay :=
  open WeekDay in
  match d with
  | Sunday => Monday
  | Monday => Tuesday
  | Tuesday => Wednesday
  | Wednesday => Thursday
  | Thursday => Friday
  | Friday => Saturday
  | Saturday => Sunday

#eval nextDay WeekDay.Thursday

def prevDay (d : WeekDay) : WeekDay :=
  match d with
  | WeekDay.Sunday => WeekDay.Saturday
  | WeekDay.Monday => WeekDay.Sunday
  | WeekDay.Tuesday => WeekDay.Monday
  | WeekDay.Wednesday => WeekDay.Tuesday
  | WeekDay.Thursday => WeekDay.Wednesday
  | WeekDay.Friday => WeekDay.Thursday
  | WeekDay.Saturday => WeekDay.Friday

-- análise de casos.

-- igualdade
--- Proposicional: forall x, x = x

lemma nextPrevId (d : WeekDay)
  : prevDay (nextDay d) = d := by
    cases d <;> simp [nextDay, prevDay]


lemma prevNextId (d : WeekDay)
  : nextDay (prevDay d) = d := by
  cases d <;> simp [nextDay, prevDay]


-- definição de boolean (presente na biblioteca)

/-
inductive Bool where
| true : Bool
| false : Bool
-/

def negb (x : Bool) : Bool :=
  match x with
  | true => false
  | _    => true

def andb (x y : Bool) : Bool :=
  match x with
  | true => y
  | false => false

def orb (x y : Bool) : Bool :=
  match x with
  | false => y
  | true => true


infixl:65 " .&. " => andb
infixl:80 " .|. " => orb

#eval true .&. true

lemma negb_inv (b : Bool) : negb (negb b) = b := by
  cases b <;> simp [negb]


lemma andb_comm b1 b2 : b1 .&. b2 = b2 .&. b1 := by
  cases b2 <;> cases b1 <;> simp [andb]

lemma orb_comm b1 b2 : b1 .|. b2 = b2 .|. b1 := by
  cases b2 <;> cases b1 <;> simp [orb]

lemma andb_assoc b1 b2 b3 :
  b1 .&. b2 .&. b3 = b1 .&. (b2 .&. b3) := by
  cases b1 <;> cases b2 <;> cases b3 <;> simp [andb]

lemma andb_orb b1 b2 : b1 .&. b2 = b1 .|. b2 → b1 = b2 := by
  cases b1 <;> cases b2 <;> simp [andb, orb]

lemma deMorgan1 b1 b2 :
  negb (b1 .&. b2) = (negb b1) .|. (negb b2) := by
  cases b1 <;> cases b2 <;> simp [negb, andb, orb]

lemma deMorgan2 b1 b2 :
  negb (b1 .|. b2) = (negb b1) .&. (negb b2) := by
  cases b1 <;> cases b2 <;> simp [negb, andb, orb]

/-
# Exercício: Modelando penalidade por atraso em entregas

O objetivo desta sequência de exercícios é a modelagem
de um sistema de penalidade por atraso em entregas e
a demonstração de alguns fatos simples sobre esse sistema.

Vamos considerar um sistema de notas em que teremos
conceitos e um modificador. O seguinte tipo modela as
diferentes possibilidades de conceitos para a nota.
-/

inductive letter :=
| A | B | C | D | E | F
deriving Repr

-- Modificadores são utilizados para representar
-- diferentes escalas de notas: A + , A ou A -

inductive modifier :=
| Plus | Plain | Minus
deriving Repr

-- Definição de uma nota

inductive grade :=
| Grade : letter → modifier → grade
deriving Repr

/-
Uma parte importante é a comparação entre notas.
Para representar os possíveis resultados de
comparação, vamos criar o tipo cmp
-/

inductive cmp1 :=
| Lt | EQ | Gt
deriving Repr

open letter
open modifier
open grade
open cmp1

-- Exercício 1. Comparando letras
-- Desenvolva a função

def letter_cmp (l1 l2 : letter) : cmp1 :=
  match l1, l2 with
  | A, A => EQ
  | B, B => EQ
  | C, C => EQ
  | D, D => EQ
  | E, E => EQ
  | F, F => EQ
  | A, _ => Gt
  | _, A => Lt
  | B, _ => Gt
  | _, B => Lt
  | C, _ => Gt
  | _, C => Lt
  | D, _ => Gt
  | _, D => Lt
  | E, _ => Gt
  | _, E => Lt

-- Exercício 2. Prove o seguinte resultado

theorem letter_cmp_refl l : letter_cmp l l = EQ := by
  cases l <;> simp [letter_cmp]

-- Exercício 3. Desenvolva a função

def modifier_cmp (m1 m2 : modifier) : cmp1 :=
  match m1, m2 with
  | Plus, Plus => EQ
  | Plain, Plain => EQ
  | Minus, Minus => EQ
  | Plus, _ => Gt
  | _, Plus => Lt
  | Plain, _ => Gt
  | _, Plain => Lt

-- Exercício 4. Desenvolva a função

def grade_cmp (g1 g2 : grade) : cmp1 :=
  match g1, g2 with
  | Grade l1 m1, Grade l2 m2 =>
    match letter_cmp l1 l2 with
    | EQ => modifier_cmp m1 m2
    | cmp1.Lt => Lt
    | cmp1.Gt => Gt

-- Exercício 5. Desenvolva a função

def lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => E
  | E => F
  | F => F

lemma lower_letter_F : lower_letter F = F := by
  simp [lower_letter]

-- Exercício 6. Prove o seguinte teorema

theorem lower_letter_lowers l :
  letter_cmp F l = Lt →
  letter_cmp (lower_letter l) l = Lt := by
  cases l <;> simp [letter_cmp, lower_letter]

-- Exercício 7. Desenvolva a função

def lower_grade (g : grade) : grade :=
  match g with
  | Grade l m =>
    match l, m with
    | F, Minus => Grade F Minus
    | _, Minus => Grade (lower_letter l) Plain
    | _, Plain => Grade l Minus
    | _, Plus => Grade l Plain

lemma F_Minus_lowest_grade :
  lower_grade (Grade F Minus) = Grade F Minus := by
  simp [lower_grade]

-- Exercício 8. Prove o seguinte teorema que formaliza
-- que se uma nota passada para lower_grade é maior que
-- F-, então o resultado de lower_grade será uma nota
-- menor que a fornecida como argumento.

theorem lower_grade_lowers g :
  grade_cmp (Grade F Minus) g = Lt ->
  grade_cmp (lower_grade g) g = Lt := by
  intros H
  simp [lower_grade, lower_letter, grade_cmp, modifier_cmp, letter_cmp]
  induction g with
  | Grade l m =>
    induction l with
    | F =>
      induction m with
      | Minus =>
        simp
        contradiction
      | Plain => rfl
      | Plus => rfl
    | _ =>
      induction m with
      | Minus => rfl
      | Plain => rfl
      | Plus => rfl

-- Exercício 9
/-
Agora, você deverá implementar uma função que
irá aplicar sobre uma nota a penalidade por atraso
de acordo com a tabela seguinte

# Dias de atraso     Penalidade
0 - 8                 sem penalidade
9 - 16                Diminuir a nota por um passo.
17 - 20               Diminuir a nota por dois passos.
          >= 21       Diminuir a nota por três passos.
-/

def apply_penalty (days_late : Nat) (g : grade) : grade :=
  if days_late <= 8 then g
  else if days_late <= 16 then lower_grade g
  else if days_late <= 20 then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g))

-- Exemplo de comparação. Use em sua definição.
#eval 1 < 2
