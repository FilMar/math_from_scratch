/-!
# Logica Proposizionale in Lean 4

Questo file contiene esercizi di base sulla logica proposizionale.
Completa i `sorry` seguendo le istruzioni nei commenti.

## Sintassi Base di Lean:
- `P → Q` significa "P implica Q" 
- `P ∧ Q` significa "P e Q" (congiunzione)
- `P ∨ Q` significa "P o Q" (disgiunzione)  
- `¬P` significa "non P" (negazione)
- `True` è sempre vero
- `False` è sempre falso

## Come funzionano le dimostrazioni:
- `theorem nome (ipotesi : tipo) : goal := by tactics`
- Le ipotesi sono quello che assumiamo
- Il goal è quello che vogliamo dimostrare
- Le tattiche sono i passi della dimostrazione
-/

-- Variabili proposizionali (lettere che rappresentano proposizioni)
variable (P Q R : Prop)

/-!
## Esercizio 1: Implicazione e Riflessività
L'implicazione è riflessiva: ogni proposizione implica se stessa.

Tattiche utili:
- `intro h` : se il goal è `P → Q`, introduce l'ipotesi `h : P` e cambia il goal in `Q`
- `exact h` : se hai un'ipotesi `h` del tipo giusto, completa la dimostrazione
- `assumption` : trova automaticamente un'ipotesi che risolve il goal
-/

theorem impl_refl : P → P := by
  -- COMPLETA: dimostra che P implica P
  -- Suggerimento: usa `intro` per assumere P, poi `exact` per restituirlo
  sorry

/-!
## Esercizio 2: Transitività dell'Implicazione  
Se P implica Q e Q implica R, allora P implica R.

Tattiche aggiuntive:
- `apply h` : se `h : Q → R` e il goal è `R`, cambia il goal in `Q`
-/

theorem impl_trans : (P → Q) → (Q → R) → (P → R) := by
  -- COMPLETA: dimostra la transitività
  -- Suggerimento: usa `intro` tre volte per le tre implicazioni
  -- poi usa `apply` e `exact`
  sorry

/-!
## Esercizio 3: Congiunzione (AND)
Dimostrare entrambe le direzioni della congiunzione.

Tattiche per la congiunzione:
- `constructor` : se il goal è `P ∧ Q`, lo divide in due goal: `P` e `Q`
- `h.left` : se `h : P ∧ Q`, estrae `P`
- `h.right` : se `h : P ∧ Q`, estrae `Q`
- `⟨hp, hq⟩` : costruisce direttamente `P ∧ Q` da `hp : P` e `hq : Q`
-/

theorem and_intro : P → Q → (P ∧ Q) := by
  -- COMPLETA: se hai P e Q, puoi costruire P ∧ Q
  sorry

theorem and_elim_left : (P ∧ Q) → P := by
  -- COMPLETA: da P ∧ Q puoi estrarre P
  sorry

theorem and_elim_right : (P ∧ Q) → Q := by
  -- COMPLETA: da P ∧ Q puoi estrarre Q  
  sorry

/-!
## Esercizio 4: Disgiunzione (OR)
La disgiunzione ha due modi per essere introdotta e un modo per essere eliminata.

Tattiche per la disgiunzione:
- `left` : se il goal è `P ∨ Q`, cambia il goal in `P`
- `right` : se il goal è `P ∨ Q`, cambia il goal in `Q`
- `cases h with | inl hp => ... | inr hq => ...` : se `h : P ∨ Q`, 
  considera entrambi i casi
-/

theorem or_intro_left : P → (P ∨ Q) := by
  -- COMPLETA: da P puoi ottenere P ∨ Q
  sorry

theorem or_intro_right : Q → (P ∨ Q) := by
  -- COMPLETA: da Q puoi ottenere P ∨ Q
  sorry

theorem or_elim : (P ∨ Q) → (P → R) → (Q → R) → R := by
  -- COMPLETA: se hai P ∨ Q e sai che sia P che Q implicano R, allora R è vero
  -- Suggerimento: usa `cases` sulla disgiunzione
  sorry

/-!
## Esercizio 5: Leggi di De Morgan
Queste sono importanti equivalenze logiche.

Tattiche per la negazione:
- `¬P` è definito come `P → False`
- `exfalso` : cambia qualsiasi goal in `False`
- `contradiction` : trova una contraddizione nelle ipotesi
-/

theorem de_morgan_1 : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  -- COMPLETA: una delle leggi di De Morgan
  -- Suggerimento: ↔ significa se e solo se, quindi dovrai dimostrare entrambe le direzioni
  -- Usa `constructor` per dividere in due goal
  sorry

/-!
## Esercizio 6: Proprietà delle Operazioni Logiche
Alcune proprietà fondamentali da dimostrare.
-/

-- Commutatività della congiunzione
theorem my_and_comm : (P ∧ Q) ↔ (Q ∧ P) := by
  -- COMPLETA
  sorry

-- Commutatività della disgiunzione  
theorem my_or_comm : (P ∨ Q) ↔ (Q ∨ P) := by
  -- COMPLETA
  sorry

-- Associatività della congiunzione
theorem my_and_assoc : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) := by
  -- COMPLETA
  sorry

/-!
## Esercizio Bonus: Doppia Negazione
In logica classica, ¬¬P equivale a P.
In Lean questo richiede l'assioma del terzo escluso.
-/

-- Questo è facile (intuizionista)
theorem double_neg_intro : P → ¬¬P := by
  -- COMPLETA: da P ottieni ¬¬P
  sorry

-- Questo richiede logica classica
theorem double_neg_elim : ¬¬P → P := by
  -- COMPLETA: questo è più difficile, potrebbe richiedere `by_cases`
  -- o l'importazione di `Classical`
  sorry