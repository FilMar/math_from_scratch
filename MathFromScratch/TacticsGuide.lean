/-!
# Guida alle Tattiche Base di Lean 4

Questo file è una guida pratica alle tattiche più importanti.
Ogni tattica ha una spiegazione, la sintassi, e un esempio da completare.

## Come Usare Questo File:
1. Leggi la spiegazione di ogni tattica
2. Prova gli esempi completando i `sorry`
3. Sperimenta modificando gli esercizi
4. Usa `#check` per esplorare i tipi

## Nota sulla Sintassi:
- `theorem nome : statement := by tactics` è la forma base
- Ogni tattica opera sullo "stato della dimostrazione" 
- Lean ti mostra sempre il goal corrente e le ipotesi disponibili
-/

-- Variabili per gli esempi
variable (P Q R : Prop) (n m : Nat)

/-!
## 1. TATTICHE DI INTRODUZIONE
Queste tattiche introducono nuove ipotesi.
-/

/-! ### `intro` - Introduzione di Implicazione/Funzione
**Cosa fa:** Se il goal è `P → Q`, introduce `P` come ipotesi e cambia il goal in `Q`
**Sintassi:** `intro h` (dove `h` è il nome dell'ipotesi)
**Quando usarla:** Sempre quando il goal è un'implicazione o una funzione
-/

theorem intro_example : P → P := by
  intro h -- Ora hai ipotesi h : P e goal P
  -- COMPLETA: usa h per risolvere il goal
  exact h


-- Puoi introdurre più ipotesi in una volta
theorem intro_multiple : P → Q → P := by
  intro hp hq  -- Equivale a: intro hp; intro hq
  -- COMPLETA: quale ipotesi usi?
  exact hp
  

/-! ### `constructor` - Costruzione di Congiunzioni/Strutture
**Cosa fa:** Se il goal è `P ∧ Q`, lo divide in due goal: `P` e `Q`  
**Sintassi:** `constructor`
**Quando usarla:** Per congiunzioni, bicondicionali, esistenziali con dati concreti
-/

theorem constructor_example : P → Q → (P ∧ Q) := by
  intro hp hq
  constructor
  -- Ora hai due goal da dimostrare
  · -- Goal 1: P
    exact hp
  · -- Goal 2: Q  
    exact hq

/-!
## 2. TATTICHE DI ELIMINAZIONE  
Queste tattiche usano ipotesi esistenti.
-/

/-! ### `exact` - Soluzione Esatta
**Cosa fa:** Completa il goal se hai esattamente quello che serve
**Sintassi:** `exact h` (dove `h` ha il tipo del goal)
**Quando usarla:** Quando hai un'ipotesi del tipo giusto
-/

theorem exact_example : P → P := by
  intro h
  exact h  -- h ha tipo P, il goal è P: perfetto!

/-! ### `apply` - Applicazione di Funzione/Implicazione
**Cosa fa:** Se hai `h : P → Q` e il goal è `Q`, cambia il goal in `P`
**Sintassi:** `apply h`
**Quando usarla:** Per "lavorare all'indietro" da una conclusione
-/

theorem apply_example : (P → Q) → P → Q := by
  intro h hp
  apply h  -- h : P → Q, goal: Q, quindi nuovo goal: P
  -- COMPLETA: risolvi il nuovo goal P
  exact hp

/-! ### `cases` - Analisi per Casi
**Cosa fa:** Divide un'ipotesi in tutti i suoi casi possibili
**Sintassi:** `cases h with | caso1 => ... | caso2 => ...`
**Quando usarla:** Per disgiunzioni, tipi induttivi, esistenziali
-/

theorem cases_example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro h hpr hqr
  cases h with
  | inl hp => 
    -- Caso: h è della forma inl(hp) dove hp : P
    -- COMPLETA: risolvi usando hp
    apply hpr
    exact hp
  | inr hq =>
    -- Caso: h è della forma inr(hq) dove hq : Q  
    -- COMPLETA: risolvi usando hq
    apply hqr
    exact hq


/-!
## 3. TATTICHE DI RISCRITTURA
Queste tattiche cambiano l'aspetto del goal o delle ipotesi.
-/

/-! ### `rw` - Riscrittura (Rewrite)
**Cosa fa:** Sostituisce un lato di un'uguaglianza con l'altro
**Sintassi:** `rw [teorema]` o `rw [← teorema]` (freccia sinistra per direzione opposta)
**Quando usarla:** Per semplificare usando uguaglianze
-/

theorem rw_example : n + 0 = n → n + 0 + m = n + m := by
  intro h
  rw [h]  -- Sostituisce n + 0 con n nel goal e completa automaticamente

/-! ### `simp` - Semplificazione Automatica
**Cosa fa:** Applica automaticamente molte regole di semplificazione
**Sintassi:** `simp` o `simp [teorema1, teorema2]`
**Quando usarla:** Per semplificare espressioni aritmetiche e booleane
-/

theorem simp_example : n + 0 + (m + 0) = n + m := by
  simp  -- Semplifica automaticamente le addizioni con 0

/-!
## 4. TATTICHE SPECIALI
-/

/-! ### `induction` - Induzione Matematica
**Cosa fa:** Dimostra per induzione su un tipo induttivo (es. Nat)
**Sintassi:** `induction n with | zero => ... | succ k ih => ...`
**Quando usarla:** Per proprietà sui numeri naturali o altri tipi induttivi
-/

theorem induction_example : ∀ n : Nat, n + 0 = n := by
  intro n
  induction n with
  | zero =>
    -- Caso base: 0 + 0 = 0
    rfl
  | succ k ih =>
    -- Passo induttivo: hai ih : k + 0 = k, devi dimostrare succ k + 0 = succ k
    rfl
    -- Il caso è automatico per definizione

/-! ### `by_cases` - Dimostrazione per Casi (Logica Classica)
**Cosa fa:** Divide la dimostrazione nei casi P e ¬P
**Sintassi:** `by_cases h : P`
**Quando usarla:** Quando hai bisogno del terzo escluso
-/

theorem by_cases_example : P ∨ ¬P := by
  by_cases h : P
  · -- Caso: h : P
    left  -- Scegli il lato sinistro della disgiunzione
    exact h
  · -- Caso: h : ¬P
    right  -- Scegli il lato destro della disgiunzione
    exact h

/-!
## 5. TATTICHE DI CONTROLLO
-/

/-! ### `·` (Bullet Points) - Struttura della Dimostrazione
**Cosa fa:** Organizza la dimostrazione in sottogoal
**Sintassi:** `· tattica1; tattica2` o blocchi separati con `·`
**Quando usarla:** Per rendere le dimostrazioni più leggibili
-/

theorem bullet_example : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) := by
  constructor
  · -- Direzione →
    intro h
    constructor
    · -- Goal: P
      exact h.left.left
    · -- Goal: Q ∧ R  
      constructor
      · exact h.left.right
      · exact h.right
  · -- Direzione ←
    intro h
    constructor
    · -- Goal: P ∧ Q
      constructor
      · exact h.left
      · exact h.right.left  
    · -- Goal: R
      exact h.right.right

/-! ### `sorry` - Placeholder
**Cosa fa:** Accetta qualsiasi goal (solo per sviluppo!)
**Sintassi:** `sorry`
**Quando usarla:** Per lasciare buchi da riempire dopo, mai in codice finale
-/

/-!
## 6. ESERCIZI DI PRATICA
Completa questi esercizi usando le tattiche appena imparate.
-/

-- Esercizio 1: Usa intro, constructor, exact
theorem practice_1 : P → Q → (Q ∧ P) := by
  -- COMPLETA: ricorda l'ordine in Q ∧ P
  intro p q
  constructor
  . exact q 
  . exact p

-- Esercizio 2: Usa cases per la disgiunzione
theorem practice_2 : (P ∨ Q) → (Q ∨ P) := by
  -- COMPLETA: mostra la commutatività della disgiunzione
  intro h
  cases h with 
  | inl hp => 
    right
    exact hp
  | inr hq => 
    left -- questo non lo sapevo...
    exact hq


-- Esercizio 3: Usa apply e intro
theorem practice_3 : (P → Q → R) → (P ∧ Q → R) := by
  -- COMPLETA: trasforma una funzione di due argomenti in una che prende una coppia
  intro h p
  apply h
  apply p.left
  exact p.right
  

-- Esercizio 4: Usa induction sui naturali  
theorem practice_4 : ∀ n : Nat, 0 + n = n := by
  -- COMPLETA: dimostra che 0 è neutro a sinistra per +
  intro h
  induction h with
  | zero =>
    rfl
  | succ s hi =>
    calc 0 + s.succ 
     _ = (0 + s).succ := by rfl
     _ = s.succ := by rw [hi] 
    
    
    

-- Esercizio 5: Usa simp e rw
theorem practice_5 : ∀ n : Nat, n + (0 + 0) = n + 0 := by
  -- COMPLETA: semplifica l'espressione
  intro h
  calc  h + (0 + 0) = h + 0 := by rfl


/-!
## 7. TATTICHE AVANZATE (Bonus)
Queste sono più avanzate ma molto utili.
-/

-- `contradiction` - trova contraddizioni automaticamente
theorem contradiction_example : P → ¬P → Q := by
  intro hp hnp
  contradiction  -- Lean trova automaticamente che hp e hnp sono contraddittorie

-- `exfalso` - usa il principio ex falso sequitur quodlibet  
theorem exfalso_example : False → P := by
  intro h
  exfalso  -- Cambia il goal in False
  exact h

-- `have` - introduce lemmi intermedi
theorem have_example : P → Q → (P ∧ Q) ∧ P := by
  intro hp hq
  have h : P ∧ Q := ⟨hp, hq⟩  -- Lemma intermedio
  exact ⟨h, hp⟩

/-!
## Consigli per Iniziare:
1. Usa sempre `intro` per le implicazioni
2. Usa `constructor` per AND, esistenziali, bicondicionali
3. Usa `cases` per OR e tipi induttivi  
4. Usa `exact` quando hai esattamente quello che serve
5. Usa `apply` per lavorare all'indietro
6. Usa `simp` per semplificare aritmetica
7. Organizza con `·` per leggibilità

## Per Esplorare:
- `#check nome` mostra il tipo di un teorema
- `#print nome` mostra la definizione  
- Hover su teoremi in VS Code per vedere la documentazione
-/
