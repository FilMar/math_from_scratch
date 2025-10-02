/-!
# Guida alla Sintassi Base di Lean 4

Questo file ti introduce alla sintassi fondamentale di Lean 4.
Completa ogni sezione prima di passare al TacticsGuide.lean!

## Come Usare Questo File:
1. Leggi ogni spiegazione attentamente
2. Prova gli esempi con #check
3. Completa gli esercizi sostituendo i `sorry`
4. Usa VS Code per vedere i tipi e gli errori

## Nota Importante:
Non preoccuparti se non capisci tutto subito - l'importante è familiarizzare 
con i simboli e la struttura base!
-/

/-!
## 1. TIPI FONDAMENTALI
Lean ha diversi "tipi" - pensa a loro come categorie di oggetti.
-/

-- I tipi più comuni:
#check Nat        -- Numeri naturali: 0, 1, 2, 3, ...
#check Bool       -- Booleani: true, false  
#check String     -- Stringhe: "ciao", "mondo"
#check Prop       -- Proposizioni: affermazioni che possono essere vere o false

-- Esempi di valori:
#check 42         -- Questo è un Nat
#check true       -- Questo è un Bool
#check "ciao"     -- Questo è un String

/-!
## 2. VARIABILI E DICHIARAZIONI
Come dire a Lean "useremo queste cose negli esempi"
-/

-- Dichiara variabili per gli esempi
variable (n m : Nat)           -- n e m sono numeri naturali
variable (x y : String)        -- x e y sono stringhe  
variable (P Q R : Prop)        -- P, Q, R sono proposizioni

-- Prova tu: dichiara una variabile b di tipo Bool
-- ESERCIZIO 1: completa la riga sotto
variable (b : Bool)

/-!
## 3. SIMBOLI LOGICI FONDAMENTALI
Questi sono i "mattoni" della logica matematica.
-/

-- IMPLICAZIONE: →
-- "P → Q" si legge "se P allora Q" o "P implica Q"
#check P → Q      

-- CONGIUNZIONE: ∧  
-- "P ∧ Q" si legge "P e Q" (entrambi veri)
#check P ∧ Q      

-- DISGIUNZIONE: ∨
-- "P ∨ Q" si legge "P o Q" (almeno uno vero)  
#check P ∨ Q      

-- NEGAZIONE: ¬
-- "¬P" si legge "non P"
#check ¬P         

-- EQUIVALENZA: ↔
-- "P ↔ Q" si legge "P se e solo se Q"
#check P ↔ Q      

/-!
## 4. COME SCRIVERE I SIMBOLI
In VS Code puoi digitare:
- \to o \imp per →
- \and per ∧  
- \or per ∨
- \not o \neg per ¬
- \iff per ↔
- \forall per ∀
- \exists per ∃
-/

-- ESERCIZIO 2: scrivi "se n è maggiore di m, allora n non è uguale a m"
-- Usa: n > m → ¬(n = m)
#check n > m → ¬(n = m) 

/-!
## 5. QUANTIFICATORI
Per dire "per tutti" e "esiste"
-/

-- QUANTIFICATORE UNIVERSALE: ∀
-- "∀ n : Nat, P n" significa "per ogni numero naturale n, vale P n"
#check ∀ n : Nat, n + 0 = n

-- QUANTIFICATORE ESISTENZIALE: ∃  
-- "∃ n : Nat, P n" significa "esiste un numero naturale n tale che vale P n"
#check ∃ n : Nat, n > 10

-- ESERCIZIO 3: scrivi "per ogni numero naturale n, n è uguale a se stesso"
#check ∀ (n : Nat), n = n

-- ESERCIZIO 4: scrivi "esiste un numero naturale che è maggiore di 5"
#check ∃ n: Nat, n > 5

/-!
## 6. FUNZIONI E TIPI DI FUNZIONE
Le funzioni prendono un input e danno un output.
-/

-- Una funzione da Nat a Nat
#check Nat → Nat

-- Una funzione che prende due Nat e restituisce un Nat
#check Nat → Nat → Nat

-- Esempi di funzioni built-in:
#check Nat.add    -- addizione di numeri naturali
#check Nat.mul    -- moltiplicazione di numeri naturali

-- ESERCIZIO 5: che tipo ha una funzione che prende una stringa e restituisce un booleano?
#check String → Bool

/-!
## 7. STRUTTURA DI UN TEOREMA
Ecco come si scrive un teorema in Lean.
-/

-- La struttura base:
-- theorem nome_teorema : affermazione := dimostrazione

-- Esempio semplice (senza dimostrazione per ora):
theorem esempio_base : P → P := sorry

-- Con variabili locali:
theorem esempio_con_variabili (A B : Prop) : A → B → A := sorry

-- ESERCIZIO 6: scrivi un teorema che dice "P e Q implica P"
theorem esercizio_e_implica : P → Q := sorry

-- ESERCIZIO 7: scrivi un teorema che dice "se P implica Q e Q implica R, allora P implica R"
theorem esercizio_transitivita : sorry := sorry

/-!
## 8. DEFINIZIONI SEMPLICI
Come definire nuove funzioni e costanti.
-/

-- Definire una costante:
def mio_numero : Nat := 42

-- Definire una funzione semplice:
def raddoppia (n : Nat) : Nat := n + n

-- Definire una funzione con più parametri:
def somma_tre (a b c : Nat) : Nat := a + b + c

-- ESERCIZIO 8: definisci una funzione che prende un numero e restituisce il suo triplo
def triplo (n : Nat) : Nat := 3 * n

#check triplo

-- ESERCIZIO 9: definisci una funzione che prende due booleani e restituisce la loro congiunzione
def e_logico (a b : Bool) : Bool := a ∧ b

#check e_logico

/-!
## 9. CONTROLLI E VERIFICHE
Comandi utili per esplorare.
-/

-- #check mostra il tipo di qualcosa
#check raddoppia
#check mio_numero

-- #eval calcola il valore di un'espressione
#eval raddoppia 5
#eval mio_numero + 10

-- ESERCIZIO 10: usa #eval per calcolare il triplo di 7
#eval triplo 7

/-!
## 10. RICAPITOLO: HAI IMPARATO...

✓ I tipi base: Nat, Bool, String, Prop
✓ Come dichiarare variabili con `variable`
✓ I simboli logici: →, ∧, ∨, ¬, ↔
✓ I quantificatori: ∀, ∃
✓ La struttura dei teoremi: `theorem nome : affermazione := dimostrazione`
✓ Come definire funzioni con `def`
✓ I comandi utili: #check, #eval

## PROSSIMO PASSO:
Ora sei pronto per il TacticsGuide.lean! 
Lì imparerai come scrivere le dimostrazioni usando le tattiche.

Le tattiche sono i comandi che usi dopo `by` per costruire le dimostrazioni passo dopo passo.
-/

/-!
## BONUS: ERRORI COMUNI E COME RISOLVERLI

### Errore: "expected ':'"
Significa che hai dimenticato i due punti dopo il nome del teorema.
Sbagliato: `theorem test P → P`
Corretto: `theorem test : P → P`

### Errore: "unknown identifier"  
Significa che stai usando una variabile non dichiarata.
Soluzione: aggiungi `variable (nome : Tipo)` all'inizio.

### Errore: "type mismatch"
Significa che stai provando a usare qualcosa del tipo sbagliato.
Usa #check per vedere che tipo hanno le cose.
-/
