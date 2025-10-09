/-!
# Logica Proposizionale

Il fondamento di ogni ragionamento matematico. La logica proposizionale studia i principi 
basilari dell'inferenza logica che rendono possibile la dimostrazione matematica.

**Sviluppo Storico:**
- **Aristotele (384-322 a.C.)**: Primo studio sistematico della logica nell'"Organon" tramite i sillogismi
- **Stoici (III secolo a.C.)**: Svilupparono la logica proposizionale e le implicazioni
- **George Boole (1815-1864)**: Approccio algebrico alla logica in "Laws of Thought" (1854)
- **Gottlob Frege (1848-1925)**: Logica simbolica moderna in "Begriffsschrift" (1879)

I simboli che usiamo oggi (∧, ∨, →, ¬) furono standardizzati solo nel XX secolo, 
ma le relazioni logiche che rappresentano sono studiate da oltre 2000 anni.
-/

variable (P Q R : Prop)

/-!
## Implicazione e Riflessività

**Significato Matematico:** La riflessività dell'implicazione stabilisce che ogni 
affermazione segue da se stessa - un principio fondamentale di identità nella logica.

**Nota Storica:** Questo principio era così ovvio per i matematici antichi che 
non fu formalmente enunciato fino allo sviluppo della logica moderna. Aristotele 
lo prese come assunzione implicita nei suoi sillogismi.
-/

theorem impl_refl : P → P := by
  intro h
  exact h

/-!
## Transitività dell'Implicazione

**Scoperta da:** Aristotele (ragionamento sillogistico)
**Significato:** La spina dorsale della dimostrazione matematica - se possiamo stabilire 
una catena di implicazioni, possiamo concludere il risultato finale dalla premessa iniziale.

**Esempio di Aristotele:** "Tutti gli uomini sono mortali, Socrate è un uomo, 
quindi Socrate è mortale." Questa stessa struttura logica è alla base di ogni 
dimostrazione matematica che procede attraverso passaggi intermedi.
-/

theorem impl_trans : (P → Q) → (Q → R) → (P → R) := by
  intro a b p
  apply b
  apply a
  exact p

/-!
## Congiunzione (AND Logico)

**Origini Antiche:** Il concetto di congiunzione appare nella logica aristotelica, 
anche se non formalizzato con simboli moderni fino al lavoro di Boole.

**Significato Matematico:** La congiunzione ci permette di combinare condizioni multiple.
In matematica, usiamo costantemente affermazioni come "n è pari E n > 10".
-/

theorem and_intro : P → Q → (P ∧ Q) := by
  intro a b
  apply And.intro -- si puo' usare anche il costructor, ma secondo me e' meno esplicito
  apply a
  apply b
    


theorem and_elim_left : (P ∧ Q) → P := by
  intro a
  apply a.left

theorem and_elim_right : (P ∧ Q) → Q := by
  intro a
  apply a.right

/-!
## Disgiunzione (OR Logico)

**Innovazione Stoica:** Gli Stoici furono i primi a distinguere chiaramente tra 
OR inclusivo (uno o entrambi) e OR esclusivo (uno ma non entrambi). La matematica 
moderna usa principalmente l'OR inclusivo.

**OR Legale vs Matematico:** È interessante notare che il linguaggio legale spesso 
usa l'OR esclusivo ("colpevole O innocente") mentre la matematica usa l'OR inclusivo, 
portando a secoli di dibattito filosofico sul significato "naturale" di "o".
-/

theorem or_intro_left : P → (P ∨ Q) := by
  intro p
  apply Or.intro_left
  apply p



theorem or_intro_right : Q → (P ∨ Q) := by
  intro q
  apply Or.intro_right
  apply q

/-! ## Il teorema di eliminazione dell'OR (la regola di inferenza) 

è un principio fondamentale della logica noto come Ragionamento per Casi (o Case Analysis).
Sebbene il principio stesso sia utilizzato fin dai tempi di Aristotele (circa IV secolo a.C.) e fosse implicito nella logica tradizionale, 
la sua formulazione esplicita e sistematica come regola formale di inferenza all'interno di un sistema logico moderno si deve principalmente
al lavoro del logico tedesco Gerhard Gentzen negli anni '30 del XX secolo.

**Il Contributo di Gentzen**
Gentzen, nei suoi lavori del 1934-1935,
sviluppò i sistemi di Deduzione Naturale (come quello su cui si basa Lean) e il Calcolo dei Sequenti.
Nel sistema di Deduzione Naturale, Gentzen definì le regole logiche in coppie:
Regole di Introduzione (che dicono come costruire una formula con un connettivo).
Regole di Eliminazione (che dicono come usare una formula con un connettivo per giungere a una conclusione).
La regola di Eliminazione dell'OR (∨E nella notazione di Gentzen, che è l'equivalente del tuo or_elim) fu stabilita come una delle regole centrali
per definire il significato dell'operatore "OR" in modo formale e rigoroso. 
-/
theorem or_elim : (P ∨ Q) → (P → R) → (Q → R) → R := by
  intro a b c
  cases a with
  | inl ap =>
    apply b
    exact ap
  | inr aq =>
    apply c
    exact aq
/-!
## Leggi di De Morgan

**Scoperte da:** Augustus De Morgan (1806-1871)
**Pubblicate:** 1847 in "Formal Logic"

**L'Uomo:** De Morgan era famosamente eccentrico - rifiutò tutti gli onori e le lauree, 
dicendo "Non sono mai stato Senior Wrangler, non ho mai provato per onori universitari, 
e non li avrei mai accettati." Eppure divenne uno dei logici più influenti del XIX secolo.

**Significato Matematico:** Queste leggi rivelano la profonda dualità tra ∧ e ∨ 
attraverso la negazione. Sono fondamentali per l'algebra booleana e l'informatica.

**Impatto Moderno:** Ogni processore implementa queste leggi nei suoi circuiti logici.
Quando scrivi codice con condizioni come `!(a && b)`, stai usando l'intuizione di De Morgan.
-/

theorem de_morgan_1 : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  constructor
  intro a
  apply NonAnd

/-!
## Commutatività delle Operazioni Logiche

**Riconoscimento Antico:** Mentre il termine "commutativo" deriva dall'algebra del XIX secolo,
il concetto che "A e B" significa lo stesso di "B e A" era riconosciuto dai logici antichi.

**Contributo di Boole:** George Boole fu il primo a trattare la logica algebricamente,
mostrando che le operazioni logiche seguono molte delle stesse leggi dell'aritmetica.
-/

theorem and_comm : (P ∧ Q) ↔ (Q ∧ P) := sorry

theorem or_comm : (P ∨ Q) ↔ (Q ∨ P) := sorry

/-!
## Associatività

**Dall'Algebra alla Logica:** Il concetto di associatività fu prima studiato nell'aritmetica, 
poi generalizzato all'algebra astratta da matematici come Arthur Cayley (1821-1895). 
La sua applicazione alla logica mostra la profonda unità tra diverse aree della matematica.
-/

theorem and_assoc : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) := sorry

/-!
## Doppia Negazione

**Intuizionista vs Classica:** L'eliminazione della doppia negazione (¬¬P → P) 
divide la filosofia matematica.

**L.E.J. Brouwer (1881-1966):** Fondò l'intuizionismo, rifiutando l'eliminazione 
della doppia negazione come non-costruttiva. Argomentò che non possiamo concludere 
che P esiste solo perché abbiamo dimostrato ¬¬P.

**Matematica Classica:** Accetta l'eliminazione della doppia negazione, permettendo 
la dimostrazione per assurdo.

**Il Dibattito:** Questo principio apparentemente semplice scatenò uno dei più grandi 
dibattiti della matematica del XX secolo sulla natura dell'esistenza matematica e della dimostrazione.
-/

theorem double_neg_intro : P → ¬¬P := sorry

-- Questo richiede logica classica (legge del terzo escluso)
theorem double_neg_elim : ¬¬P → P := sorry
