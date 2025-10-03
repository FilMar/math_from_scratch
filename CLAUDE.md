# Guida per Claude: Creazione di Nuovi File Matematici

Questo documento spiega come creare nuovi file `.lean` quando sarà necessario espandere il progetto matematico.

## 🎯 **Filosofia del Progetto**

### **Obiettivo:** 
Ricostruire la matematica dalle fondamenta con focus storico e concettuale, non tutorial su Lean.

### **Stile:**
- **Pura matematica:** Zero riferimenti a Lean come tool
- **Storia ricca:** Ogni teorema ha contesto storico e aneddoti
- **Tutti `sorry`:** L'utente impara dimostrando
- **Connessioni:** Ogni concetto si collega alla narrativa più ampia

---

## 📝 **Template per Nuovi File**

### **Struttura Standard:**

```lean
/-!
# [Nome Area Matematica]

[Descrizione di 2-3 righe dell'area e sua importanza]

**Sviluppo Storico:**
- **[Matematico 1] ([date])**: [Contributo principale]
- **[Matematico 2] ([date])**: [Contributo principale]  
- **[Matematico 3] ([date])**: [Contributo principale]
- **[Matematico 4] ([date])**: [Contributo principale]

[Paragrafo conclusivo su importanza moderna o connessioni]
-/

-- Eventuali variabili/parametri necessari
variable {α β : Type*} [eventuali constraints]

/-!
## [Nome Concetto/Teorema 1]

**[Chi/Quando]:** [Breve storia dello scopritore]
**[Significato/Importanza]:** [Perché questo concetto è fondamentale]

**[Aneddoto storico opzionale]:** [Storia interessante sul matematico o sulla scoperta]

[Spiegazione matematica del concetto senza riferimenti a Lean]
-/

theorem [nome_teorema] : [statement] := sorry

/-!
## [Nome Concetto/Teorema 2]
...
-/

theorem [altro_teorema] : [statement] := sorry
```

---

## 🎨 **Elementi di Stile**

### **1. Sezione Introduttiva (`/-! # Titolo -/`):**
- **Nome chiaro** dell'area matematica
- **Descrizione breve** ma evocativa (2-3 righe)
- **Sviluppo Storico** con 4-6 matematici chiave
- **Connessione moderna** (AI, fisica, informatica, ecc.)

### **2. Sezioni per Teoremi (`/-! ## Nome -/`):**
- **Scopritore e data** quando rilevante
- **Significato matematico** profondo
- **Aneddoto storico** del matematico (personalità, controversie, vita)
- **Impatto moderno** o connessioni interdisciplinari

### **3. Teoremi:**
- **Solo `sorry`** - nessuna dimostrazione
- **Nomi descrittivi** in snake_case
- **Statements chiari** e ben tipati

---

## 🧠 **Come Scegliere gli Aneddoti Storici**

### **Tipi di Storie Efficaci:**
1. **Controversie:** Resistenza a nuove idee (numeri negativi, infinito)
2. **Personalità eccentriche:** Abitudini strane, ossessioni
3. **Tragedie:** Galois, Ramanujan, Abel
4. **Rivalità:** Leibniz vs Newton, intuizionisti vs classici
5. **Applicazioni inaspettate:** Matematica pura che diventa pratica
6. **Connessioni moderne:** Come concetti antichi alimentano l'AI

### **Esempi di Buoni Aneddoti:**
- De Morgan che rifiutava lauree honoris causa
- Cantor e la resistenza all'infinito
- Gödel e la paranoia per il cibo
- Nash e la schizofrenia
- Eulero che continuava a fare matematica da cieco

---

## 🔗 **Connessioni da Evidenziare**

### **Per ogni nuovo file, chiedi:**
1. **Come si connette storicamente** ai file precedenti?
2. **Quali matematici appaiono in più file** (temi ricorrenti)?
3. **Come questo anticipa** sviluppi futuri?
4. **Connessioni moderne:** AI, fisica, informatica, crittografia?

### **Esempi di Connessioni:**
- **Gauss:** Appare in numeri complessi, statistica, geometria differenziale
- **Eulero:** Grafi, analisi complessa, teoria dei numeri
- **Von Neumann:** Teoria dei giochi, informatica, fisica quantistica

---

## 📚 **Linee Guida per Aree Specifiche**

### **Geometria:**
- Enfatizza visualizzazione e intuizione
- Connetti a fisica (relatività, meccanica quantistica)
- Storia delle geometrie alternative

### **Analisi:**
- Focus su rigorosità vs intuizione
- Crisi dei fondamenti del XIX secolo
- Connessioni a fisica matematica

### **Algebra:**
- Astrazione crescente nel tempo
- Da problemi concreti a strutture astratte
- Galois e la tragedia del genio

### **Probabilità/Statistica:**
- Dai giochi d'azzardo all'AI moderna
- Controversie filosofiche sull'incertezza
- Fisher vs Neyman vs Bayesiani

### **Informatica Teorica:**
- Turing e la computabilità
- Von Neumann e l'architettura dei computer
- Church e i fondamenti logici

---

## ⚠️ **Cosa NON Fare**

### **Evitare:**
- ❌ Riferimenti a "VS Code", "InfoView", "tattiche"
- ❌ Spiegazioni di come usare Lean
- ❌ Dimostrazioni complete (sempre `sorry`)
- ❌ Focus tecnico invece che concettuale
- ❌ Elenchi secchi senza narrativa

### **Non Dire:**
- "Usa la tattica `rw`"
- "In Lean, questo si scrive così"
- "Completa usando `simp`"
- "Controlla il goal con `#check`"

---

## 🚀 **Processo di Creazione**

### **1. Ricerca Storica (5 min):**
- Chi sono i 4-6 matematici chiave?
- Quali aneddoti interessanti esistono?
- Come si inserisce nella progressione storica?

### **2. Struttura Matematica (10 min):**
- Quali sono i 5-8 teoremi fondamentali?
- Come si collegano logicamente?
- Quali definizioni servono?

### **3. Scrittura (15 min):**
- Intro storica coinvolgente
- Sezioni per teoremi con aneddoti
- Controllo coerenza stilistica

### **4. Revisione (5 min):**
- Zero riferimenti a Lean?
- Storia e aneddoti presenti?
- Connessioni con altri file?
- Tutti teoremi `sorry`?

---

## 🎯 **Obiettivo Finale**

Ogni file deve far sentire l'utente come se stesse **esplorando una biblioteca di Alessandro**, dove ogni teorema è un tesoro nascosto con una storia affascinante da raccontare.

**Non tutorial su Lean, ma viaggio nella storia del pensiero umano!** 🌟