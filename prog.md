# Créneaux

1h30 lundi pm
1h15 mardi pm
1h15 jeudi pm

# Plan

Meta-questions à régler :
1. Ordre des deux parties ?
2. Formalisation minimale/clean des catégories dans setoid.

## Partie 1 : (co)Algèbres initiales et finales

Pitch : Quels sont les challenges pour avoir des types coinductifs qui soient vraiment des coalgèbres finales ?

### Catégorie dans Type

-> initiale ok direct : exemple sur list
-> finales problème égalité

### Catégorie dans Setoid

--> finales ok, on introduit la bisimulation : exemple sur colist
Question : un fichier category setoid minimalist peut-il être fait?

## Partie 2 : Ok, maintenant il faut travailler avec la bisimilarité

Pitch : Comment raisonner «efficacement» sur des relations coinductives via la tower induction

### Tower induction mix tableau/fichier

-> Voici une bibliothèque, voici l'interface

### On passe sur CCS et la librairie coinduction

-> On se restreint à la forte


# Abstract

Title: bisimulation and coinductive types.

The Rocq proof assistant provides inductive and coinductive datatypes. However, while the former yield initial algebras, it is not generally the case that the later yield final coalgebras: we need to consider them reason modulo bisimilarity.
During this course we will present tools that make it possible to work efficiently with bisimilarity (or any coinductive predicate), and show how to obtain final coalgebras from coinductive types.

Bring you computer: the course will be based on Rocq exercises.


# Difficultés

- besoin de setoid-cats avant-même d'atteindre les coinductifs, pour pouvoir faire sans axiome la catégorie des algèbres (ou coalgèbres): il faut oublier les preuves que les homomorphismes en sont.

- besoin de funext (+ propext) pour définir les foncteurs de base dans TYPES -> faire ETYPES ?

- si on garde le flow 
     1. cats-algèbres-coalgèbres
	 2. bisim pour coinductifs
	 3. companion/tower
	 4. bisim pour CCS
  -- alors il faut faire 2. à la mano -> en CoInductive, ou en imprédicatif (= union des bisimulations) ?
  -- on l'avait déjà remarqué je crois, mais on ne reboucle pas sur 1. avec 4. car le foncteur naturel pour CCS n'a pas de coalgèbre finale :-/
  
  
