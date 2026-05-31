# Rapport
<!-- Le format markdown est-il ok pour un rapport ? Ça serait peut être mieux d'en faire un joli pdf -->




## Tests 

Les jeux de tests suivants ont été ajoutés : 
- Congruence : teste le domaine de congruence
- interval_congruence : teste le produit réduit



## Domaines

### Produit réduit  
Pour implémenter le produit réduit entre le domaine des intervalles et celui des congruences, nous avons utilisé la réduction suivante : 

TODO : Insérer réduction (formule LaTeX ou image)

qui est la réduction exacte, et est calculable efficacement.

Nous avons essayé de créer un foncteur qui prend en entrée deux modules A,B de type VALUE_DOMAIN et une fonction de réduction red : (A.t * B.t) -> (A.t * B.t), et qui renvoie le VALUE_DOMAIN du produit réduit. Malheureusement, cette implémentation est refusée car les modules A,B sont passés en tant que VALUE_DOMAIN, et sont donc scellés : le compilateur refuse de les laisser déballer par la fonction red...  
Nous avons donc du faire une implémentation spécifique (c'est à dire copier les définitions de A, B et red au début du code du foncteur)
