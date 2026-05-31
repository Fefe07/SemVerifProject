# Rapport
<!-- Le format markdown est-il ok pour un rapport ? Ça serait peut être mieux d'en faire un joli pdf -->




## Tests 

Les jeux de tests suivants ont été ajoutés : 
- Congruence : teste le domaine de congruence
- interval_congruence : teste le produit réduit
- sign et sign_loop : teste le domaine signes
- polyhedral : teste le domaine des polyèdres
- terminate : teste la terminaison de l'iterateur


## Itérateur

Les foncteur `Make(Abs)` défini dans `iterator/iterator.ml` implémente un
itérateur simple de worklist, l'algorithme proposé dans le sujet.

Au début du module on introduit des fonctions d'affichage, permettant de
dérouler les étapes de l'itérateur lorsque le paramètre `verbose` est activé
(`-v` dans la ligne de commande, d'après `analyser/analyzer.ml`).

L'algorithme simple parcourt le graphe et associe des environnements abstraits
aux noeuds du graphe en fonction des instructions entrantes (disjonction faite
dans `apply_instr`). Deux points sont cependant à commenter :
- Lors des assertions, on utilise `Abs.guard` sur l'expression contraire
pour déterminer s'il est possible (selon l'abstraction) de contredire
l'expression booléenne.
- La terminaison doit être assurée en présence des boucles, on commence donc
l'analyse par rechercher les "widening points" par un parcours du graphe
`find_widening_points`, qui permet de distinguer s'il faut appliquer `Abs.widen`
avec l'abstraction définie précédemment dans l'itérateur, pour un certain noeud
donné.

Les appels de fonctions ne sont pas prises en comptes par l'itérateur.


## Domaines

### Dérivation des domaines non relationnels

Le foncteur `ValueDomainDerivation(Abs)(Vars)` issu de
`domains/valueDomainDerivation.ml` reçoit un module de valeurs abstraites non
relationnelles, et un environnement de variables, et construit le domaine
abstrait des fonctions associant une abstraction à chaque variable (ainsi que
l'élément `bottom`).
Les environnements sont des `Abs.t VarMap.t`, l'élément `bottom` est
l'environnement vide, et tout autre environnement est une fonction totale
des variables (tout variable a une valeur image) vers des valeurs non vides.
Les fonctions définies assurent cet invariant, et une exception `Bottom_exc`
permet de replier un environnement sur `bottom` si une variable est réduite à
`Abs.bottom`.

- Les opérations binaires d'environnements (`join`, `meet`, `widen`, `narrow`)
sont simplement des extensions point à point des opérations issues de `Abs`.
- `assign` utilise `evaluate_iexpr` qui appelle récursivement les opérateurs
de `Abs` pour évaluer une expression.
- `guard` est le plus complexe à implémenter. `bwd_evaluate_iexpr` est
l'équivalent de `evaluate_iexpr`, mais en appelant les `bwd_<op>`. `guard_arg`
propage un argument `bool`, représentant la résolution des opérateurs de
négation, en utilisant les lois De Morgan.

### Signes simples

Le foncteur `Make(Vars)` issu de `domains/signDomain.ml` utilise la dérivation
précédente et implémente le domaine
des signes simples (inégalités larges par rapport à 0) à partir de la
`VALUE_DOMAIN` `SignValueDomain`.
C'est un cas de domaine abstrait fini avec 5 éléments : bottom, zéro, négatif,
positif, top. La majorité des opérations sont alors des distinctins de cas
simples sur les arguments.
Puisque le domaine est fini, `widen` et `narrow` se réduisent simplement
à `join` et `meet` puisqu'il n'y a pas d'enjeu de terminaison.

Ce domaine est correct, mais a peu d'expressivité et n'est donc pas complet.
C'est pour cette raison qu'on lui fournit des ensembles de tests séparés.

### Intervalles

Le foncteur `Make(Vars)` issu de `domains/intervalDomain.ml`
dérive la `VALUE_DOMAIN` de `IntervalValueDomain`.

Nous avons adapté les résultats du TP 3 pour convenir à l'interface de
`VALUE_DOMAIN`; ceci consistait à ajouter l'opération `widen`, et à assembler
les opérateurs `bas_<comp>` dans un `compare` plus général.

Ce domaine es correct, et possède les manques d'expressivités décrits en cours.



### Produit réduit  
Pour implémenter le produit réduit entre le domaine des intervalles et celui des congruences, nous avons utilisé la réduction suivante : 

TODO : Insérer réduction (formule LaTeX ou image)

qui est la réduction exacte, et est calculable efficacement.

Nous avons essayé de créer un foncteur qui prend en entrée deux modules A,B de type VALUE_DOMAIN et une fonction de réduction red : (A.t * B.t) -> (A.t * B.t), et qui renvoie le VALUE_DOMAIN du produit réduit. Malheureusement, cette implémentation est refusée car les modules A,B sont passés en tant que VALUE_DOMAIN, et sont donc scellés : le compilateur refuse de les laisser déballer par la fonction red...  
Nous avons donc du faire une implémentation spécifique (c'est à dire copier les définitions de A, B et red au début du code du foncteur)


### Polèdres (APRON)

Le foncteur `Make(Vars)` issu de `domains/polyhedralDomain.ml` construit un
`DOMAIN` en utilisant la librairie APRON, plus spécifiquement son module
`apron.polkaMPQ.

L'initialisation et la transformations du domaine est facilitée par l'invariance
de l'environnement `env`, puisque toutes les variables sont supposées globales
et valide à tout instant. Cependant, puisque `ControlFlowGraph` se réfère à ses
variables par identifiant et non par nom contrairement à APRON, on décide
d'ajouter cet identifiant au nom des `Apron.Var.t` pour éviter toute collision.

C'est le rôle de `translate_var`, qui rejoint un ensemble de fonctions de
traduction entre éléments (variables, constantes entières ou aléatoires,
opérateurs, expressions, comparaisons, contraintes) de `ControlFlowGraph` et
les éléments correspondant d'APRON.

Une fois cette traduction effectuée, la plupart des opérateurs abstraits se
réduisent à des appels d'APRON.
La complexité vient de l'implémentation de `guard` qui n'est pas proposée
telle qu'elle dans la librairie. Comme pour la dérivation des `VALUE_DOMAIN`,
on utilise une fonction récursive `guard_ard` propageant les négations.
Les contraintes doivent être adaptées pour convenir à la forme `<expr> >= 0`
ou `<expr> = 0` de `Polka.loose Polka.t`, ce qui consiste à reformuler les
expressions, ajouter des constantes 1 pour les inégalités strictes, et faire une
disjonction pour `!=`, qui est ensuite rassemblée par `join`.

Nous n'avons pas rencontré de problèmes de correction sur ce domaine, cependant
la division semble manquer de précision, ce qui est mis en valeur par
quelques tests de `example/polyhedral/` : la division par zéro (ou la possible
division par zéro) lève toute contrainte sur le résultat de la division
(lors d'un assign de la forme `x = y/0` par exemple), et certaines divisions
renvoient un résultat plus large que prévu (par exemple si `x = 42/2`, les
contraintes résultante affirment `x <= 21` et `x >= 20`).

Nous n'avons pas eu le temps d'adresser ce problème, estimant que cette partie
visait surtout investir la librairie APRON dans le projet.


